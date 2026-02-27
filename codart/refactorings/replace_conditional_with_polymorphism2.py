import os
import re
import sys
from codart.gen.JavaParserLabeled import JavaParserLabeled
from codart.gen.JavaLexer import JavaLexer
from antlr4 import *
from antlr4.TokenStreamRewriter import TokenStreamRewriter
from codart.gen.JavaParserLabeledListener import JavaParserLabeledListener

os.add_dll_directory("C:\\Program Files\\SciTools\\bin\\pc-win64\\")
sys.path.append("C:\\Program Files\\SciTools\\bin\\pc-win64\\python")
import understand


GLOBAL_INJECTIONS = {
    "abstract": {},  # baseType -> abstractMethodText
    "concrete": {},  # classType -> [methodText, ...]
}


def analyze_project_with_understand(udb_path, target_method):
    db = understand.open(udb_path)

    owners = set()
    fields_map = {}   # owner_class -> set of fields
    getters_map = {}  # owner_class -> {getter_name: field_name}

    for m in db.ents("Method"):
        if m.name() != target_method:
            continue

        # Get defining class
        parent_class = None
        for ref in m.refs("Definein"):
            if ref.ent().kindname().endswith("Class"):
                parent_class = ref.ent()
                break
        if not parent_class:
            parent_class = m.parent()
        if not parent_class:
            continue

        owner_class = parent_class.name()
        owners.add(owner_class)

        # Get fields of the owner class
        if owner_class not in fields_map:
            fields_map[owner_class] = {
                f.name(): f.type()
                for f in parent_class.ents("Define", "Java Variable")
            }

        # Get getters mapping
        if owner_class not in getters_map:
            getters = {}
            for method in parent_class.ents("Define", "Java Method"):
                if not (method.name().startswith("get") or method.name().startswith("is")):
                    continue
                # Try to find which field it returns
                for ref in method.refs("Return", "Java Variable"):
                    ret_ent = ref.ent()
                    if ret_ent and ret_ent.name() in fields_map[owner_class]:
                        getters[method.name()] = ret_ent.name()
            getters_map[owner_class] = getters
            print(getters_map)

    return list(owners), fields_map, getters_map


class ClassCollector(JavaParserLabeledListener):
    def __init__(self, class_ctx):
        self.class_ctx = class_ctx

    def enterClassDeclaration(self, ctx):
        name = ctx.IDENTIFIER().getText()
        self.class_ctx[name] = ctx


class ReplaceConditionalWithPolymorphismRTTIListener(JavaParserLabeledListener):
    """
    Generic Replace Conditional with Polymorphism (RTTI).
    Works for any Java input satisfying preconditions.
    """

    def __init__(self, tokens: CommonTokenStream, target_method: str, global_class_ctx, method_owners, fields_map, getters_map):
        self.tokens = tokens
        self.rewriter = TokenStreamRewriter(tokens)
        self.target_method = target_method

        self.current_class = None
        self.in_target_method = False

        self.param_name = None
        self.param_type = None

        self.if_ctx = None
        self.current_subtype = None

        self.cases = []      # [{type, body}]
        self.default_body = None

        self.class_ctx = global_class_ctx
        self.method_owners = set(method_owners)
        self.class_fields = set()
        self.getters = {}  # method_name -> field_name
        self.fields_map = fields_map  # owner_class -> {field: type}
        self.getters_map = getters_map  # owner_class -> {getter_name: field_name}

        self.capture_body_for = None  # class name for current if/else-if
        self.pending_cases = []  # [{type, body}]
        self.is_else_block = False

    def enterClassDeclaration(self, ctx):
        name = ctx.IDENTIFIER().getText()
        self.current_class = name
        self.class_ctx[name] = ctx

    def enterMethodDeclaration(self, ctx):

        if ctx.IDENTIFIER().getText() != self.target_method:
            return

        self.in_target_method = True

        params = ctx.formalParameters().formalParameterList()
        if not params or len(params.formalParameter()) != 1:
            self.in_target_method = False
            return

        p = params.formalParameter()[0]
        self.param_name = p.variableDeclaratorId().getText()
        self.param_type = p.typeType().getText()

    def exitMethodDeclaration(self, ctx):
        if not self.in_target_method:
            return
        self._inject_abstract_method(ctx)
        self._inject_concrete_methods(ctx)
        self._replace_if_with_dispatch()
        self._reset()

    # RTTI detection
    def enterStatement2(self, ctx):
        if not self.in_target_method or not ctx.parExpression():
            return

        expr = ctx.parExpression().expression()
        if not expr.INSTANCEOF():
            return

        lhs = expr.expression().getText()
        if lhs != self.param_name:
            return

        self.capture_body_for = expr.typeType().getText().split(".")[-1]
        self.if_ctx = ctx.parentCtx

    # Capture bodies
    def enterStatement0(self, ctx: JavaParserLabeled.StatementContext):
        if not self.if_ctx:
            return

        start = ctx.start.tokenIndex
        stop = ctx.stop.tokenIndex

        body_text = self.rewriter.getText("", start, stop).strip()

        # Remove surrounding braces
        if body_text.startswith("{") and body_text.endswith("}"):
            body_text = body_text[1:-1].strip()

        # Decide target class
        if self.capture_body_for:
            class_label = self.capture_body_for
            self.capture_body_for = None
        else:
            # ELSE branch → base type
            # ELSE branch → infer from cast
            inferred = self._extract_cast_type(body_text)
            if not inferred:
                print("ELSE branch without cast — skipping")
                return

            class_label = inferred
            self.is_else_block = True

        body_text = self._transform_body(body_text)

        self.pending_cases.append({
            "type": class_label,
            "body": body_text
        })

        print(f"Captured body for {class_label}:\n{body_text}\n")

    # Refactoring
    def _transform_body(self, body):
        # Take first owner from the set (or list)
        owner_class = next(iter(self.method_owners))  # e.g., "InstructionFactory"
        param_name = owner_class[0].lower() + owner_class[1:]  # camelCase

        # Replace field access with getter call
        if owner_class in self.getters_map:
            for getter, field in self.getters_map[owner_class].items():
                # Replace all occurrences of the field in the body
                body = re.sub(rf"\b{field}\b", f"{param_name}.{getter}()", body)

        # Replace RTTI parameter name with "this"
            # Step 1: Replace any cast around the RTTI parameter with "( this )"
        if self.param_name:
            # Matches: (Type) param_name, possibly with spaces
            body = re.sub(
                rf"\(\s*[\w<>]+\s*\)\s*{self.param_name}\b",
                "(this)",
                body
            )
        return body

    def _inject_abstract_method(self, method_ctx):
        base = self.class_ctx.get(self.param_type)
        if not base:
            return

        ret_type = method_ctx.typeTypeOrVoid().getText()

        abstract_method = (
            f"\n\tpublic abstract {ret_type} "
            f"{self.target_method}("
            f"{self._caller_signature(method_ctx)});\n"
        )
        base = self.param_type
        GLOBAL_INJECTIONS["abstract"][base] = abstract_method

        print(f"Registered abstract method for {base}")

    def _inject_concrete_methods(self, method_ctx):
        ret_type = method_ctx.typeTypeOrVoid().getText()

        for case in self.pending_cases:
            ctx = self.class_ctx.get(case["type"])
            if not ctx:
                continue

            method = (
                "\n\t@Override\n"
                f"\tpublic {ret_type} {self._method_signature()} {{\n"
                f"{case['body']}\n\t}}\n"
            )
            print(f"Injecting concrete method into {case['type']}")

            cls = case["type"]
            GLOBAL_INJECTIONS.setdefault("concrete", {}).setdefault(cls, []).append(method)

            print(f"Registered concrete method for {cls}")

    def _replace_if_with_dispatch(self):
        if not self.if_ctx:
            return

        call = f"{self.param_name}.{self.target_method}({self._caller_args()})"
        replacement = f"return {call};" if self._returns() else f"{call};"

        self.rewriter.replaceRange(
            self.if_ctx.start.tokenIndex,
            self.if_ctx.stop.tokenIndex,
            replacement
        )

    def _get_text(self, ctx):
        return self.rewriter.getText(
            "",
            ctx.start.tokenIndex,
            ctx.stop.tokenIndex
        )

    def _method_signature(self):
        return f"{self.target_method}({self._caller_signature(None)})"

    def _caller_signature(self, ctx):
        # Take first owner from the set (or list)
        owner_class = next(iter(self.method_owners))  # e.g., "InstructionFactory"

        # Generate parameter name in camelCase: instructionFactory
        param_name = owner_class[0].lower() + owner_class[1:]

        return f"{owner_class} {param_name}"

    def _caller_args(self):
        return "this"

    def _returns(self):
        return True

    def _reset(self):
        self.in_target_method = False
        self.if_ctx = None
        self.cases.clear()
        self.default_body = None

    def _extract_cast_type(self, body_text):
        """
        Extracts cast type from expressions like:
        (ObjectType) t
        (pkg.ObjectType) t
        """
        m = re.search(r"\(\s*([\w\.<>]+)\s*\)\s*" + re.escape(self.param_name), body_text)
        if m:
            return m.group(1).split(".")[-1]
        return None


def find_java_files(root_dir):
    java_files = []
    for root, _, files in os.walk(root_dir):
        for f in files:
            if f.endswith(".java"):
                java_files.append(os.path.join(root, f))
    return java_files


def apply_global_injections(project_root):
    for f in find_java_files(project_root):
        tokens, tree = parse_file(f)

        class_ctx = {}
        collector = ClassCollector(class_ctx)
        ParseTreeWalker().walk(collector, tree)

        rewriter = TokenStreamRewriter(tokens)

        for cls, ctx in class_ctx.items():

            # abstract methods
            if cls in GLOBAL_INJECTIONS["abstract"]:
                rewriter.insertBefore(
                    rewriter.DEFAULT_PROGRAM_NAME,
                    ctx.classBody().stop.tokenIndex,
                    GLOBAL_INJECTIONS["abstract"][cls]
                )
                print(f"Injected abstract method into {cls}")

            # concrete methods
            for m in GLOBAL_INJECTIONS["concrete"].get(cls, []):
                rewriter.insertBefore(
                    rewriter.DEFAULT_PROGRAM_NAME,
                    ctx.classBody().stop.tokenIndex,
                    m
                )
                print(f"Injected concrete method into {cls}")

        new_code = rewriter.getDefaultText()
        open(f, "w", encoding="utf-8").write(new_code)


def parse_file(java_path):
    with open(java_path, "r", encoding="utf-8") as f:
        code = f.read()

    lexer = JavaLexer(InputStream(code))
    tokens = CommonTokenStream(lexer)
    parser = JavaParserLabeled(tokens)
    tree = parser.compilationUnit()

    return tokens, tree


def refactor_project(project_root, output_root, udb_path, target_method):

    # semantic analysis
    owners, fields_map, getters_map = analyze_project_with_understand(udb_path, target_method)

    # collect classes
    class_ctx = {}
    for f in find_java_files(project_root):
        _, tree = parse_file(f)
        collector = ClassCollector(class_ctx)
        ParseTreeWalker().walk(collector, tree)
        class_ctx.update(collector.class_ctx)

    # rewrite
    for f in find_java_files(project_root):
        tokens, tree = parse_file(f)

        listener = ReplaceConditionalWithPolymorphismRTTIListener(
            tokens,
            target_method,
            class_ctx,
            owners,
            fields_map,
            getters_map
        )

        ParseTreeWalker().walk(listener, tree)
        # write replaced if-dispatch only
        out = os.path.join(output_root, os.path.relpath(f, project_root))
        os.makedirs(os.path.dirname(out), exist_ok=True)
        open(out, "w", encoding="utf-8").write(
            listener.rewriter.getDefaultText()
        )

        # inject everything
    apply_global_injections(output_root)


if __name__ == "__main__":
    refactor_project(
        project_root="C:/Users/98910/Desktop/type_checking_examples_before_refactor/rtti",
        output_root="C:/Users/98910/Desktop/type_checking_examples_before_refactor/rtti",
        udb_path="C:/Users/98910/Desktop/type_checking_examples_before_refactor/rtti/rtti.udb",
        target_method="createCheckCast"
    )

    print("RTTI refactoring complete.")
