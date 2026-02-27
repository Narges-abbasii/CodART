import os
import re
from antlr4 import *
from codart.gen.JavaParserLabeled import JavaParserLabeled
from codart.gen.JavaLexer import JavaLexer
from codart.gen.JavaParserLabeledListener import JavaParserLabeledListener
from collections import defaultdict
from dataclasses import dataclass


@dataclass(frozen=True)
class TypeCheckingSmell:
    package: str
    class_name: str
    method: str
    line: int
    kind: str
    condition: str | None = None


class SymbolTableListener(JavaParserLabeledListener):
    def __init__(self):
        self.class_modifiers = []
        self.abstract_classes = set()
        self.subclasses = {}  # {superclass: [subclasses]}
        self.current_class = None
        self.static_constants = {}  # {class: [static constant names]}
        self.abstract_methods = []  # {class: [abstract method names]}
        self.current_is_abstract = False

    def enterClassOrInterfaceModifier(self, ctx: JavaParserLabeled.ClassOrInterfaceModifierContext):
        self.class_modifiers = ctx.getText()

    def enterClassDeclaration(self, ctx: JavaParserLabeled.ClassDeclarationContext):
        class_name = ctx.IDENTIFIER().getText()
        # Track superclass relationships
        if ctx.IMPLEMENTS():
            superclass = ctx.typeList().getText()
            self.abstract_classes.add(superclass)
            self.subclasses.setdefault(superclass, []).append(class_name)
        if ctx.EXTENDS():
            superclass = ctx.typeType().getText()
            self.abstract_classes.add(superclass)
            self.subclasses.setdefault(superclass, []).append(class_name)

    def enterFieldDeclaration(self, ctx: JavaParserLabeled.FieldDeclarationContext):
        # modifiers = [m.getText() for m in ctx.parentCtx.modifier()]
        # if "static" in modifiers and "final" in modifiers:
        #     if self.current_class:
        #         var_name = ctx.variableDeclarators().variableDeclarator(0).variableDeclaratorId().getText()
        #         self.static_constants[self.current_class].append(var_name)
        parent = ctx.parentCtx
        grandparent = parent.parentCtx

        modifiers = []
        if hasattr(grandparent, "modifier"):  # classBodyDeclaration likely
            modifiers = [m.getText() for m in grandparent.modifier()]
        elif hasattr(parent, "modifier"):
            modifiers = [m.getText() for m in parent.modifier()]

        field_name = ctx.variableDeclarators().variableDeclarator(0).variableDeclaratorId().IDENTIFIER().getText()

    def enterMethodDeclaration(self, ctx: JavaParserLabeled.MethodDeclarationContext):
        method_name = ctx.IDENTIFIER().getText()
        method_body = ctx.methodBody()
        # Check if method has Nobody (i.e., abstract methods)
        if method_body is None or method_body.getText() == ";":
            self.abstract_methods.append(method_name)

        if self.current_is_abstract:
            modifiers = [m.getText() for m in ctx.parentCtx.modifier()]
            if "abstract" in modifiers:
                method_name = ctx.IDENTIFIER().getText()
                self.abstract_methods[self.current_class].append(method_name)


class MissingHierarchyListener(JavaParserLabeledListener):
    def __init__(self, abstract_classes, subclasses, abstract_methods):
        self.enter_class = False
        self.class_fields = set()
        self.static_fields = []
        self.abstract_classes = abstract_classes
        self.parameters = []
        self.enter_method = False
        self.method_identifier = ""
        self.class_identifier = []
        self.package_identifier = ""
        self.abstract_method = []
        self.current_abstract = None
        self.getters = {}  # key = methodName, value = fieldName
        self.enum_constants = []
        self.fields = []
        self.literals = []
        self.if_else = False
        self.else_count = 0
        self.if_conditions = []
        self.visited_methods = set()
        self.operators = ["==", "!=", "<=", ">=", "instanceof"]
        self.switch = False
        self.switch_condition = []
        self.switch_label = []
        self.subclasses = subclasses
        self.abstract_methods = abstract_methods
        self.detected_smells = []
        self.rtti_smells = []
        self.abstract_getters = defaultdict(list)
        self.abstract_var_to_type = {}
        self.method_called = []
        self.type_checking_smells: set[TypeCheckingSmell] = set()
        self._if_block_start_line = None

    def enterCompilationUnit(self, ctx: JavaParserLabeled.CompilationUnitContext):
        if ctx.packageDeclaration():
            self.package_identifier = ctx.packageDeclaration().getText().replace(";", "").strip()

    def enterClassDeclaration(self, ctx: JavaParserLabeled.ClassDeclarationContext):
        self.enter_class = True
        class_name = ctx.IDENTIFIER().getText()
        self.class_identifier.append(class_name)

    def enterFieldDeclaration(self, ctx: JavaParserLabeled.FieldDeclarationContext):
        for declarator in ctx.variableDeclarators().variableDeclarator():
            field_name = declarator.variableDeclaratorId().getText()
            self.class_fields.add(field_name)
            self.fields.append(field_name)

        parent = ctx.parentCtx  # should be memberDeclaration
        grandparent = parent.parentCtx if parent else None
        if grandparent and hasattr(grandparent, 'modifier'):
            modifiers = grandparent.modifier()
            is_static = any(m.getText() == 'static' for m in modifiers)
            if is_static:
                var_type = ctx.typeType().getText()
                var_names = [v.variableDeclaratorId().getText() for v in ctx.variableDeclarators().variableDeclarator()]
                for name in var_names:
                    self.static_fields.append((var_type, name))
                    self.literals.append(name)

    def enterMethodDeclaration(self, ctx: JavaParserLabeled.MethodDeclarationContext):
        self.enter_method = True
        parameters = []

        formal_params_ctx = ctx.formalParameters()
        if formal_params_ctx:
            param_list_ctx = formal_params_ctx.formalParameterList()
            if param_list_ctx:
                # Process normal parameters (if any)
                if hasattr(param_list_ctx, "formalParameter"):
                    for param in param_list_ctx.formalParameter():
                        if param.typeType():
                            param_type = param.typeType().getText()
                        else:
                            param_type = "Unknown"

                        param_name = param.variableDeclaratorId().getText()
                        # Only track parameters that match abstract classes
                        for superClass in self.abstract_classes:
                            if superClass == param_type:
                                parameters.append((param_type, param_name))
                                self.parameters.append(param_name)

                # Process last parameter if it exists (for varargs)
                if hasattr(param_list_ctx, "lastFormalParameter") and param_list_ctx.lastFormalParameter():
                    param = param_list_ctx.lastFormalParameter()
                    if param.typeType():
                        param_type = param.typeType().getText()
                    else:
                        param_type = "Unknown"

                    param_name = param.variableDeclaratorId().getText()
                    for superClass in self.abstract_classes:
                        if superClass == param_type:
                            parameters.append((param_type, param_name))
                            self.parameters.append(param_name)

        self.method_identifier = ctx.IDENTIFIER().getText()
        parameters = ctx.formalParameters().getText()
        return_type = ctx.typeTypeOrVoid().getText()
        self.abstract_method = ctx.IDENTIFIER().getText()
        method_body = ctx.methodBody()
        # Check if method has Nobody (i.e., abstract methods)
        if method_body is None or method_body.getText() == ";":
            if self.current_abstract:
                self.abstract_getters[self.current_abstract].append(self.abstract_method)

        if parameters != "()" or return_type == "void":
            return
        if self.method_identifier.startswith("get") or self.method_identifier.startswith("is"):
            method_body = ctx.methodBody().getText()
            for field in self.class_fields:
                if f"return{field}" in method_body or f"return this.{field}" in method_body:
                    self.getters[self.method_identifier] = field

    def enterEnumDeclaration(self, ctx: JavaParserLabeled.EnumDeclarationContext):
        if ctx.enumConstants():
            for enum_constant in ctx.enumConstants().enumConstant():
                name = enum_constant.IDENTIFIER().getText()
                self.enum_constants.append(name)

    def enterEnhancedForControl(self, ctx: JavaParserLabeled.EnhancedForControlContext):
        var_type = ctx.typeType().getText()
        for superClass in self.abstract_classes:
            if superClass == var_type:
                # Extract parameter name
                var_name = ctx.variableDeclaratorId().getText()
                self.parameters.append(var_name)

    def enterMethodCall0(self, ctx: JavaParserLabeled.MethodCall0Context):
        called_method = ctx.getText()
        if called_method in self.abstract_method:
            print("abstract method:", called_method)

    def enterFormalParameter(self, ctx: JavaParserLabeled.FormalParameterContext):
        parameter = ctx.variableDeclaratorId().getText()
        self.fields.append(parameter)

    # def enterVariableDeclarator(self, ctx: JavaParserLabeled.VariableDeclaratorContext):
    #     variable = ctx.variableDeclaratorId().getText()
    #     if ctx.variableInitializer():
    #         # self.literals.append(variable)
    #         self.fields.append(variable)
    #     else:
    #         self.fields.append(variable)

    def enterLocalVariableDeclaration(self, ctx: JavaParserLabeled.LocalVariableDeclarationContext):
        for dec in ctx.variableDeclarators().variableDeclarator():
            var_name = dec.variableDeclaratorId().getText()
            initializer = dec.variableInitializer()
            if initializer is None:
                continue
            init_text = initializer.getText()
            root = init_text.split(".")[0]
            if not ctx.typeType().primitiveType():
                self.fields.append(var_name)
            elif root not in self.class_fields:
                continue
            elif "Dialog" in init_text:
                continue
            self.fields.append(var_name)

    # def enterPrimary3(self, ctx: JavaParserLabeled.Primary3Context):
    #     exp = ctx.getText()
    #     if exp not in ("0", "0L", "0.0", "false", "null", "", "this"):  # skip trivial numeric constants
    #         self.literals.append(exp)

    def exitExpression1(self, ctx: JavaParserLabeled.Expression1Context):
        text = ctx.getText()
        if "." in text and text[0].isupper():  # crude but effective enum check
            self.literals.append(text)

    def debug_tree(self, ctx, level=0):
        print("  " * level, type(ctx), "->", ctx.getText())
        for i in range(ctx.getChildCount()):
            self.debug_tree(ctx.getChild(i), level + 1)

    def extract_conditions(self, expr_ctx):
        conditions = []
        # Unwrap single-child wrappers
        if expr_ctx.getChildCount() == 1:
            return self.extract_conditions(expr_ctx.getChild(0))

        # Unwrap parentheses inside Primary
        if "Primary" in type(expr_ctx).__name__:
            for i in range(expr_ctx.getChildCount()):
                child = expr_ctx.getChild(i)
                if child.getText() not in ["(", ")"]:
                    return self.extract_conditions(child)

        # Split on logical operators
        for i in range(expr_ctx.getChildCount()):
            child = expr_ctx.getChild(i)
            if child.getText() in ["&&", "||"]:
                left = expr_ctx.getChild(i - 1)
                right = expr_ctx.getChild(i + 1)

                conditions.extend(self.extract_conditions(left))
                conditions.extend(self.extract_conditions(right))
                return conditions

        # Atomic condition
        conditions.append(expr_ctx.getText())
        return conditions

    def enterStatement2(self, ctx: JavaParserLabeled.Statement2Context):
        self.if_else = True
        if ctx.ELSE():
            self.else_count += 1
        # Store the first line of the if-else block
        # if not hasattr(self, "_if_block_start_line") or self._if_block_start_line is None:
        #     self._if_block_start_line = ctx.start.line

        # condition = ctx.parExpression().expression().getText()
        # if condition not in self.if_conditions:
        #     self.if_conditions.append(condition)
        expr_ctx = ctx.parExpression().expression()
        atomic_conditions = self.extract_conditions(expr_ctx)

        for cond in atomic_conditions:
            if cond not in self.if_conditions:
                self.if_conditions.append(cond)

    def exitStatement2(self, ctx: JavaParserLabeled.Statement2Context):
        """
        Record only one smell per if-else block, using the line of the first 'if'.
        """
        if self.if_else and self.else_count > 0:
            has_type_check = False
            has_rtti = False
            for cond in self.if_conditions:
                # print("condition", cond)
                # Skip pure boolean checks like if(result.isSuccess())
                if self.is_simple_boolean_check(cond):
                    continue

                # if any(op in cond for op in self.operators):
                if re.fullmatch(r'\s*\w+\s*(==|!=|<=|>=|<|>)\s*\w+\s*', cond):

                    lhs, rhs = self.split_condition(cond)
                    lhs = lhs.split('.')[0]
                # direct field/literal or getter
                    for field in self.fields:
                        for literal in self.literals:
                            match_direct = (field in lhs and rhs == literal) or (rhs == field and lhs == literal)
                            match_getter = (self.is_getter_invocation(lhs, self.getters) and rhs == literal) or \
                                           (self.is_getter_invocation(rhs, self.getters) and lhs == literal)
                            if match_direct or match_getter:
                                has_type_check = True
                                break

                    if has_type_check:
                        self._if_block_start_line = ctx.start.line
                        break
                if has_type_check:
                    break
                # Pattern2: (Shape instanceof Circle)
                if "instanceof" in cond:
                    lhs, rhs = self.split_instanceof(cond)
                    if self.check_type_check(lhs, rhs, ctx.start.line):
                        has_rtti = True
                    break
                # Pattern3: getClass() == Subclass.class
                if re.search(r"\.getClass\(\)\s*==\s*\w+\.class", cond):
                    lhs, rhs = self.split_getclass_equality(cond)
                    if self.check_type_check(lhs, rhs, ctx.start.line):
                        has_rtti = True
                    break
                # Pattern4: getClass().equals(SubClass.class)
                if re.search(r"\.getClass\(\)\.equals\(\s*\w+\.class\s*\)", cond):
                    lhs, rhs = self.split_getclass_equals(cond)
                    if self.check_type_check(lhs, rhs, ctx.start.line):
                        has_rtti = True
                    break

                # Pattern 5: var.getType() == CONSTANT
                if re.search(r"(\w+)\.(\w+)\(\)\s*==\s*(\w+(\.\w+)?)", cond):
                    lhs, rhs = self.split_condition(cond)
                    if self.check_encoded_type(lhs, rhs, ctx.start.line):
                        has_rtti = True
                    break

            if has_type_check:
                self.record_smell(
                    ctx,
                    kind="IF_ELSE_TYPE_CHECK",
                    condition=" | ".join(self.if_conditions),
                    line=self._if_block_start_line  # use first if line
                )
            if has_rtti:
                self.record_smell(
                    ctx,
                    kind="RTTI",
                    condition=" | ".join(self.if_conditions),
                    line=self._if_block_start_line  # use first if line
                )

        # Reset temporary state
        self.if_else = False
        self.else_count = 0
        self.if_conditions.clear()
        self._if_block_start_line = None

    def enterStatement8(self, ctx: JavaParserLabeled.Statement8Context):
        self.switch = True
        statement = ctx.SWITCH()
        if statement:
            condition = ctx.parExpression().expression().getText()
            if '.' in condition:
                condition = condition.split('.')[-1]
            self.switch_condition.append(condition)

    def enterSwitchLabel(self, ctx: JavaParserLabeled.SwitchLabelContext):
        label = ctx.getText()
        self.switch_label.append(label)

    def exitStatement8(self, ctx: JavaParserLabeled.Statement8Context):
        for field in self.fields:
            for literal in self.literals:
                if field in self.switch_condition and f"case{literal}:" in self.switch_label:
                    self.switch = False
                    print("Found Switch statement involving type field!", self.method_identifier)
                    if field in self.switch_condition and f"case{literal}:" in self.switch_label:
                        self.record_smell(
                            ctx,
                            kind="SWITCH_TYPE_CHECK",
                            condition=" ".join(self.switch_condition)
                        )

                    return self.method_identifier
                for getter in self.getters:
                    if f"{getter}()" in self.switch_condition and f"case{literal}:" in self.switch_label:
                        self.switch = False
                        print("Found Switch statement involving getter!", self.method_identifier)
                        if f"{getter}()" in self.switch_condition and f"case{literal}:" in self.switch_label:
                            self.record_smell(
                                ctx,
                                kind="SWITCH_GETTER_TYPE_CHECK",
                                condition=" ".join(self.switch_condition)
                            )
                        return self.package_identifier, self.class_identifier, self.method_identifier

    def exitMethodDeclaration(self, ctx: JavaParserLabeled.MethodDeclarationContext):
        self.enter_method = False

    def exitClassDeclaration(self, ctx: JavaParserLabeled.ClassDeclarationContext):
        self.class_identifier.pop()
        self.enter_class = False
        # self.fields.clear()
        self.getters.clear()
        self.literals.clear()

    def split_condition(self, condition: str):
        """
        Split the condition into left-hand side (lhs) and right-hand side (rhs).
        """
        for op in ["==", "!=", "<=", ">="]:
            if op in condition:
                return condition.split(op)
        return "", ""

    def is_getter_invocation(self, expr: str, known_getters: dict) -> bool:
        """
        Check if the expression looks like a getter invocation.
        Accepts forms like: phone.getType(), this.getType(), getType()
        """
        for getter in known_getters.keys():
            if expr.endswith(f".{getter}()") or expr == f"{getter}()":
                return True
        return False

    def split_instanceof(self, condition):
        parts = condition.replace("(", "").replace(")", "").split("instanceof")
        lhs = parts[0].strip()
        rhs = parts[1].strip()
        return lhs, rhs

    def split_getclass_equality(self, condition):
        # Example: (s.getClass() == Circle.class)
        m = re.search(r"(\w+)\.getClass\(\)\s*==\s*(\w+)\.class", condition)
        if m:
            lhs = m.group(1)
            rhs = m.group(2)
            return lhs, rhs
        return None, None

    def split_getclass_equals(self, condition):
        # Example: s.getClass().equals(Circle.class)
        m = re.search(r"(\w+)\.getClass\(\)\.equals\(\s*(\w+)\.class\s*\)", condition)
        if m:
            lhs = m.group(1)
            rhs = m.group(2)
            return lhs, rhs
        return None, None

    def check_type_check(self, lhs, rhs, line) -> bool:
        for superClass in self.abstract_classes:
            subclasses = self.subclasses.get(superClass, [])
            if rhs in subclasses and lhs in self.parameters:
                self.detected_smells.append({
                    "line": line,
                    "super": superClass,
                    "sub": rhs,
                    "variable": lhs
                })
                return True  # smell detected
        return False

    def check_encoded_type(self, lhs, rhs, line) -> bool:
        if "." in lhs and "(" in lhs and lhs.endswith(")"):
            lhs_f = lhs.split(".")[0]  # 'type'
            lhs_l = lhs.split(".")[1].split("(")[0]  # 'getType'
            for superClass in self.abstract_classes:
                if lhs_f in self.parameters and lhs_l in self.abstract_methods:
                    self.detected_smells.append({
                        "line": line,
                        "super": superClass,
                        "sub": rhs,
                        "variable": lhs
                    })
                    return True
        return False

    def record_smell(self, ctx, kind: str, condition: str | None = None, line: int | None = None):
        current_class = self.class_identifier[-1] if self.class_identifier else None
        self.type_checking_smells.add(
            TypeCheckingSmell(
                package=self.package_identifier,
                class_name=current_class,
                method=self.method_identifier,
                line=line if line is not None else ctx.start.line,  # use provided line if given
                kind=kind,
                condition=condition
            )
        )

    def is_simple_boolean_check(self, cond: str) -> bool:
        """
        Returns True if condition is a simple boolean check like:
        - result.isSuccess()
        - isValid()
        - flag
        - !result.isSuccess()
        """

        cond = cond.strip()

        # remove surrounding parentheses
        if cond.startswith("(") and cond.endswith(")"):
            cond = cond[1:-1].strip()

        # remove leading negation
        cond = cond.lstrip("!").strip()

        # Case 1: simple variable (flag)
        if re.fullmatch(r"\w+", cond):
            return True

        # Case 2: simple method call without comparison (obj.isSuccess())
        if re.fullmatch(r"\w+\.\w+\(\)", cond):
            return True

        # Case 3: direct method call (isValid())
        if re.fullmatch(r"\w+\(\)", cond):
            return True

        return False


def get_all_java_files(directory):
    java_files = []
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith(".java"):
                java_files.append(os.path.join(root, file))
    return java_files


def parse_java_file(file_path, symbol_listener, if_listener=None):
    input_stream = FileStream(file_path, encoding="utf-8", errors="ignore")
    lexer = JavaLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = JavaParserLabeled(stream)
    tree = parser.compilationUnit()
    # listener = listener_class()
    walker = ParseTreeWalker()
    # walker.walk(listener, tree)
    walker.walk(symbol_listener, tree)
    if if_listener:
        walker.walk(if_listener, tree)


if __name__ == "__main__":
    project_path = "F:/benchmarks-proposal/ant"
    symbol_listener = SymbolTableListener()
    # Build symbol table
    for file in get_all_java_files(project_path):
        parse_java_file(file, symbol_listener)
    # Detect type checks
    if_listener = MissingHierarchyListener(symbol_listener.abstract_classes,
                                           symbol_listener.subclasses,
                                           symbol_listener.abstract_methods)
    for file in get_all_java_files(project_path):
        parse_java_file(file, symbol_listener, if_listener)

    print("\n=== Type Checking Smells Detected in ===")

    smells = sorted(
        if_listener.type_checking_smells,
        key=lambda s: (s.package, s.class_name, s.method, s.line)
    )
    print(f"Total smells detected: {len(smells)}\n")
    for smell in smells:
        print(
            f"package: {smell.package}\n"
            f"class: {smell.class_name}\n"
            f"method: {smell.method}\n"
            f"(line {smell.line}) --> [{smell.kind}]"
        )
