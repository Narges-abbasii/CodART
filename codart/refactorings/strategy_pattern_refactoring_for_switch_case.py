import argparse
import re
from collections import defaultdict
from time import time
import os
from antlr4 import *
from antlr4.TokenStreamRewriter import TokenStreamRewriter
from codart.gen.JavaLexer import JavaLexer
from codart.gen.JavaParserLabeled import JavaParserLabeled
from codart.gen.JavaParserLabeledListener import JavaParserLabeledListener


class StrategyPatternRefactoringListenerForSwitch(JavaParserLabeledListener):
    """
    Implementing State/Strategy pattern to refactor type checking
    """

    def __init__(self, common_token_stream: CommonTokenStream = None, method_identifier: str = None, base_dir= None):
        """
        :param common_token_stream:
        """
        self.base_dir = base_dir
        self.package_name = ""
        self.enter_class = False
        self.class_identifier = ""
        self.class_fields = set()
        self.field_contexts = {}
        self.current_method = None
        self.uses_instance_fields = False
        self.instance_fields = set()
        self.current_case_instance_fields = set()
        self.method_identifier = method_identifier
        self.method_contexts = {}
        self.methods = {}
        self.enter_method = False
        self.method_selected = False
        self.selected_method_ctx = {}
        self.switch_method_name = ""
        self.method_returns = defaultdict(list)
        self.local_vars = []
        self.old_method_declaration = ""
        self.modified_old_method_declaration = ""
        self.method_parameters = set()
        self.local_variables = set()
        self.switch_stmt_ctx = {}
        self.switch_condition_name = ""
        self.switch = False
        self.switch_condition = None
        self.body = ""
        self.case_has_return = False
        self.old_method_dec_with_body_per_case = {}
        self.params_injected = False
        self.token_stream = common_token_stream
        self.newClasses = ""
        self.abstractClass = ""
        self.switch_label = ""
        self.new_abstract_method_declaration = ""
        self.method_name = ""
        self.method_return = ""
        self.new_abstract_method = ""
        self.private_fields = {}
        self.pending_cases = []
        self.generated_subclasses = []
        self.final_method_return = None
        self.label_text = ""
        self.static_fields = set()
        self.null_object_body = None
        self.current_labels = []
        self.getters = {}
        self.switch_field_name = ""
        self.switch_name = ""
        self.extra_params = []

        # Move all the tokens in the source code in a buffer, token_stream_rewriter.
        if common_token_stream is not None:
            self.token_stream_rewriter = TokenStreamRewriter(common_token_stream)
        else:
            raise TypeError('common_token_stream is None')

    def enterCompilationUnit(self, ctx: JavaParserLabeled.CompilationUnitContext):
        if ctx.packageDeclaration():
            self.package_name = ctx.packageDeclaration().getText().replace(";", "").strip()

    def enterClassDeclaration(self, ctx: JavaParserLabeled.ClassDeclarationContext):
        self.enter_class = True
        self.class_identifier = ctx.IDENTIFIER().getText()

    def enterFieldDeclaration(self, ctx: JavaParserLabeled.FieldDeclarationContext):
        # Save class field names
        for declarator in ctx.variableDeclarators().variableDeclarator():
            field_name = declarator.variableDeclaratorId().getText()
            self.class_fields.add(field_name)
            # Save context for later type replacement
            if not hasattr(self, "field_contexts"):
                self.field_contexts = {}
            self.field_contexts[field_name] = ctx

        # Go up to classBodyDeclaration
        class_body_dec = ctx.parentCtx.parentCtx
        modifiers = []
        if hasattr(class_body_dec, "modifier"):
            modifiers = [m.getText() for m in class_body_dec.modifier()]
        if "private" in modifiers:
            field_type = ctx.typeType().getText()
            var_dec = ctx.variableDeclarators().variableDeclarator(0)
            field_name = var_dec.variableDeclaratorId().getText()
            self.private_fields[field_name] = field_type
            # print(f"Collected private field: {field_name} ({field_type})")
        if "static" in modifiers:
            var_dec = ctx.variableDeclarators().variableDeclarator(0)
            field_name = var_dec.variableDeclaratorId().getText()
            self.static_fields.add(field_name)

    def enterMethodDeclaration(self, ctx: JavaParserLabeled.MethodDeclarationContext):
        method_name = ctx.IDENTIFIER().getText()
        if method_name.startswith("get") or method_name.startswith("is"):
            method_body = ctx.methodBody().getText()
            for field in self.class_fields:
                if f"return{field}" in method_body or f"return this.{field}" in method_body:
                    self.getters[method_name] = field

        self.method_contexts[method_name] = ctx
        grand_parent_ctx = ctx.parentCtx.parentCtx
        method_dec = self.token_stream_rewriter.getText("", grand_parent_ctx.modifier(0).
                                                            start.tokenIndex,
                                                            ctx.formalParameters().stop.tokenIndex)
        self.methods[method_name] = method_dec
        if self.method_identifier is None or method_name == self.method_identifier:
            self.current_method = method_name
            self.uses_instance_fields = False  # reset for this method
            if method_name == self.method_identifier:
                self.enter_method = True
                self.method_selected = True
                self.selected_method_ctx = ctx
                self.switch_method_name = method_name
                self.current_method = method_name
                self.method_returns[self.current_method] = []
                self.local_vars = []

                self.old_method_declaration = method_dec
                self.modified_old_method_declaration = method_dec
                print("Old declaration of method:", self.old_method_declaration)

    def enterFormalParameter(self, ctx):
        param_name = ctx.variableDeclaratorId().getText()
        self.method_parameters.add(param_name)

    def enterLocalVariableDeclaration(self, ctx: JavaParserLabeled.LocalVariableDeclarationContext):
        for dec in ctx.variableDeclarators().variableDeclarator():
            var_name = dec.variableDeclaratorId().getText()
            self.local_variables.add(var_name)

        if not self.current_method:
            return

        var_type = ctx.typeType().getText()
        declarator = ctx.variableDeclarators().variableDeclarator(0)
        var_name = declarator.variableDeclaratorId().getText()
        # Collect locals
        if (var_type, var_name) not in self.local_vars:
            self.local_vars.append((var_type, var_name))

    def enterExpression0(self, ctx: JavaParserLabeled.Expression0Context):
        if not self.current_method:
            return
        name = ctx.getText()
        # skip qualified access
        if "." in name:
            return
        # skip locals, parameters, static fields
        if name in self.local_variables or name in self.method_parameters or name in self.static_fields:
            return
        # check exact match against instance fields
        if name in self.private_fields:
            self.uses_instance_fields = True
            self.instance_fields.add(name)
            self.current_case_instance_fields.add(name)

    def enterStatement8(self, ctx: JavaParserLabeled.Statement8Context):
        if not self.method_selected:
            return
        if ctx:
            self.switch_stmt_ctx = ctx
            self.switch_condition_name = ctx.parExpression().expression().getText()
            self.switch_name = ctx.parExpression().expression().getText().replace("()", "")
            if self.switch_name in self.getters:
                self.switch_field_name = self.getters[self.switch_name]
        if not self.method_selected:
            return
        self.switch = True
        expr = ctx.parExpression().expression()

        # Case 1: switch(getSomething())
        if hasattr(expr, "methodCall") and expr.methodCall():
            self.method_name = expr.methodCall().IDENTIFIER().getText()
            if self.method_name.startswith("get") and len(self.method_name) > 3:
                self.switch_condition = self.method_name[3:]
            else:
                self.switch_condition = self.method_name
        # Case 2: switch(type)
        else:
            self.switch_condition = expr.getText()
            s = self.switch_condition[0].upper() + self.switch_condition[1:]
            # self.method_name = f"get{self.switch_condition.capitalize()}"
            self.method_name = f"get{s}"

    def enterSwitchBlockStatementGroup(self, ctx: JavaParserLabeled.SwitchBlockStatementGroupContext):
        if not self.method_selected:
            return
        block_statements = ctx.blockStatement()
        if not block_statements:
            return

        start = block_statements[0].start.tokenIndex
        stop = block_statements[-1].stop.tokenIndex
        body_text = self.token_stream_rewriter.getText("", start, stop).strip()

        # Remove trailing break;
        if body_text.endswith("break;"):
            body_text = body_text[:-6].strip()

        # Detect return inside case
        if re.search(r"\breturn\b", body_text):
            self.case_has_return = True

        # Detect DEFAULT label
        is_default = any(label.DEFAULT() for label in ctx.switchLabel())

        if is_default:
            # capture Null Object behavior
            self.null_object_body = body_text
            return

        self.body = body_text

    def enterSwitchLabel(self, ctx: JavaParserLabeled.SwitchLabelContext):
        if not self.method_selected:
            return
        self.switch = True

        # Detect label
        if ctx.expression():
            self.label_text = ctx.expression().getText()

        # Normalize label (ENGINEER → Employee.ENGINEER)
            if "." not in self.label_text:
                self.label_text = f"{self.class_identifier}.{self.label_text}"

            # Extract subclass name (ENGINEER)
            self.switch_label = self.to_pascal_case(self.label_text.split(".")[-1])
            self.current_labels.append((self.switch_label, self.label_text))

        # Normalize switch condition (getType → EmployeeType)
        self.switch_condition = self.to_pascal_case(self.switch_condition)

        # Rewrite concrete method body
        if self.method_name in self.methods:
            old_dec = self.methods[self.method_name]
            return_stmt = f"return {self.label_text};"
            new_body = "{ " + return_stmt + " }"
            self.old_method_dec_with_body_per_case[self.label_text] = old_dec + new_body

        # Handle case body
        self.case_has_return = "return" in self.body
        if self.body and self.body[0] != "{":
            self.body = "{\n\t" + self.body + "\n\t}"

    def exitSwitchBlockStatementGroup(self, ctx: JavaParserLabeled.SwitchBlockStatementGroupContext):
        if not self.method_selected:
            return

        for switch_label, label_text in self.current_labels:
            case_info = {
                "label": switch_label,
                "switch_label": label_text,
                "body": self.body,
                "case_has_return": "return" in self.body,
                "instance_fields": set(self.current_case_instance_fields)
            }
            self.pending_cases.append(case_info)
            self.current_case_instance_fields.clear()

            # Clear labels for next group
        self.current_labels.clear()

    def enterStatement10(self, ctx: JavaParserLabeled.StatementContext):
        if not self.current_method:
            return
        start = ctx.start.tokenIndex
        stop = ctx.stop.tokenIndex
        text = self.token_stream_rewriter.getText("", start, stop).strip()
        # Capture ONLY method-level return
        if text.startswith("return"):
            self.final_method_return = text

    def exitMethodDeclaration(self, ctx: JavaParserLabeled.MethodDeclarationContext):
        # Create abstract method
        if self.method_name in self.methods:
            abstract_dec = self.methods[self.method_name]
            if "abstract" not in abstract_dec:
                # insert after visibility modifier if present, otherwise at the beginning
                if abstract_dec.startswith(("public ", "protected ", "private ")):
                    parts = abstract_dec.split(" ", 1)
                    # abstract_dec = parts[0] + " abstract " + parts[1]
                    abstract_dec = parts[1]
                    self.new_abstract_method = abstract_dec + ";"
                else:
                    # abstract_dec = "abstract " + self.modified_old_method_declaration
                    abstract_dec = self.modified_old_method_declaration
                    self.new_abstract_method = abstract_dec + ";"
            print("Modified getter declaration (abstract modifier):", self.new_abstract_method)

        if not self.current_method:
            return

        if getattr(self, "params_injected", False):
            return

        self.extra_params = []
        receiver_name = None

        # Case 1: locals exist
        if self.local_vars:
            self.extra_params = [f"{t} {n}" for t, n in self.local_vars]

        # Case 2: no locals, but instance fields used
        elif self.uses_instance_fields:
            receiver_type = self.class_identifier
            receiver_name = receiver_type[0].lower() + receiver_type[1:]
            self.extra_params = [f"{receiver_type} {receiver_name}"]

        # Inject into method signature
        paren_index = self.old_method_declaration.find("(")
        if paren_index == -1:
            return  # still invalid method signature, keep this check

        before = self.old_method_declaration[:paren_index + 1]
        after = self.old_method_declaration[paren_index + 1:]

        if after.strip().startswith(")"):
            self.modified_old_method_declaration = before
            if self.extra_params:
                self.modified_old_method_declaration += ", ".join(self.extra_params)
            self.modified_old_method_declaration += after

            self.new_abstract_method_declaration = self.modified_old_method_declaration
        else:
            self.modified_old_method_declaration = before
            if self.extra_params:
                self.modified_old_method_declaration += ", ".join(self.extra_params) + ", "
            self.modified_old_method_declaration += after

            self.new_abstract_method_declaration = self.modified_old_method_declaration

        self.params_injected = bool(self.extra_params)
        print("Modified declaration (method signature) :", self.modified_old_method_declaration)

        if "abstract" not in self.modified_old_method_declaration:
            # insert after visibility modifier if present, otherwise at the beginning
            if self.modified_old_method_declaration.startswith(("public ", "protected ", "private ")):
                parts = self.modified_old_method_declaration.split(" ", 1)
                self.new_abstract_method_declaration = parts[1]
            else:
                self.new_abstract_method_declaration = self.modified_old_method_declaration
        print("Modified declaration (abstract modifier):", self.new_abstract_method_declaration)

        for case in self.pending_cases:
            body = case["body"]
            if case["instance_fields"]:
                body = self.rewrite_body_with_receiver(
                    body,
                    receiver_name
                )

            if body and body[0] != "{":
                body = "{\n\t" + body + "\n\t}"

            case_label = case["switch_label"]
            label = case["label"]
            new_sub_class = (
                    "\n public class " + label +
                    " implements " + self.switch_condition + "{\n\t"
                    + "@Override" + "\n\t"
                    + self.old_method_dec_with_body_per_case[case_label] +
                    "\n\t" + "@Override" + "\n\t" +
                    self.modified_old_method_declaration
            )

            self.generated_subclasses.append({
                "label": label,
                "header": new_sub_class,
                "body": body,
                "case_has_return": case["case_has_return"]
            })

    def exitClassDeclaration(self, ctx: JavaParserLabeled.ClassDeclarationContext):
        # print("....", self.method_selected, self.switch)
        if self.method_selected and self.switch:
            for case in self.generated_subclasses:
                body = case["body"]

                # Append method-level return ONLY if case has no return
                if not case.get("case_has_return", False) and getattr(self, "final_method_return", None):
                    # Ensure proper indentation
                    body = body.rstrip("}") + f"\t\t{self.final_method_return}\n}}"
                    case["body"] = body

                self.newClasses += case["header"] + body + "\n}"
                self._write_single_strategy_file(case)

            # ---- Generate Null Object ----
            if self.null_object_body:
                null_class_name = f"Null{self.switch_condition}"

                null_method_body = self.null_object_body
                if null_method_body and null_method_body[0] != "{":
                    null_method_body = "{\n\t" + null_method_body + "\n\t}"

                null_class = (
                    f"\npublic class {null_class_name} implements {self.switch_condition} {{\n\t"
                    f"@Override \n\t {self.modified_old_method_declaration}\n\t"
                    f"{null_method_body}\n}}"
                )

                self.newClasses += null_class
                self._write_null_object_file()

            self.generated_subclasses.clear()

            # Build abstract class
            self.abstractClass = (
                f"\npublic interface {self.switch_condition} {{\n\t"
                f"{self.new_abstract_method}\n\t"
                f"{self.new_abstract_method_declaration};\n}}"
            )
            self._write_abstract_strategy_file(self.base_dir)

            print("New subclasses:", self.newClasses)
            print("Interface:", self.abstractClass)

        self.enter_method = False
        self.method_selected = False
        self.enter_class = False

        # Step 1: Replace int type with Type
        # Find token indices for 'private int type;'
        self.replace_type_variable()

        # Step 2: replace switch with delegation
        if self.switch:
            # Assuming last Statement8Context is the switch
            self.replace_switch_with_delegation()

        # Reset
        self.pending_cases.clear()
        self.switch = False

    def to_pascal_case(self, label: str) -> str:
        parts = label.lower().split('_')
        return ''.join(word.capitalize() for word in parts)

    def rewrite_body_with_receiver(self, body, receiver_name):
        for field in self.instance_fields:
            body = re.sub(
                rf"\b{field}\b",
                f"{receiver_name}.{field}",
                body
            )
        return body

    def replace_type_variable(self):
        """
        Replace any int/enum field used as a type in a switch with the new abstract class type.
        This modifies:
          1. Field declaration type
          2. Getter return value
        Handles both void and non-void methods and works for any field used as switch condition.
        """
        abstract_type = self.switch_condition  # the new abstract class type

        for field_name, field_type in self.private_fields.items():
            # Only replace if this field was used in the switch
            # if field_name.lower() == self.switch_condition_name.lower():
            if field_name == self.switch_field_name:

                # Replace field declaration type
                field_ctx = self.field_contexts.get(field_name)
                if field_ctx:
                    start = field_ctx.typeType().start.tokenIndex
                    stop = field_ctx.typeType().stop.tokenIndex
                    self.token_stream_rewriter.replaceRange(start, stop, abstract_type)
                    print(f"Replaced field '{field_name}' type '{field_type}' with '{abstract_type}'")

                # Replace getter return type
                # getter_name = f"get{field_name[0].upper() + field_name[1:]}"
                # getter_ctx = self.method_contexts.get(getter_name)
                getter_ctx = self.method_contexts.get(self.switch_name)
                if getter_ctx:
                    body = getter_ctx.methodBody()
                    if body and body.block():
                        for stmt in body.block().blockStatement():
                            statement = stmt.statement()
                            if statement and statement.RETURN():
                                expr = statement.expression()
                                if expr:
                                    start = expr.start.tokenIndex
                                    stop = expr.stop.tokenIndex
                                    new_expr = f"{field_name}.{self.switch_condition_name}"
                                    self.token_stream_rewriter.replaceRange(start, stop, new_expr)
                                    print("Updated getter return delegation")

                # Initialize with Null Object
                field_ctx = self.field_contexts.get(field_name)
                if field_ctx and self.null_object_body:
                    parent = field_ctx.parentCtx.parentCtx
                    insert_index = parent.stop.tokenIndex - 1
                    self.token_stream_rewriter.insertAfter(
                        insert_index,
                        f"\n\t{field_name} = new Null{abstract_type}()"
                    )

    def _write_single_strategy_file(self, case):
        package_path = ""
        if self.package_name:
            package_path = (
                self.package_name
                .replace("package ", "")
                .replace(";", "")
                .replace(".", os.sep)
            )
            output_dir = os.path.join(self.base_dir, package_path)
        else:
            # No package -> put next to original class file
            output_dir = "C:/Users/98910/Desktop/all_example_for_type_checking/Video_Store_7/Video_Store_7"

        # Make sure directory exists
        os.makedirs(output_dir, exist_ok=True)

        class_name = case["label"]
        file_path = os.path.join(output_dir, f"{class_name}.java")

        if os.path.exists(file_path):
            # File exists: append before last closing brace
            with open(file_path, "r", encoding="utf8") as f:
                content = f.read()

            # Find last closing brace
            last_brace_index = content.rfind("}")
            if last_brace_index == -1:
                # No closing brace found, append at end
                new_content = content + "\n" + self.modified_old_method_declaration + "\n}\n"
            else:
                new_content = content[:last_brace_index] + "\n" + self.modified_old_method_declaration + "\n}\n"

            with open(file_path, "w", encoding="utf8") as f:
                f.write(new_content)

            print(f"Appended to {file_path}")

        else:
            print("uuuu")
            # File does not exist: create normally
            with open(file_path, "w", encoding="utf8") as f:
                if self.package_name:
                    f.write(self.package_name + ";\n\n")

                f.write(case["header"])
                f.write(case["body"])
                f.write("\n}\n")

            print(f"Created {file_path}")

    def _write_abstract_strategy_file(self, base_dir: str):

        if not self.abstractClass:
            return

        package_path = ""
        if self.package_name:
            package_path = (
                self.package_name
                .replace("package  ", "")
                .replace(";", "")
                .replace(".", os.sep)
            )

            output_dir = os.path.join(base_dir, package_path)
        else:
            output_dir = "C:/Users/98910/Desktop/all_example_for_type_checking/Video_Store_7/Video_Store_7"

        os.makedirs(output_dir, exist_ok=True)

        class_name = self.switch_condition
        file_path = os.path.join(output_dir, f"{class_name}.java")

        # CASE 1: File does not exist → create it
        if not os.path.exists(file_path):

            with open(file_path, "w", encoding="utf8") as f:
                if self.package_name:
                    f.write(self.package_name + ";\n\n")

                f.write(self.abstractClass)

            print(f"Created abstract strategy: {file_path}")
            return

        # CASE 2: File exists → append safely
        with open(file_path, "r", encoding="utf8") as f:
            content = f.read()

        last_brace_index = content.rfind("}")
        if last_brace_index == -1:
            # corrupted file fallback
            new_content = content + "\n" + self.new_abstract_method_declaration + "\n}\n"
        else:
            new_content = (
                    content[:last_brace_index]
                    + "\n"
                    + self.new_abstract_method_declaration
                    + "\n}\n"
            )

        with open(file_path, "w", encoding="utf8") as f:
            f.write(new_content)

        print(f"Updated abstract strategy: {file_path}")

    def replace_switch_with_delegation(self):
        """
        Replace switch with unconditional delegation.
        Default behavior is moved into a Null Object.
        """

        if not self.switch_stmt_ctx or not self.selected_method_ctx:
            return

        # type_var = self.switch_condition_name  # e.g., type
        type_var = self.switch_field_name
        method_decl = self.new_abstract_method_declaration
        match = re.search(r"\((.*)\)", method_decl)
        param_str = ""
        param_names = []
        if match:
            param_str = match.group(1)
            # Extract just variable names
            for p in param_str.split(","):
                p = p.strip()  # remove spaces
                if p:
                    name = p.split()[-1]  # last token is the param name
                    param_names.append(name)
        params_str = ", ".join(param_names)
        method_name = f"{self.switch_method_name}({params_str})"
        # method_name = self.switch_method_name  # e.g., m

        default_body = ""

        for block in self.switch_stmt_ctx.switchBlockStatementGroup():
            for label in block.switchLabel():
                if label.DEFAULT():
                    stmts = block.blockStatement()
                    default_body = "\n".join(stmt.getText() for stmt in stmts)

        # TRUE Null Object delegation (no condition!)
        delegation_code = f"{type_var}.{method_name};"

        start = self.switch_stmt_ctx.start.tokenIndex
        stop = self.switch_stmt_ctx.stop.tokenIndex

        self.token_stream_rewriter.replaceRange(start, stop, delegation_code)

    def write_generated_strategy_files(self, base_dir: str):
        """
        Write all generated subclasses into the **same package** as the base class.
        """
        # Compute folder based on package
        package_path = ""
        if self.package_name:
            package_path = self.package_name.replace("package  ", "").replace(";", "").replace(".", os.sep)
        output_dir = os.path.join(base_dir, package_path)
        os.makedirs(output_dir, exist_ok=True)

        # Write each generated subclass
        for case in self.generated_subclasses:
            class_name = case["label"]
            file_path = os.path.join(output_dir, f"{class_name}.java")
            with open(file_path, "w", encoding="utf8") as f:
                if self.package_name:
                    f.write(self.package_name + ";\n\n")
                f.write(case["header"])
                f.write(case["body"])
            print(f"Wrote {file_path}")

    def _write_null_object_file(self):
        if not self.null_object_body:
            return

        package_path = ""
        if self.package_name:
            package_path = (
                self.package_name
                .replace("package ", "")
                .replace(";", "")
                .replace(".", os.sep)
            )

        output_dir = os.path.join(self.base_dir, package_path)
        os.makedirs(output_dir, exist_ok=True)

        class_name = f"Null{self.switch_condition}"
        file_path = os.path.join(output_dir, f"{class_name}.java")

        body = self.null_object_body
        if body and not body.startswith("{"):
            body = "{\n\t" + body + "\n\t}"

        with open(file_path, "w", encoding="utf8") as f:
            if self.package_name:
                f.write(self.package_name + ";\n\n")

            f.write(
                f"public class {class_name} implements {self.switch_condition} {{\n\t"
                f"{self.modified_old_method_declaration}\n\t"
                f"{body}\n}}\n"
            )

        print(f"Wrote {file_path}")


def main(args):
    begin_time = time()

    # Step 1: Load input source
    stream = FileStream(args.file, encoding='utf8', errors='ignore')

    # Step 2: Lexer
    lexer = JavaLexer(stream)

    # Step 3: Token stream
    token_stream = CommonTokenStream(lexer)

    # Step 4: Parser
    parser = JavaParserLabeled(token_stream)

    # Step 5: Parse tree
    parse_tree = parser.compilationUnit()

    # Step 6: Listener
    my_listener = StrategyPatternRefactoringListenerForSwitch(
        common_token_stream=token_stream,
        method_identifier='getCharge'
    )

    # Step 7: Walk tree (THIS populates abstractClass & newClasses)
    walker = ParseTreeWalker()
    walker.walk(t=parse_tree, listener=my_listener)

    # Step 9: Write refactored base class
    refactored_code = my_listener.token_stream_rewriter.getDefaultText()

    print('Compiler result:')
    print(refactored_code)

    with open(args.file, "w", encoding="utf8") as f:
        f.write(refactored_code)

    end_time = time()
    print("execute time : ", end_time - begin_time)


if __name__ == '__main__':
    argparser = argparse.ArgumentParser()
    argparser.add_argument(
        '-n', '--file',
        help='Input source',
        default=r'C:\Users\98910\Desktop\all_example_for_type_checking\Video_Store_7\Video_Store_7\Movie.java')
    args_ = argparser.parse_args()
    main(args_)
