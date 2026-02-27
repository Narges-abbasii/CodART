import argparse
import re
import os
from collections import defaultdict
from time import time

from antlr4 import *
from antlr4.TokenStreamRewriter import TokenStreamRewriter

from codart.gen.JavaLexer import JavaLexer
from codart.gen.JavaParserLabeled import JavaParserLabeled
from codart.gen.JavaParserLabeledListener import JavaParserLabeledListener


class StrategyPatternRefactoringListenerForIfElse(JavaParserLabeledListener):
    """
    Implementing State/Strategy pattern to refactor type checking
    """

    def __init__(self, common_token_stream: CommonTokenStream = None, method_identifier: str = None, smell_line=None):
        """
        :param common_token_stream:
        """
        self.smell_line = smell_line
        self.capture_body_for = None
        self.is_else_block = False
        self.base_dir = "C:/Users/98910/Desktop/type_checking_examples_before_refactor/if"
        self.getter_signature = None
        self.package_name = None
        self.condition_field = ""
        self.method_identifier = method_identifier
        self.class_identifier = ""
        self.class_fields = set()
        self.private_fields = {}
        self.local_vars = []
        self.old_method_Declaration = ""
        self.new_abstract_method_Declaration = ""
        self.modified_old_method_Declaration = ""
        self.new_abstract_method = ""
        self.method_selected = False
        self.switch = False
        self.switch_condition = ""
        self.method_name = ""
        self.class_methods = {}
        self.getter_declaration = ""
        self.current_method = None
        self.method_returns = {}
        self.method_returns = defaultdict(list)
        self.enter_method = False
        self.methods = {}
        self.methods2 = {}
        self.if_else = False
        self.para = ""
        self.newClasses = ""
        self.body = ""
        self.switch_label = ""
        self.old_method_Declaration2 = ""
        self.new_method_Declaration = ""
        self.inputPara = False
        self.newPara = []
        self.oldPara = []
        self.typePara = []
        self.i = 0
        self.token_stream = common_token_stream
        self.method_identifie = ""
        self.enter_class = False
        self.interface = ""
        self.abstractClass = ""
        self.if_has_return = False
        self.getter_Declaration = []
        self.new_sub_class = ""
        self.getters = {}
        self.filtered_methods = ""
        self.method_return = ""
        self.pending_cases = []
        self.final_method_return = None
        self.method_return = None
        self.pending_cases = []
        self.new_abstract_method_declaration = ""
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
        self.if_stmt_ctx = {}
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
        self.class_f = {}
        self.pending_cases = []
        self.generated_subclasses = []
        self.final_method_return = None
        self.label_text = ""
        self.static_fields = set()
        self.if_expression_text = ""
        self.current_if_label = ""
        self.null_object_body = None
        self.flag = False
        self.constructor_contexts = []
        self.strategy_required_fields = set()
        # Move all the tokens in the source code in a buffer, token_stream_rewriter.
        if common_token_stream is not None:
            self.token_stream_rewriter = TokenStreamRewriter(common_token_stream)
        else:
            raise TypeError('common_token_stream is None')

    def enterPackageDeclaration(self, ctx: JavaParserLabeled.PackageDeclarationContext):
        self.package_name = ctx.qualifiedName().getText()

    def enterCompilationUnit(self, ctx: JavaParserLabeled.CompilationUnitContext):
        self.package_name = ""

    def enterClassDeclaration(self, ctx: JavaParserLabeled.ClassDeclarationContext):
        self.enter_class = True
        self.class_identifier = ctx.IDENTIFIER().getText()

    def enterConstructorDeclaration(self, ctx):
        if not hasattr(self, "constructor_contexts"):
            self.constructor_contexts = []
        self.constructor_contexts.append(ctx)

    def enterFieldDeclaration(self, ctx: JavaParserLabeled.FieldDeclarationContext):
        # Save class field names
        for declarator in ctx.variableDeclarators().variableDeclarator():
            field_name = declarator.variableDeclaratorId().getText()
            field_type = ctx.typeType().getText()
            self.class_f[field_name] = field_type
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
        self.method_contexts[method_name] = ctx
        member_ctx = ctx.parentCtx  # MemberDeclaration*
        class_body_ctx = member_ctx.parentCtx  # ClassBodyDeclaration

        # extract modifiers if present
        modifiers = []
        if hasattr(class_body_ctx, "modifier"):
            modifiers = class_body_ctx.modifier()

        if modifiers:
            start_index = modifiers[0].start.tokenIndex
        else:
            # fallback: start at method identifier
            start_index = ctx.IDENTIFIER().symbol.tokenIndex

        end_index = ctx.formalParameters().stop.tokenIndex

        method_dec = self.token_stream_rewriter.getText(
            "",
            start_index,
            end_index
        )

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
        if self.method_selected:
            self.inputPara = True
            self.oldPara.append(ctx.typeType().getText() + " " + ctx.variableDeclaratorId().getText())
            self.typePara.append(ctx.typeType().getText())
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

    # def enterMethodBody(self, ctx:JavaParserLabeled.MethodBodyContext):
    #     if self.method_selected:
    #         self.if_stmt_ctx = ctx.block()

    def enterStatement2(self, ctx: JavaParserLabeled.Statement2Context):
        if not ctx or not self.method_selected:
            return

        if self.smell_line and ctx.start.line != self.smell_line:
            return
        self.if_stmt_ctx = ctx

        # Mark that we are inside an if-based type check
        self.switch = True  # reuse same pipeline
        self.if_else = True

        expr = ctx.parExpression().expression()
        self.if_expression_text = expr.getText()

        # Expected patterns:
        # if (type == VALUE)
        # if (getType() == VALUE)

        # Case 1: getType() == VALUE
        if hasattr(expr, "binaryOp") or expr.getChildCount() >= 3:
            left = expr.getChild(0).getText()
            right = expr.getChild(2).getText()

            # Normalize condition source
            if left.startswith("get"):
                self.method_name = left
                self.switch_condition = left[3:]
            else:
                self.switch_condition = left
                self.method_name = f"get{left.capitalize()}"


            # Normalize label (ENGINEER → Employee.ENGINEER)
            if "." not in right:
                right = f"{self.class_identifier}.{right}"

            self.label_text = right
            self.switch_label = self.to_pascal_case(right.split(".")[-1])

            self.switch_condition_name = self.switch_condition
            # Normalize switch condition (type → Type)
            self.switch_condition = self.to_pascal_case(self.switch_condition)

            # --- Capture IF body ---
            # Mark that we need to capture the body for this if block
            self.capture_body_for = self.switch_label

            # ----- Rewrite concrete getter if needed -----
            if self.method_name in self.methods:
                old_dec = self.methods[self.method_name]
                return_stmt = f"return {right};"
                new_body = "{ " + return_stmt + " }"
                # Store mapping using switch_label
                self.old_method_dec_with_body_per_case[self.switch_label] = old_dec + " " + new_body
                # self.old_method_dec_with_body_per_case[right] = old_dec + new_body

        # Track that this is not an else block
        self.is_else_block = False

    def enterStatement0(self, ctx: JavaParserLabeled.StatementContext):
        if not ctx or not self.method_selected:
            return

        if self.smell_line and ctx.start.line != self.smell_line:
            return
        start = ctx.start.tokenIndex
        stop = ctx.stop.tokenIndex

        # Get the full text of the block
        body_text = self.token_stream_rewriter.getText("", start, stop).strip()

        # Remove surrounding braces if any
        if body_text.startswith("{") and body_text.endswith("}"):
            body_text = body_text[1:-1].strip()

        # Decide class label
        if getattr(self, "capture_body_for", None):
            # Regular if/else if block
            class_label = self.capture_body_for
            body = body_text
            self.capture_body_for = None
        else:
            # Else block → NullType
            class_label = f"Null{self.switch_condition}"
            body = body_text
            self.is_else_block = True

        # Track return statements
        case_has_return = bool(re.search(r"\breturn\b", body))

        # Prepare case info
        case_info = {
            "label": class_label,
            "switch_label": class_label,
            "body": body,
            "case_has_return": case_has_return,
            "instance_fields": set(self.current_case_instance_fields)
        }
        # Track globally required fields for abstract class
        self.strategy_required_fields.update(self.current_case_instance_fields)

        # Avoid duplicates
        if class_label not in [c["switch_label"] for c in self.pending_cases]:
            self.pending_cases.append(case_info)

        # Clear temporary data
        self.current_case_instance_fields.clear()

        # Optional: print captured body
        print(f"Captured {class_label} body:\n{body}\n")

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
        # 1. Create ABSTRACT getter / discriminator method
        if self.method_name in self.methods:
            abstract_dec = self.methods[self.method_name]

            if "abstract" not in abstract_dec:
                if abstract_dec.startswith(("public ", "protected ", "private ")):
                    vis, rest = abstract_dec.split(" ", 1)
                    abstract_dec = f"{rest}"
                else:
                    abstract_dec = f"{abstract_dec}"

            self.new_abstract_method = abstract_dec + ";"
            print("Modified getter declaration (abstract):", self.new_abstract_method)

        # 2. Sanity checks
        if not self.current_method:
            return

        if getattr(self, "params_injected", False):
            return

        # 3. Decide extra parameters
        extra_params = []
        receiver_name = None

        # Case 1: local variables used
        if self.local_vars:
            extra_params = [f"{t} {n}" for t, n in self.local_vars]

        # Case 2: instance fields used
        elif self.uses_instance_fields:
            receiver_type = self.class_identifier
            receiver_name = receiver_type[0].lower() + receiver_type[1:]
            extra_params = [f"{receiver_type} {receiver_name}"]

        # 4. Inject parameters into method signature
        old_decl = self.old_method_declaration
        paren_index = old_decl.find("(")
        if paren_index == -1:
            return  # invalid signature, stay safe

        before = old_decl[:paren_index + 1]
        after = old_decl[paren_index + 1:]

        self.modified_old_method_declaration = before

        if after.strip().startswith(")"):
            if extra_params:
                self.modified_old_method_declaration += ", ".join(extra_params)
            self.modified_old_method_declaration += after
        else:
            if extra_params:
                self.modified_old_method_declaration += ", ".join(extra_params) + ", "
            self.modified_old_method_declaration += after

        self.params_injected = bool(extra_params)

        print("Modified declaration (signature):",
              self.modified_old_method_declaration)

        # 5. Make the method ABSTRACT
        if "abstract" not in self.modified_old_method_declaration:
            if self.modified_old_method_declaration.startswith(
                    ("public ", "protected ", "private ")
            ):
                vis, rest = self.modified_old_method_declaration.split(" ", 1)
                self.new_abstract_method_declaration = f"{rest}"
            else:
                self.new_abstract_method_declaration = (
                    f"{self.modified_old_method_declaration}"
                )
        else:
            self.new_abstract_method_declaration = (
                self.modified_old_method_declaration
            )

        print("Modified declaration (abstract):",
              self.new_abstract_method_declaration)

        # 6. Generate subclasses (works for SWITCH and IF)
        for case in self.pending_cases:
            body = case["body"]
            if case["instance_fields"] and receiver_name:
                body = self.rewrite_body_with_receiver(body, receiver_name)
            if body and not body.startswith("{"):
                body = "{\n\t" + body + "\n\t}"
            case_label = case["switch_label"]
            subclass_name = case["label"]

            abstract_name = self.switch_condition.split('.')[0]
            abstract_name = abstract_name[0].upper() + abstract_name[1:]

            new_sub_class = (
                    "\npublic class " + subclass_name +
                    " implements " + abstract_name + " {\n\t" +
                    "@Override" + "\n\t" +
                    self.old_method_dec_with_body_per_case.get(case_label, "") +
                    "\n\t" + "@Override" + "\n\t" + self.modified_old_method_declaration
            )

            self.generated_subclasses.append({
                "label": subclass_name,
                "header": new_sub_class,
                "body": body,
                "case_has_return": case["case_has_return"]
            })

    def exitClassDeclaration(self, ctx: JavaParserLabeled.ClassDeclarationContext):
        if not self.method_selected or not self.switch:
            return

        # --- Write all subclasses ---
        for case in self.generated_subclasses:
            body = case["body"]
            if not case.get("case_has_return", False) and getattr(self, "final_method_return", None):
                body = body.rstrip("}") + f"\n\t\t{self.final_method_return}\n\t}}"
                case["body"] = body

            self._write_single_strategy_file(case)
            self.newClasses += case["header"] + body + "\n}"

        # --- Null Object ---
        if getattr(self, "null_object_body", None):
            null_class_name = f"Null{self.switch_condition}"
            if any(c['label'] == null_class_name for c in self.generated_subclasses):
                null_class_name += "Default"
            null_method_body = self.null_object_body
            if null_method_body and not null_method_body.startswith("{"):
                null_method_body = "{\n\t" + null_method_body + "\n\t}"
            null_class = (
                f"\npublic class {null_class_name} implements {self.switch_condition} {{\n\t"
                f"{self.modified_old_method_declaration}\n\t"
                f"{null_method_body}\n}}"
            )
            self.newClasses += null_class
            self._write_null_object_file()

        # --- Abstract base class ---
        abstract_name = self.switch_condition.split('.')[0]
        abstract_name = abstract_name[0].upper() + abstract_name[1:]
        self.abstractClass = (
            f"\npublic interface {abstract_name} {{\n\t"
            f"{self.new_abstract_method}\n\t"
            f"{self.new_abstract_method_declaration};\n}}"
        )

        self._write_abstract_strategy_file(self.base_dir)

        print("Generated subclasses:", self.newClasses)
        print("Generated interface:", self.abstractClass)

        # --- Reset listener state ---
        self.enter_method = False
        self.method_selected = False
        self.enter_class = False
        self.switch = False

        # --- Replace int type with Type field ---
        self.replace_type_variable()
        self.replace_constructor_parameter_type()
        if self.if_else:
            self.replace_if_else_with_delegation()
        self.if_else = False

    def to_pascal_case(self, label: str) -> str:
        parts = label.lower().split('_')
        return ''.join(word.capitalize() for word in parts)

    def make_getter(self, field_name, field_type):
        getter_name = "get" + field_name[0].upper() + field_name[1:]
        return f"{field_type} {getter_name}();"

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
          2. Getter return type
          3. Setter parameter type
        Handles both void and non-void methods and works for any field used as switch condition.
        """
        # Replace field type, getter, setter, and initialize with Null Object
        abstract_type = self.switch_condition  # e.g., "Type"

        for field_name, field_type in self.class_f.items():
            if field_name.lower() != self.switch_condition.lower():
                continue

            field_ctx = self.field_contexts.get(field_name)
            if field_ctx:
                # Replace field type
                start = field_ctx.typeType().start.tokenIndex
                stop = field_ctx.typeType().stop.tokenIndex
                self.token_stream_rewriter.replaceRange(start, stop, abstract_type)
                print(f"Replaced field '{field_name}' type with '{abstract_type}'")

                # Initialize field with Null Object
                stop_token = field_ctx.stop
                insert_index = stop_token.tokenIndex + 1  # insert AFTER semicolon

                # Prepare the assignment code
                # code = f"\n\t{field_name} = new Null{abstract_type}();\n"
                # Pass required fields into Null object constructor
                args = ", ".join(self.strategy_required_fields)

                code = f"\n\t{field_name} = new Null{abstract_type}({args});\n"

                # Insert it using the rewriter
                self.token_stream_rewriter.insertBefore(
                    program_name=self.token_stream_rewriter.DEFAULT_PROGRAM_NAME,
                    index=insert_index,
                    text=code
                )
                print(f"Inserted Null Object assignment for field '{field_name}' after declaration")

            # Replace getter return type
            getter_name = f"get{field_name[0].upper() + field_name[1:]}"
            getter_ctx = self.method_contexts.get(getter_name)
            if getter_ctx:
                result_ctx = getter_ctx.typeTypeOrVoid()  # call the method
                if result_ctx.typeType:
                    start = result_ctx.start.tokenIndex
                    stop = result_ctx.stop.tokenIndex
                    self.token_stream_rewriter.replaceRange(start, stop, abstract_type)
                    print(f"Replaced getter '{getter_name}' return type with '{abstract_type}'")

            # Replace setter parameter type
            setter_name = f"set{field_name[0].upper() + field_name[1:]}"
            setter_ctx = self.method_contexts.get(setter_name)
            if setter_ctx:
                param_list_ctx = setter_ctx.formalParameters().formalParameterList()
                if param_list_ctx:
                    for param in param_list_ctx.formalParameter():
                        param_name = param.variableDeclaratorId().IDENTIFIER().getText()
                        if param_name.lower() == field_name.lower():
                            start = param.typeType().start.tokenIndex
                            stop = param.typeType().stop.tokenIndex
                            self.token_stream_rewriter.replaceRange(start, stop, abstract_type)
                            print(f"Replaced setter '{setter_name}' parameter type with '{abstract_type}'")

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
        os.makedirs(output_dir, exist_ok=True)

        class_name = case["label"]
        file_path = os.path.join(output_dir, f"{class_name}.java")

        with open(file_path, "w", encoding="utf8") as f:
            if self.package_name:
                f.write("package " + self.package_name + ";\n\n")

            f.write(case["header"])
            f.write(case["body"])

            # CLOSE THE CLASS
            f.write("\n}\n")

        print(f"Wrote {file_path}")

    def _write_abstract_strategy_file(self, base_dir: str):
        """
        Write the abstract base strategy class into the same package.
        """
        if not self.abstractClass:
            return

        # Compute package folder
        package_path = ""
        if self.package_name:
            package_path = (
                self.package_name
                .replace("package ", "")
                .replace(";", "")
                .replace(".", os.sep)
            )

        output_dir = os.path.join(base_dir, package_path)
        os.makedirs(output_dir, exist_ok=True)

        abstract_name = self.switch_condition.split('.')[0]
        class_name = abstract_name[0].upper() + abstract_name[1:]
        # class_name = self.switch_condition
        file_path = os.path.join(output_dir, f"{class_name}.java")

        with open(file_path, "w", encoding="utf8") as f:
            if self.package_name:
                f.write("package " + self.package_name + ";\n\n")

            f.write(self.abstractClass)

        print(f"Wrote abstract strategy: {file_path}")

    def replace_if_else_with_delegation(self):
        """
        Replace the entire if/else chain in a method with a delegation to the type object.
        The original method body is fully replaced.
        """

        if not self.if_else or not self.switch_method_name:
            return
        # abstract_name = self.switch_condition.split('.')[0]
        # type_var = abstract_name[0].upper() + abstract_name[1:]
        type_var = self.switch_condition_name  # e.g., "type"
        method_name = self.switch_method_name  # e.g., "m"

        # Delegation code: simple method call to the polymorphic object
        # delegation_code = f"{{\n\t{type_var}.{method_name}();\n}}"
        args = ", ".join(self.strategy_required_fields)

        delegation_code = f"{{\n\t{type_var}.{method_name}({args});\n}}"

        start = self.if_stmt_ctx.start.tokenIndex
        stop = self.if_stmt_ctx.stop.tokenIndex

        # Replace the full method body with delegation
        self.token_stream_rewriter.replaceRange(start, stop, delegation_code)


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

    def replace_constructor_parameter_type(self):

        if not hasattr(self, "constructor_contexts"):
            return

        abstract_type = self.switch_condition

        for ctx in self.constructor_contexts:

            param_list_ctx = ctx.formalParameters().formalParameterList()

            if not param_list_ctx:
                continue

            for param in param_list_ctx.formalParameter():

                param_name = param.variableDeclaratorId().getText()

                if param_name.lower() == self.switch_condition_name.lower():
                    start = param.typeType().start.tokenIndex
                    stop = param.typeType().stop.tokenIndex

                    self.token_stream_rewriter.replaceRange(
                        start,
                        stop,
                        abstract_type
                    )

                    print("Constructor parameter type replaced")

    def detect_used_fields(self, ctx):
        used_fields = set()

        tokens = ctx.getText()

        for field_name in self.class_fields:
            if field_name in tokens:
                used_fields.add(field_name)

        return used_fields


def main(args):
    # Step 1: Load input source into stream
    begin_time = time()
    stream = FileStream(args.file, encoding='utf8', errors='ignore')
    # input_stream = StdinStream()
    # Step 2: Create an instance of AssignmentStLexer
    lexer = JavaLexer(stream)
    # Step 3: Convert the input source into a list of tokens
    token_stream = CommonTokenStream(lexer)
    # Step 4: Create an instance of the AssignmentStParser
    parser = JavaParserLabeled(token_stream)
    parser.getTokenStream()
    # Step 5: Create parse tree
    parse_tree = parser.compilationUnit()
    # Step 6: Create an instance of the refactoringListener, and send as a parameter the list of tokens to the class
    my_listener = StrategyPatternRefactoringListenerForIfElse(common_token_stream=token_stream,
                                                     method_identifier='m')
    #                                                     method_identifier='read')
    #                                                     method_identifier='write')

    walker = ParseTreeWalker()
    walker.walk(t=parse_tree, listener=my_listener)
    refactored_code = my_listener.token_stream_rewriter.getDefaultText()
    print('Compiler result:')
    print(refactored_code)
    with open(args.file, "w", encoding="utf8") as f:
        f.write(refactored_code)
    end_time = time()
    print("execute time : ", end_time - begin_time)


# Test driver
if __name__ == '__main__':
    argparser = argparse.ArgumentParser()
    argparser.add_argument(
        '-n', '--file',
        help='Input source',
        default=r'C:\Users\98910\Desktop\type_checking_examples_before_refactor\if\ContextIfStatement.java')
    args_ = argparser.parse_args()
    main(args_)
