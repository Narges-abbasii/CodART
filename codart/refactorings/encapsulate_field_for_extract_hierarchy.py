from dataclasses import dataclass
from antlr4 import *
from antlr4.TokenStreamRewriter import TokenStreamRewriter
from codart.gen.JavaLexer import JavaLexer
from codart.gen.JavaParserLabeled import JavaParserLabeled
from codart.gen.JavaParserLabeledListener import JavaParserLabeledListener


@dataclass
class ClassModel:
    name: str
    fields: dict
    methods: set
    type_field: str | None = None
    type_field_insert_index: int | None = None


class TypeFieldNormalizationListener(JavaParserLabeledListener):
    """
    Pass 1 — Class normalization / field encapsulation
    Triggered only for classes that have type-checking smells.
    """

    def __init__(self, token_stream: CommonTokenStream, smells_for_class):
        self.rewriter = TokenStreamRewriter(token_stream)
        # self.current_class: ClassModel | None = None
        self.class_stack: list[ClassModel] = []
        self.class_models: dict[str, ClassModel] = {}
        self.smells_for_class = smells_for_class

    def enterClassDeclaration(self, ctx: JavaParserLabeled.ClassDeclarationContext):
        class_name = ctx.IDENTIFIER().getText()

        model = ClassModel(
            name=class_name,
            fields={},
            methods=set()
        )

        self.class_models[class_name] = model
        self.class_stack.append(model)

    def exitClassDeclaration(self, ctx: JavaParserLabeled.ClassDeclarationContext):
        if not self.class_stack:
            return

        model = self.class_stack.pop()

        # Only encapsulate if there are smells in this class
        if not self.smells_for_class:
            return

        field = model.type_field
        field_type = model.fields.get(field)
        insert_index = model.type_field_insert_index

        if not field or not field_type or insert_index is None:
            return

        cap = field[0].upper() + field[1:]
        getter = f"get{cap}"
        setter = f"set{cap}"

        has_getter = getter in model.methods
        has_setter = setter in model.methods

        if has_getter and has_setter:
            return

        code = ""

        if not has_getter:
            code += (
                f"\n\tpublic {field_type} {getter}() {{\n"
                f"\t\treturn {field};\n"
                f"\t}}\n"
            )

        if not has_setter:
            code += (
                f"\n\tpublic void {setter}({field_type} {field}) {{\n"
                f"\t\tthis.{field} = {field};\n"
                f"\t}}\n"
            )

        self.rewriter.insertBefore(
            program_name=self.rewriter.DEFAULT_PROGRAM_NAME,
            index=insert_index,
            text=code
        )

    def enterFieldDeclaration(self, ctx: JavaParserLabeled.FieldDeclarationContext):
        if not self.current_class:
            return

        field_type = ctx.typeType().getText()
        for d in ctx.variableDeclarators().variableDeclarator():
            field_name = d.variableDeclaratorId().getText()
            self.current_class.fields[field_name] = field_type

            stop_token = ctx.stop
            self.current_class.type_field_insert_index = stop_token.tokenIndex + 1

    def enterMethodDeclaration(self, ctx: JavaParserLabeled.MethodDeclarationContext):
        if self.current_class:
            self.current_class.methods.add(ctx.IDENTIFIER().getText())

    def enterStatement8(self, ctx: JavaParserLabeled.Statement8Context):
        if not self.current_class:
            return

        expr = ctx.parExpression().expression()

        # Case: switch(getType())
        if hasattr(expr, "methodCall") and expr.methodCall():
            name = expr.methodCall().IDENTIFIER().getText()
            if name.startswith("get") and len(name) > 3:
                field = name[3:].lower()
                if field in self.current_class.fields:
                    self.current_class.type_field = field
            return

        # Case: switch(type)
        field = expr.getText()
        if field in self.current_class.fields:
            self.current_class.type_field = field

    @property
    def current_class(self):
        return self.class_stack[-1] if self.class_stack else None


def apply_encapsulation(java_file_path: str, smells_for_class):
    with open(java_file_path, "r", encoding="utf-8", errors="ignore") as f:
        source = f.read()

    lexer = JavaLexer(InputStream(source))
    tokens = CommonTokenStream(lexer)
    parser = JavaParserLabeled(tokens)
    tree = parser.compilationUnit()

    listener = TypeFieldNormalizationListener(tokens, smells_for_class)
    walker = ParseTreeWalker()
    walker.walk(listener, tree)

    return listener.rewriter.getDefaultText()
