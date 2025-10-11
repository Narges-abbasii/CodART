## Introduction

# The module implements Move Field refactoring operation, supporting moving static fields between classes in different packages.

## Pre and post-conditions

### Pre-conditions:
# - The source class, target class, and field must exist in the provided Understand database.
# - The field must not be package-private if moving to a different package.
# - The source and target classes must not be the same.
# - There must be no cyclic dependencies between the source and target classes.

### Post-conditions:
# - The field is moved from the source class to the target class.
# - All references to the field are updated to reflect the new location (e.g., `TargetClass.field_name` for static fields).
# - Necessary import statements are added to the source class if the packages differ.
# - The source class does not contain an instance of the target class for static fields.

__version__ = '0.3.0'
__author__ = 'Morteza Zakeri'

from antlr4.TokenStreamRewriter import TokenStreamRewriter
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass
from collections import defaultdict
import os
import re

from gen.JavaParserLabeled import JavaParserLabeled
from gen.JavaParserLabeledListener import JavaParserLabeledListener
from symbol_table import parse_and_walk

try:
    import understand as und
except ImportError as e:
    print(e)

from config import logger

STATIC = "Public Static Variable"
und.license('B33AYrOUTdC4LBFj')


class CutFieldListener(JavaParserLabeledListener):
    """
    Listener to cut (remove) a field from the source class
    """
    def __init__(self, class_name: str, instance_name: str, field_name: str, target_package: str, is_static: bool, import_statement: str,
                 rewriter: TokenStreamRewriter):
        self.class_name = class_name
        self.field_name = field_name
        self.is_static = is_static
        self.import_statement = import_statement
        self.rewriter = rewriter
        self.instance_name = instance_name
        self.target_package = target_package
        self.is_member = False
        self.do_delete = False
        self.field_text = ""

    def exitPackageDeclaration(self, ctx: JavaParserLabeled.PackageDeclarationContext):
        if self.import_statement:
            self.rewriter.insertAfterToken(
                token=ctx.stop,
                text=self.import_statement,
                program_name=self.rewriter.DEFAULT_PROGRAM_NAME
            )
            self.import_statement = None

    def enterMemberDeclaration2(self, ctx: JavaParserLabeled.MemberDeclaration2Context):
        self.is_member = True

    def exitMemberDeclaration2(self, ctx: JavaParserLabeled.MemberDeclaration2Context):
        self.is_member = False

    def enterVariableDeclaratorId(self, ctx: JavaParserLabeled.VariableDeclaratorIdContext):
        if self.is_member and ctx.IDENTIFIER().getText() == self.field_name:
            self.do_delete = True

    def exitClassBodyDeclaration2(self, ctx: JavaParserLabeled.ClassBodyDeclaration2Context):
        if self.do_delete:
            self.field_text = self.rewriter.getText(
                program_name=self.rewriter.DEFAULT_PROGRAM_NAME,
                start=ctx.start.tokenIndex,
                stop=ctx.stop.tokenIndex
            )
            self.rewriter.replace(
                program_name=self.rewriter.DEFAULT_PROGRAM_NAME,
                from_idx=ctx.start.tokenIndex,
                to_idx=ctx.stop.tokenIndex,
                text=""
            )
            self.do_delete = False


class PasteFieldListener(JavaParserLabeledListener):
    def __init__(self, field_text: str, rewriter: TokenStreamRewriter):
        self.field_text = field_text
        self.rewriter = rewriter

    def enterClassBody(self, ctx: JavaParserLabeled.ClassBodyContext):
        self.rewriter.insertAfterToken(
            token=ctx.start,
            text="\n" + self.field_text + "\n",
            program_name=self.rewriter.DEFAULT_PROGRAM_NAME
        )


class PropagateListener(JavaParserLabeledListener):
    def __init__(self, field_name: str, new_name: str, lines: list, rewriter: TokenStreamRewriter, is_static: bool,
                 target_class: str, target_package: str):
        self.field_name = field_name
        self.new_name = new_name
        self.lines = lines
        self.rewriter = rewriter
        self.is_static = is_static
        self.target_class = target_class
        self.target_package = target_package

    def enterExpression1(self, ctx: JavaParserLabeled.Expression1Context):
        identifier = ctx.IDENTIFIER()
        if identifier and ctx.start.line in self.lines and identifier.getText() == self.field_name:
            if self.is_static:
                self.rewriter.replaceSingleToken(
                    token=ctx.stop,
                    text=f"{self.target_class}.{self.field_name}"
                )
            else:
                self.rewriter.replaceSingleToken(
                    token=ctx.stop,
                    text=self.new_name
                )

    def enterExpression0(self, ctx: JavaParserLabeled.Expression0Context):
        identifier = ctx.getText()
        if identifier and ctx.start.line in self.lines and identifier == self.field_name:
            if self.is_static:
                self.rewriter.replaceSingleToken(
                    token=ctx.stop,
                    text=f"{self.target_class}.{self.field_name}"
                )
            else:
                self.rewriter.replaceSingleToken(
                    token=ctx.stop,
                    text=self.new_name
                )


class CheckCycleListener(JavaParserLabeledListener):
    def __init__(self, class_name: str):
        self.class_name = class_name
        self.is_valid = True
        self.in_constructor = False

    def enterConstructorDeclaration(self, ctx: JavaParserLabeled.ConstructorDeclarationContext):
        self.in_constructor = True

    def exitConstructorDeclaration(self, ctx: JavaParserLabeled.ConstructorDeclarationContext):
        self.in_constructor = False

    def enterCreatedName0(self, ctx: JavaParserLabeled.CreatedName0Context):
        if ctx.IDENTIFIER() and self.in_constructor and self.is_valid:
            identifiers = [i.getText() for i in ctx.IDENTIFIER()]
            if self.class_name in identifiers:
                self.is_valid = False


@dataclass
class FieldUsageInfo:
    field_name: str
    source_class: str
    source_package: str
    is_static: bool
    is_package_private: bool
    usage_in_source: int = 0
    usage_by_class: Dict[str, int] = None

    def __post_init__(self):
        if self.usage_by_class is None:
            self.usage_by_class = defaultdict(int)

    @property
    def primary_external_user(self) -> Optional[Tuple[str, int]]:
        if not self.usage_by_class:
            return None
        return max(self.usage_by_class.items(), key=lambda x: x[1])

    def get_envy_ratio(self, target_class: str) -> float:
        if self.usage_in_source == 0:
            return float('inf')
        target_usage = self.usage_by_class.get(target_class, 0)
        return target_usage / self.usage_in_source


def analyze_field_usage(db: und.Db) -> List[FieldUsageInfo]:
    fields_info = []
    for var in db.ents("Variable"):
        parent = var.parent()
        if not parent or parent.kind().check("Unknown"):
            continue

        if not parent.kind().check("Class"):
            continue

        source_class = parent.name()

        source_package = ""
        if var.library():
            source_package = var.library()
        else:
            parent_file = parent.parent()
            if parent_file and parent_file.kind().check("File"):
                parent_pkg = parent_file.parent()
                if parent_pkg and parent_pkg.kind().check("Package"):
                    source_package = parent_pkg.longname()

        if var.kind().check("Private") or var.kind().check("Protected"):
            continue

        info = FieldUsageInfo(
            field_name=var.name(),
            source_class=source_class,
            source_package=source_package,
            is_static=var.kindname() == STATIC,
            is_package_private=var.kind().check("Package")
        )

        for ref in var.refs("Useby, Setby"):
            ref_ent = ref.ent()
            if not ref_ent:
                continue

            ref_class = ref_ent.parent()
            while ref_class and not ref_class.kind().check("Class"):
                ref_class = ref_class.parent()

            if not ref_class:
                continue

            ref_class_name = ref_class.name()
            if ref_class_name == source_class:
                info.usage_in_source += 1
            else:
                info.usage_by_class[ref_class_name] += 1

        if info.usage_in_source > 0 or len(info.usage_by_class) > 0:
            fields_info.append(info)

    return fields_info


def detect_move_candidates(fields: List[FieldUsageInfo], envy_threshold: float = 2.0, min_usage: int = 3) -> List[Tuple[FieldUsageInfo, str]]:

    candidates = []
    for field in fields:
        if field.primary_external_user is None:
            continue

        target_class, usage_count = field.primary_external_user

        # چک کردن شرایط
        if usage_count < min_usage:
            continue

        if field.is_package_private:
            continue

        ratio = field.get_envy_ratio(target_class)

        if ratio >= envy_threshold:
            logger.debug(f"Candidate found: {field.field_name} "
                         f"({field.source_class} → {target_class}) "
                         f"with ratio {ratio:.2f} "
                         f"(source={field.usage_in_source}, target={usage_count})")
            candidates.append((field, target_class))

    return candidates


def extract_field_type(file_path: str, field_name: str) -> str:
    """
    استخراج نوع فیلد از فایل سورس
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        pattern = rf'(?:public|private|protected)?\s+(?:static\s+)?(?:final\s+)?([\w<>\[\]]+)\s+{field_name}\s*[;=]'
        match = re.search(pattern, content)

        if match:
            return match.group(1)

        return "int"

    except Exception as e:
        logger.debug(f"Could not extract field type: {e}")
        return "int"


def update_target_class_references(
        target_file_path: str,
        source_class: str,
        field_name: str,
        target_class: str
):

    try:
        with open(target_file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        original_content = content

        pattern1 = rf'\b(\w+)\.{field_name}\b'

        def replace_reference(match):
            obj_name = match.group(1)
            if obj_name.lower() == source_class.lower() or \
                    obj_name == source_class[0].lower() + source_class[1:] or \
                    obj_name == 'this':
                return field_name
            return match.group(0)

        content = re.sub(pattern1, replace_reference, content)

        pattern2 = rf'this\.(\w+)\.{field_name}\b'
        content = re.sub(pattern2, f'this.{field_name}', content)

        if content != original_content:
            with open(target_file_path, 'w', encoding='utf-8') as f:
                f.write(content)
            logger.info(f"✅ Updated references in target class: {target_file_path}")
            return True
        else:
            logger.debug(f"No reference updates needed in: {target_file_path}")
            return False

    except Exception as e:
        logger.error(f"Failed to update target class references: {e}")
        return False


def update_constructor_initialization(
        target_file_path: str,
        source_class: str,
        field_name: str,
        field_type: str
):
    try:
        with open(target_file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        original_content = content

        class_name = os.path.splitext(os.path.basename(target_file_path))[0]

        constructor_pattern = rf'(public\s+{class_name}\s*\([^)]*\)\s*\{{)'

        def add_initialization(match):
            constructor_header = match.group(1)

            match_end = match.end()
            next_lines = content[match_end:match_end+500]

            if f'this.{field_name}' in next_lines:
                return constructor_header  # قبلاً اضافه شده

            if field_type in ['int', 'long', 'short', 'byte']:
                init_value = '0'
            elif field_type in ['float', 'double']:
                init_value = '0.0'
            elif field_type == 'boolean':
                init_value = 'false'
            elif field_type == 'char':
                init_value = "'\\0'"
            else:
                init_value = 'null'

            indent = '        '
            init_line = f'\n{indent}this.{field_name} = {init_value};'

            return constructor_header + init_line

        content = re.sub(constructor_pattern, add_initialization, content)

        if content != original_content:
            with open(target_file_path, 'w', encoding='utf-8') as f:
                f.write(content)
            logger.info(f"✅ Updated constructor initialization in: {target_file_path}")
            return True

        return False

    except Exception as e:
        logger.error(f"Failed to update constructor: {e}")
        return False


def remove_source_constructor_initialization(
        source_file_path: str,
        field_name: str
):
    try:
        with open(source_file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()

        original_lines = lines[:]
        filtered_lines = []

        for line in lines:
            # اگر خط شامل مقداردهی فیلد منتقل شده است، حذفش کن
            if re.search(rf'this\.{field_name}\s*=', line):
                logger.debug(f"Removing initialization: {line.strip()}")
                continue
            filtered_lines.append(line)

        if len(filtered_lines) != len(original_lines):
            with open(source_file_path, 'w', encoding='utf-8') as f:
                f.writelines(filtered_lines)
            logger.info(f"✅ Removed field initialization from source constructor")
            return True

        return False

    except Exception as e:
        logger.error(f"Failed to remove source initialization: {e}")
        return False


def main(source_class: str, source_package: str, target_class: str, target_package: str, field_name: str,
         udb_path: str, *args, **kwargs):
    import_statement = None
    if source_package != target_package:
        import_statement = f"\nimport {target_package}.{target_class};"

    instance_name = target_class.lower() + "ByCodArt"
    db = und.open(udb_path)

    field_query = f"{source_package}.{source_class}.{field_name}" if source_package else f".{source_class}.{field_name}"
    field_ent = db.lookup(field_query, "Variable")

    if len(field_ent) == 0:
        logger.error(f"Entity not found with query: {field_query}.")
        db.close()
        return False

    if source_package == target_package and source_class == target_class:
        logger.error("Can not move to self.")
        db.close()
        return False

    field_ent = field_ent[0]
    is_static = field_ent.kindname() == STATIC

    if source_package != target_package and field_ent.kind().check("package"):
        logger.error(f"Cannot move package-private field {field_name} to a different package.")
        db.close()
        return False

    if is_static:
        logger.debug("Field is static")

    usages = {}
    for ref in field_ent.refs("Setby, Useby"):
        file = ref.file().longname()
        usages.setdefault(file, []).append(ref.line())

    try:
        src_class_file = db.lookup(f"{source_package}.{source_class}.java")[0].longname()
        target_class_file = db.lookup(f"{target_package}.{target_class}.java")[0].longname()
    except IndexError:
        logger.error("This is a nested class.")
        db.close()
        return False

    db.close()

    listener = parse_and_walk(file_path=target_class_file, listener_class=CheckCycleListener, class_name=source_class)
    if not listener.is_valid:
        logger.error(f"Can not move field because there is a cycle between {source_class}, {target_class}")
        return False

    for file in usages.keys():
        parse_and_walk(
            file_path=file,
            listener_class=PropagateListener,
            has_write=True,
            field_name=field_name,
            new_name=f"{field_name}",
            lines=usages[file],
            is_static=is_static,
            target_class=target_class,
            target_package=target_package
        )

    listener = parse_and_walk(
        file_path=src_class_file,
        listener_class=CutFieldListener,
        has_write=True,
        class_name=target_class,
        instance_name=instance_name,
        field_name=field_name,
        is_static=is_static,
        import_statement=import_statement,
        target_package=target_package
    )
    field_text = listener.field_text

    parse_and_walk(
        file_path=target_class_file,
        listener_class=PasteFieldListener,
        has_write=True,
        field_text=field_text,
    )


    field_type = extract_field_type(src_class_file, field_name)

    update_target_class_references(
        target_file_path=target_class_file,
        source_class=source_class,
        field_name=field_name,
        target_class=target_class
    )

    update_constructor_initialization(
        target_file_path=target_class_file,
        source_class=source_class,
        field_name=field_name,
        field_type=field_type
    )

    remove_source_constructor_initialization(
        source_file_path=src_class_file,
        field_name=field_name
    )

    logger.info(f"✅ Successfully moved field '{field_name}' from {source_class} to {target_class}")
    return True


def auto_move_fields(udb_path: str, envy_threshold: float = 2.0, min_usage: int = 3):
    if not os.path.exists(udb_path):
        logger.error(f"Understand database not found: {udb_path}")
        return

    db = und.open(udb_path)
    logger.info("Analyzing project for Move Field opportunities...")

    fields_info = analyze_field_usage(db)
    logger.info(f"Found {len(fields_info)} field candidates for analysis.")

    candidates = detect_move_candidates(fields_info, envy_threshold, min_usage)
    logger.info(f"Detected {len(candidates)} move field candidates.")

    success_count = 0
    for field_info, target_class in candidates:
        logger.info(f"Automatically moving field {field_info.field_name} from {field_info.source_class} → {target_class}")

        result = main(
            source_class=field_info.source_class,
            source_package=field_info.source_package,
            target_class=target_class,
            target_package=field_info.source_package,  # فرض: همان package
            field_name=field_info.field_name,
            udb_path=udb_path
        )

        if result:
            success_count += 1

    db.close()
    logger.info(f"Automatic Move Field finished. Successfully moved {success_count}/{len(candidates)} fields.")


def debug_database_info(udb_path: str):
    db = und.open(udb_path)

    print("\n" + "="*60)
    print("DATABASE ANALYSIS")
    print("="*60)

    # نمایش packages
    print("\n📦 PACKAGES:")
    packages = db.ents("Package")
    for pkg in packages:
        print(f"  - {pkg.longname()}")

    # نمایش کلاس‌ها
    print("\n🏛️  CLASSES:")
    classes = db.ents("Class")
    for cls in classes:
        parent = cls.parent()
        pkg_name = ""
        if parent and parent.kind().check("File"):
            pkg_parent = parent.parent()
            if pkg_parent and pkg_parent.kind().check("Package"):
                pkg_name = pkg_parent.longname()
        print(f"  - {cls.name()} (package: {pkg_name})")

    # نمایش فیلدها
    print("\n📌 FIELDS:")
    variables = db.ents("Variable")
    for var in variables:
        parent = var.parent()
        if parent and parent.kind().check("Class"):
            refs = list(var.refs('Useby, Setby'))
            print(f"  - {var.name()} in {parent.name()} "
                  f"(kind: {var.kindname()}, "
                  f"refs: {len(refs)}, "
                  f"package: {var.library()})")

    print("\n" + "="*60 + "\n")
    db.close()


if __name__ == '__main__':
    UDB_PATH = "/Users/snapp/Documents/Codes/MyProject/test-for-codart/test-for-codart.und"

    auto_move_fields(UDB_PATH, envy_threshold=2.0, min_usage=3)

    # main(
    #     source_class="Book",
    #     source_package="library",
    #     target_class="BookStatistics",
    #     target_package="library",
    #     field_name="totalViews",
    #     udb_path=UDB_PATH
    # )
