import os
import argparse
from time import time
from antlr4 import *
from collections import defaultdict
from codart.gen.JavaLexer import JavaLexer
from codart.gen.JavaParserLabeled import JavaParserLabeled
from codart.refactorings.extract_hierarchy_detection import SymbolTableListener, MissingHierarchyListener, TypeCheckingSmell
from codart.refactorings.encapsulate_field_for_extract_hierarchy import apply_encapsulation
from codart.refactorings.strategy_pattern_refactoring_for_switch_case import StrategyPatternRefactoringListenerForSwitch
from codart.refactorings.strategy_pattern_refactoring_if import StrategyPatternRefactoringListenerForIfElse
from codart.refactorings.replace_conditional_with_polymorphism2 import refactor_project


def get_all_java_files(directory):
    java_files = []
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith(".java"):
                java_files.append(os.path.join(root, file))
    return java_files


def parse_java_file(file_path, listeners):
    """ Walk a parse tree with one or multiple listeners """
    input_stream = FileStream(file_path, encoding="utf-8", errors="ignore")
    lexer = JavaLexer(input_stream)
    token_stream = CommonTokenStream(lexer)
    parser = JavaParserLabeled(token_stream)
    tree = parser.compilationUnit()

    walker = ParseTreeWalker()
    for listener in listeners:
        walker.walk(listener, tree)

    return token_stream, tree


def build_typecheck_index(smells: set[TypeCheckingSmell]):
    by_class = defaultdict(list)
    by_class_method = defaultdict(list)

    for s in smells:
        by_class[s.class_name].append(s)
        by_class_method[(s.class_name, s.method)].append(s)

    return by_class, by_class_method


def main(project_path):
    begin_time = time()

    if not os.path.isdir(project_path):
        print("Error: Provided path is not a directory")
        return

    java_files = get_all_java_files(project_path)
    print(f"Found {len(java_files)} Java files")

    # ===== Step 1: Build symbol table =====
    symbol_listener = SymbolTableListener()
    for file_path in java_files:
        parse_java_file(file_path, [symbol_listener])

    # ===== Step 2: Detect type-checking smells =====
    if_listener = MissingHierarchyListener(
        symbol_listener.abstract_classes,
        symbol_listener.subclasses,
        symbol_listener.abstract_methods
    )
    for file_path in java_files:
        parse_java_file(file_path, [if_listener])

    # === INDEX SMELLS ===
    smells_by_class, smells_by_class_method = build_typecheck_index(if_listener.type_checking_smells)

    # Map class_name -> file_path for easy refactoring
    class_to_file = {os.path.splitext(os.path.basename(f))[0]: f for f in java_files}

    # Report detected smells
    print("\n=== Type Checking Smells Detected ===")
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

    # ===== Step 3: Apply encapsulation/refactoring for smelly files if needed =====
    for file_path in java_files:
        class_name = os.path.splitext(os.path.basename(file_path))[0]
        smells_for_class = smells_by_class.get(class_name, [])
        print(f"Encapsulation: Processing {file_path} smells={len(smells_for_class)}")
        new_source = apply_encapsulation(file_path, smells_for_class)
        with open(file_path, "w", encoding="utf-8") as f:
            f.write(new_source)

    # ===== Step 4: Apply strategy pattern refactoring =====
    for smell in if_listener.type_checking_smells:
        target_file = class_to_file.get(smell.class_name)
        if not target_file or not os.path.exists(target_file):
            continue

        print(f"Strategy Refactoring: {smell.class_name}.{smell.method} in {target_file}")

        # Parse the file again for refactoring
        input_stream = FileStream(target_file, encoding="utf-8")
        lexer = JavaLexer(input_stream)
        token_stream = CommonTokenStream(lexer)
        parser = JavaParserLabeled(token_stream)
        tree = parser.compilationUnit()

        # Choose listener based on smell kind
        if "switch" in smell.kind.lower():
            listener = StrategyPatternRefactoringListenerForSwitch(
                common_token_stream=token_stream,
                method_identifier=smell.method
            )
        elif smell.kind == "IF_ELSE_TYPE_CHECK":  # if-else
            listener = StrategyPatternRefactoringListenerForIfElse(
                common_token_stream=token_stream,
                method_identifier=smell.method,
                smell_line=smell.line
            )
        elif smell.kind == "RTTI":
            print(f"RTTI Refactoring: {smell.class_name}.{smell.method}")

            # IMPORTANT: You need a .udb file path
            udb_path = os.path.join(project_path, f"{os.path.basename(project_path)}.udb")

            refactor_project(
                project_root=project_path,
                output_root=project_path,  # in-place refactor
                udb_path=udb_path,
                target_method=smell.method
            )

            continue

        # Set base_dir dynamically based on the file location
        listener.base_dir = os.path.dirname(target_file)

        walker = ParseTreeWalker()
        walker.walk(listener, tree)

        # Write back the refactored code
        refactored_code = listener.token_stream_rewriter.getDefaultText()
        with open(target_file, "w", encoding="utf-8") as f:
            f.write(refactored_code)

    end_time = time()
    print("Execution completed")
    print("Total files processed:", len(java_files))
    print("Total execution time:", end_time - begin_time)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '-p', '--path',
        default=r"F:\my-refactoring\1",
        help='Path to project folder containing Java files'
    )
    args = parser.parse_args()
    main(args.path)
