"""
Utilities related to project directory.
"""
import datetime
import os
import subprocess
import time
from multiprocessing.dummy import Pool, Process, Manager

from antlr4 import FileStream
from antlr4.TokenStreamRewriter import TokenStreamRewriter
from java8speedy.parser import sa_javalabeled
from joblib import Parallel, delayed

from sbse import config
from sbse.config import logger


def git_restore(project_dir):
    """
    This function executes "git restore ." on the given project directory.
    :param project_dir: A string and Absolute path of the project's directory.
    :return: None
    """
    assert os.path.isdir(project_dir)
    exit_code_1 = subprocess.Popen(["git", "restore", "."], cwd=project_dir, stdout=open(os.devnull, 'wb')).wait()
    exit_code_2 = subprocess.Popen(["git", "clean", "-f", "-d"], cwd=project_dir, stdout=open(os.devnull, 'wb')).wait()

    if exit_code_1 != 0 or exit_code_2 != 0:
        logger.warning("Git restore failed. Trying again...")
        time.sleep(1)
        git_restore(project_dir)


def create_understand_database(project_dir):
    """
    This function creates understand database for the given project directory.
    :param und_path: The path of und binary file for executing understand command-line
    :param project_dir: The absolute path of project's directory.
    :return: String path of created database.
    """
    assert os.path.isdir(project_dir)
    db_name = os.path.basename(os.path.normpath(project_dir)) + ".und"
    db_path = os.path.join(project_dir, db_name)
    assert os.path.exists(db_path) is False
    # An example of command-line is:
    # und create -languages c++ add @myFiles.txt analyze -all myDb.udb
    subprocess.Popen(
        ['und', 'create', '-languages', 'Java', 'add', project_dir, 'analyze', '-all', db_path],
        stdout=open(os.devnull, 'wb')
    ).wait()
    return db_path


def update_understand_database(udb_path):
    """
    This function updates database due to file changes.
    :param udb_path: The absolute path of understand database.
    :return: None
    """

    exit_code = subprocess.Popen(
        ['und', 'analyze', '-all', udb_path],
        stdout=open(os.devnull, 'wb')
    ).wait()
    if exit_code == 0:
        return
    elif exit_code == 1:
        # The database is locked or read-only.
        print("Attention!")
        logger.warning("The database is locked or read-only. Trying again...")
        time.sleep(1)
        update_understand_database(udb_path)


def export_understand_dependencies_csv(csv_path: str, db_path: str):
    """
    Exports understand dependencies into a csv file.

    :param csv_path: The absolute address of csv file to generate.
    :param db_path: The absolute address of project path.
    :return: None
    """
    command = ['und', 'export', '-format', 'long', '-dependencies', 'class', 'csv', csv_path, db_path]
    subprocess.Popen(
        command,
        stdout=open(os.devnull, 'wb')
    ).wait()
    print("CSV Exported...")


# -----------------------------------------------
# trees = []
shared_set = set()


def get_java_files(directory):
    if not os.path.isdir(directory):
        raise ValueError("directory should be an absolute path of a directory!")
    for root, dirs, files in os.walk(directory):
        for file in files:
            if file.split('.')[-1] == 'java':
                yield os.path.join(root, file)  # , file
                # print(os.path.join(root, file), file)
                # yield FileStream(os.path.join(root, file), encoding="utf8")


def create_project_parse_tree(java_file_path):
    tree = None
    rewriter = None
    try:
        file_stream = FileStream(java_file_path)
        sa_javalabeled.USE_CPP_IMPLEMENTATION = config.USE_CPP_BACKEND
        tree = sa_javalabeled.parse(file_stream, 'compilationUnit')
        tokens = tree.parser.getInputStream()
        rewriter = TokenStreamRewriter(tokens)
    except Exception as e:
        print(f'Encounter a parsing error on file {java_file_path}')
        print(e)
    return tree, rewriter


def parallel_parsing(directory):
    trees = list()
    input_files = [java_file for java_file in get_java_files(directory)]
    # pool = Pool(processes=8)
    # x = pool.apply_async(create_project_parse_tree, args=(input_files[0], trees))

    # for java_file in get_java_files(directory):
    #     res = pool.apply_async(create_project_parse_tree, (java_file,))  # runs in *only* one process
    #     print(type(res.get(timeout=1)))  #

    # num = Value('d', 0.0)
    # arr = Array('i', range(500))
    with Manager() as manager:
        d = manager.dict()
        q = manager.Queue(10)
        p = Process(target=create_project_parse_tree, args=(input_files[0], q))
        p.start()
        p.join()
        print(q)

    # x.ready()
    # print(len(x.get()))
    # print(arr[0])


def parallel_parsing2(directory):
    for java_file in get_java_files(directory):
        print(java_file)
        p = Process(target=create_project_parse_tree, args=(java_file,))
        p.start()
        # p.join()


def parallel_parsing3(directory):
    d1 = datetime.datetime.now()
    pool = Pool()
    x = pool.map(create_project_parse_tree, get_java_files(directory))
    d2 = datetime.datetime.now()
    print(d2 - d1, len(x))
    return x


# @wrap_non_picklable_objects
def parallel_parsing4(directory):
    d1 = datetime.datetime.now()
    res = Parallel(n_jobs=8, )(
        delayed(create_project_parse_tree)(java_file) for java_file in get_java_files(directory)
    )
    print(res)
    d2 = datetime.datetime.now()
    print(d2 - d1)
    return []


def typical_parsing(directory):
    d1 = datetime.datetime.now()
    x = []
    for java_file in get_java_files(directory):
        x.append(create_project_parse_tree(java_file))
    d2 = datetime.datetime.now()
    print(d2 - d1, len(x))
    return x


if __name__ == '__main__':
    # directory = r'D:/IdeaProjects/JSON20201115/'
    # directory = r'D:/IdeaProjects/jvlt-1.3.2/'
    # directory = r'D:/IdeaProjects/ganttproject_1_11_1_original/'
    # directory = r'D:/IdeaProjects/105_freemind/'
    # directory = r'D:/IdeaProjects/jfreechart-master_original/'
    directory = r'D:/IdeaProjects/107_weka/'
    # directory = r'D:/IdeaProjects/104_vuze/'
    # directory = r'D:/IdeaProjects/Zarebin/'

    # trees = parallel_parsing4(directory)
    # trees = parallel_parsing3(directory)
    trees = typical_parsing(directory)

    # trees = typical_parsing(directory)
    print(f'parse successfully {len(trees)} trees')
