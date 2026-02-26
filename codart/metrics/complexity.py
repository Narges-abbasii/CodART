import os
import time
import traceback

from design_4_testability.class_diagram_extraction.class_diagram import ClassDiagram
from design_4_testability.config import test_class_diagram
from design_4_testability import config
from design_4_testability.config2 import projects_info

import networkx as nx
import csv


class Complexity():
    def __init__(self, class_diagram):
        self.class_diagram = class_diagram.class_diagram_graph
        self.CDG = class_diagram.get_CDG()

        # calculate hierarchical inheritance complexity
        self.inheritance_complexity_dic = {}
        candidate_nodes = self.__find_inheritance_candidates()
        for node in candidate_nodes:
            self.inheritance_complexity_dic[node] = self.__calculate_inheritance_complexity(node)

    # NEW FUNCTION — Fast detection whether a use_def relation exists
    def has_use_def_relation(self, source, target):
        """
        Quickly returns True if there exists ANY path between source → target
        that includes at least one use_def edge.
        """

        # Check each use_def edge and see if it can participate in a path
        for u, v, data in self.CDG.edges(data=True):
            if data.get("relation_type") == "use_def":
                # Is source -> u reachable AND v -> target reachable?
                if nx.has_path(self.class_diagram, source, u) and nx.has_path(self.class_diagram, v, target):
                    return True
        return False

    def calculate_interaction_complexity(self, source, target):

        # Case 1: No path at all → None ---
        if not nx.has_path(self.class_diagram, source, target):
            return None

        # Case 2: Path exists, but no use_def on any path → complexity = 1 ---
        if not self.has_use_def_relation(source, target):
            return 1

        # Case 3: There is use_def on at least one path → compute formula ---
        complexity = 1
        for path in nx.all_simple_paths(self.class_diagram, source=source, target=target):
            complexity *= self.__calculate_path_complexity(path)

        return complexity

    def __calculate_path_complexity(self, path):
        complexity = 1
        for i in range(len(path) - 1):
            u, v = path[i], path[i + 1]
            if self.CDG.has_edge(u, v) and self.CDG[u][v].get('relation_type') == 'use_def':
                if u in self.inheritance_complexity_dic:
                    complexity *= self.inheritance_complexity_dic[u]
        return complexity

    def __calculate_inheritance_complexity(self, node):
        complexity = 0
        stack = [node]
        # stack.append(node)
        depth_dic = {node: 1}

        while stack:
            current_node = stack.pop()
            is_leave = True
            for neighbor in self.CDG[current_node]:
                if current_node in self.CDG[neighbor]:
                    if self.CDG[current_node][neighbor]['relation_type'] == 'child' and self.CDG[neighbor][current_node]['relation_type'] == 'parent':
                        is_leave = False
                        stack.append(neighbor)
                        depth_dic[neighbor] = depth_dic[current_node] + 1

            if is_leave:
                complexity += depth_dic[current_node] * (depth_dic[current_node] - 1)
        return complexity

    def __find_inheritance_candidates(self):
        candidates = set()
        for u, v, d in self.CDG.edges(data=True):
            if d.get('relation_type') == 'parent':
                candidates.add(v)
        return candidates

    def get_matrix(self):
        start_time = time.time()
        node_list = sorted(self.CDG.nodes)
        no_nodes = len(node_list)

        matrix = []
        for s in range(no_nodes):
            matrix.append([])
            for d in range(no_nodes):
                src = node_list[s]
                dst = node_list[d]

                if self.CDG.nodes[src]['type'] == "class" and self.CDG.nodes[dst]['type'] == "class":
                    complexity = self.calculate_interaction_complexity(src, dst)
                    matrix[s].append(complexity)
                else:
                    matrix[s].append(None)
        execution_time = time.time() - start_time
        return matrix, execution_time

    @staticmethod
    def get_avg_of_matrix(matrix):
        n = 0
        s = 0
        for i in matrix:
            for j in i:
                if j is not None:
                    n += 1
                    s += j
        return s / n if n > 0 else 0

    @staticmethod
    def get_sum_of_matrix(matrix):
        return sum(val for row in matrix for val in row if val is not None)

    def save_csv(self, path):
        node_list = list(self.CDG.nodes)
        no_nodes = len(node_list)
        node_list.sort()
        header = ['src', 'dest', 'complexity']

        with open(path, 'w', encoding='UTF8') as f:
            writer = csv.writer(f)
            writer.writerow(header)

            # write the header
            writer.writerow(header)
            for s in range(no_nodes):
                for d in range(no_nodes):
                    src = node_list[s]
                    dst = node_list[d]
                    if self.CDG.nodes[src]['type'] == "class" and self.CDG.nodes[dst]['type'] == "class":
                        complexity = self.calculate_interaction_complexity(src, dst)
                        writer.writerow([src, dst, complexity])


if __name__ == "__main__":
    output_csv = "results_complexity.csv"

    if not os.path.exists(output_csv):
        with open(output_csv, mode='w', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            writer.writerow(["Project Name", "Address", "Number of Nodes", "Sum of Complexities", "Average Complexity"])

    for java_project in projects_info:
        java_project_address = projects_info[java_project]['path']
        base_dirs = projects_info[java_project]['base_dirs']

        print(f'\n=== Running project: {java_project} ===')
        # print('Project address:', java_project_address)
        # print('Base dirs:', base_dirs)

        try:
            cd = ClassDiagram(java_project_address=java_project_address,
                              base_dirs=base_dirs,
                              files=[],
                              index_dic={})
            cd.make_class_diagram()

            c = Complexity(cd)
            node_list = list(cd.class_diagram_graph.nodes)
            node_count = len(node_list)

            total_complexity = 0

            for source in node_list:
                for target in node_list:
                    if source != target:
                        complexity = c.calculate_interaction_complexity(source, target)
                        if complexity is not None:
                            total_complexity += complexity
                            print(f"Interaction Complexity between {source} and {target}: {complexity}")
                        else:
                            print(f"Warning: None value between {source} and {target}")

            average_complexity = total_complexity / node_count if node_count > 0 else 0

            print(f"\n Project: {java_project}")
            print(f"Nodes: {node_count}")
            print(f"Total Complexity: {total_complexity}")
            print(f"Average Complexity: {average_complexity:.2f}")

            with open(output_csv, mode='a', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                writer.writerow([
                    java_project,
                    java_project_address,
                    node_count,
                    total_complexity,
                    round(average_complexity, 2)
                ])
        except Exception as e:
            print(f"Error processing project {java_project}: {e}")
            traceback.print_exc()

