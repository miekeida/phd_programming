import numpy as np
from collections import defaultdict
from typing import List
import json
import itertools
from itertools import chain, combinations
import os

# takes tuple of integers
class block:
    def __init__(self, size_el, num_el):
        self.el_list = np.full(num_el, size_el).tolist()

# takes the function rk([i]) as an input. For example [1,2,3,4] means that it is the free matroids [1,1,2,2] is the matroid with cyclic flats (1,2) and (1,2, 3, 4)
class SchubertMatroid:
    def __init__(self, el_list):
        self.el_list = el_list.copy()
                    
    # accepts a permutation in form of a list            
    def permute(self, perm):
        return np.array(self.el_list)[perm].tolist()

    def get_num_blocks(self):
        return len(self.block_list)
    
    def get_elements(self):
        return self.el_list.copy()

# accepts a list of elements
def r(l): 
    al = []
    r_stead = 0
    for i in range(len(l)): 
        sorted_list = np.sort(l[:i+1])
        help_l = []
        counter = 1
        for j in range(i+1):
            if len(help_l) == 0 and sorted_list[j] > 0:
                help_l.append(counter)
                counter += 1
            else:
                if len(help_l) == 0: 
                    continue
                if sorted_list[j] > help_l[-1]:
                    help_l.append(counter)
                    counter += 1
        r = len(help_l)
        if r > r_stead:
            al.append(1)
        else:
            al.append(0)
        r_stead = r
    return al

def permutationen_liste(n):
    zahlen = np.arange(n)
    permutationen = list(itertools.permutations(zahlen))
    return [list(perm) for perm in permutationen]

def deep_frozenset(iterable):
    return frozenset(deep_frozenset(item) if isinstance(item, list) else item for item in iterable)

def sets_equal(list1, list2):
    return deep_frozenset(list1) == deep_frozenset(list2)

def all_sets_in_list(list1: List[List], list2: List[List]) -> bool:
    set1 = {frozenset(lst) for lst in list1}
    return all(frozenset(lst) in set1 for lst in list2)

class cyc_flat:
    def __init__(self, list, rank, is_cyclic):
        self.list = list
        self.rank = rank
        self.desc = []
        self.size = len(list)
        self.is_cyclic = is_cyclic

    def make_Schubert(self): 
        el_list = []
        S = SchubertMatroid([1], )

def inkl_min_listen(liste_von_listen):
    minimal_listen = []
    for liste in liste_von_listen: 
        ist_minimal = True
        for andere_liste in liste_von_listen: 
            if set(andere_liste).issubset(set(liste)) and len(andere_liste) < len(liste):
                ist_minimal = False
                break
        if ist_minimal:
            minimal_listen.append(liste)
    return minimal_listen

class S_tree:
    def __init__(self, n):
        self.root = cyc_flat([], 0, True)
        self.set_next_ranks(self.root, 1, n)
        self.size_E = n

    def set_next_ranks(self, last_flat, rank, size_E):
        min_size = rank - last_flat.rank + last_flat.size + 1
        if min_size < size_E + 1:
            for i in range(min_size, size_E + 1):
                last_flat.desc.append(cyc_flat([j for j in range(1, i + 1)], rank, True))
            dummy_flat = cyc_flat(last_flat.list, last_flat.rank, False)
            last_flat.desc.append(dummy_flat)
            for desc in last_flat.desc: 
                self.set_next_ranks(desc, rank + 1, size_E)
        else:
            return

    def return_S_matroids(self):
        S_list = []
        self.add_cflat(self.root, [], S_list)
        return S_list

    def add_cflat(self, flat, liste, S_list):
        current_els = liste.copy()
        if len(flat.desc) == 0:
            if len(liste) < self.size_E:
                for i in range(1, self.size_E - len(liste) + 1):
                    liste.append(self.size_E)
            S_list.append(SchubertMatroid(liste))
            return 
        else:
            for desc in flat.desc:
                elements = current_els.copy()
                for i in range(1, desc.size - len(current_els) + 1):
                    elements.append(desc.rank)
                self.add_cflat(desc, elements, S_list)
        return S_list

def is_union_of_circuits(flat, circuits):
    for r in range(1, len(circuits) + 1):
        for combination in combinations(circuits, r):
            union_set = set().union(*combination)
            if union_set == set(flat):
                return True
    return False

def find_cyclic_flats(ranked_flats, circuits):
    result = []
    for flat in ranked_flats:
        if is_union_of_circuits(flat.set, circuits):
            result.append(flat)
    for flat in ranked_flats: 
        if len(flat.set) == 0: 
            result.append(Ranked_set([], 0))
            break
    return result

class Ranked_set:
    def __init__(self, set, rank): 
        self.set = set
        self.rank = rank

class Matroid:
    def __init__(self, n, basis_list): 
        self.size = n
        self.basis_list = {frozenset(basis) for basis in basis_list}
        self.groundset = list(range(1, n + 1))
        self.ranked_sets = []
        if basis_list:
            self.rank = len(next(iter(self.basis_list)))
        power_set = power_s(n)
        self.Ind = alle_teilmengen(basis_list)
        for set in power_set:
            self.ranked_sets.append(Ranked_set(set, max_intersection_size(self.Ind, set)))
        self.ranked_sets.append(Ranked_set([], 0))
        self.ranked_flats = filter_maximal_subsets(self.ranked_sets)
        self.circuits = find_circuits(n, self.Ind)
        self.cyclic_fs = find_cyclic_flats(self.ranked_flats, self.circuits)
    def compare(self, M2):
        return sets_equal(self.basis_list, M2.basis_list)
    def greater(self, M2):
        return all_sets_in_list(self.basis_list, M2.basis_list)

def filter_maximal_subsets(ranked_sets):
    maximal_subsets = {}
    for r_set in ranked_sets:
        r = r_set.rank
        subset = set(r_set.set)
        if r not in maximal_subsets:
            maximal_subsets[r] = [r_set]
        else:
            is_maximal = True
            non_maximal_sets = []
            for existing_set in maximal_subsets[r]:
                existing_subset = set(existing_set.set)
                if subset > existing_subset:
                    non_maximal_sets.append(existing_set)
                elif subset < existing_subset:
                    is_maximal = False
            for non_maximal_set in non_maximal_sets:
                maximal_subsets[r].remove(non_maximal_set)
            if is_maximal:
                maximal_subsets[r].append(r_set)
    result = []
    for subsets in maximal_subsets.values():
        result.extend(subsets)
    return result

def check_cflat_axioms(cflat_list):
    return True

def cyclic_flat_to_basis(n, cflat_list):
    precircuits = []
    if not check_cflat_axioms(cflat_list):
        print("not_a_system_of_cflats")
        return
    for cflat in cflat_list:
        for subset in alle_teilmengen([cflat.list]):
            if len(subset) == cflat.rank + 1:
                precircuits.append(subset)
    circuits = inkl_min_listen(precircuits)
    ind_sets = []
    for menge in power_s(n):
        independent = True
        for circuit in circuits:
            if set(circuit).issubset(menge):
                independent = False
                break
        if independent: 
            ind_sets.append(menge)
    basis_list = []
    rk = max(len(menge) for menge in ind_sets)
    for menge in ind_sets:
        if len(menge) == rk:
            basis_list.append(menge)
    return Matroid(n, basis_list)

def power_s(n):
    if n <= 0:
        return [[]]
    else:
        subsets = []
        for i in range(1, 2**n):
            subset = [j + 1 for j in range(n) if (i >> j) & 1]
            subsets.append(subset)
        return subsets

def find_circuits(n, Ind):
    result = []
    power_set = power_s(n)
    for C in power_set:
        C_set = set(C)
        so_far = False
        if C not in Ind:
            so_far = True
            for e in C:
                C_minus_e = C_set - {e}
                if list(C_minus_e) not in Ind:
                    so_far = False
                    break
            if so_far:
                result.append(C)
    return result

def alle_teilmengen(mengen_liste):
    def teilmengen(menge):
        return chain.from_iterable(combinations(menge, r) for r in range(len(menge) + 1))
    alle_teilmengen = set()
    for menge in mengen_liste:
        for teilmenge in teilmengen(menge):
            alle_teilmengen.add(frozenset(teilmenge))
    return [list(teilmenge) for teilmenge in alle_teilmengen]

def max_intersection_size(unabhängige_Teilmengen, list_2):
    return max(len(set(subset).intersection(set(list_2))) for subset in unabhängige_Teilmengen)

def S_matroid_to_matroid(S_matroid): 
    ind_sets = []
    basis_list = []
    for subset in alle_teilmengen([list(range(1, len(S_matroid.el_list) + 1))]):
        list_2 = sorted(S_matroid.el_list[el - 1] for el in subset)
        if all(list_2[i] >= i + 1 for i in range(len(list_2))):
            ind_sets.append(subset)
    rank = max(len(sets) for sets in ind_sets)
    for sets in ind_sets:
        if len(sets) == rank:
            basis_list.append(sets)
    return Matroid(len(S_matroid.el_list), basis_list)

def remove_duplicates(input_list):
    seen = set()
    unique_list = []
    for item in input_list:
        item_tuple = tuple(item)
        if item_tuple not in seen:
            seen.add(item_tuple)
            unique_list.append(item)
    return unique_list

def multiply_matroids(matroid_1, matroid_2): 
    min_rank = min(matroid_1.rank, matroid_2.rank)
    basis_prod = []
    for basis_1 in matroid_1.basis_list:
        for basis_2 in matroid_2.basis_list: 
            intersect = set(basis_1) & set(basis_2)
            if len(intersect) <= min_rank:
                basis_prod.append(list(intersect))
    basis_prod = remove_duplicates(basis_prod)
    return Matroid(matroid_1.size, basis_prod)

#Baum = S_tree(5)

def multiply_matroids():
    Baum = S_tree(5)
    for S_matroid in Baum.return_S_matroids():
        products = []
        elem = S_matroid.el_list
        for i in range(len(elem)):
            for j in range(len(elem)):
                if elem[i] != elem[j]:
                    neue_liste = elem.copy()
                    neue_liste[j], neue_liste[i] = elem[i], elem[j]
                    S2_matroid = SchubertMatroid(neue_liste)
                    S_M1 = S_matroid_to_matroid(S_matroid)
                    S_M2 = S_matroid_to_matroid(S2_matroid)
                    Prod = multiply_matroids(S_M1, S_M2)
                    products.append(Prod)
                    if len(Prod.cyclic_fs) > 2:
                        print("We multiply ")
                        print(S_matroid.el_list)
                        print("and") 
                        print(S2_matroid.el_list)
                        print("This prod has cyclic flats")
                        for flat in Prod.cyclic_fs:
                            print(flat.set)
                            print(flat.rank)

def read_matroids_from_file(file_path, n, r):
    matroids = []
    with open(file_path, 'r') as file:
        for i, line in enumerate(file):
            if i >= 3000:
                break
            parts = line.strip().split()  
            size = int(parts[1])
            if size < n:
                continue
            if size > n:
                break
            rank = int(parts[2])
            if rank < r: 
                continue
            if rank > r: 
                break
            num_bases = int(parts[3])
            bases = []
            for base in parts[4:]:
                if base.strip("'") != '':
                    new = base.strip("'")
                    digit_list = [int(digit) if digit != '0' else 0 for digit in str(new)]
                    bases.append(digit_list)
            matroids.append(Matroid(size, bases))
    return matroids

def get_matroids(n, r):
    pre_classes_list = read_matroids_from_file('matroids09_bases.txt', n, r) 
    list_matroids = []
    for matroid in pre_classes_list:
        for perm in permutationen_liste(n): 
            new_basis_list = [{perm[el] for el in basis} for basis in matroid.basis_list]
            candidate = Matroid(n, new_basis_list)
            if not any(candidate.compare(m) for m in list_matroids):
                list_matroids.append(candidate)
    return list_matroids

class MatroidGraph:
    def __init__(self, matroids: List):
        self.matroids = matroids
        self.edges = self.build_pre_edges(matroids)
        self.build_edges(matroids)
        
    def build_pre_edges(self, matroids):
        edges = defaultdict(list)
        for a in matroids:
            for b in matroids:
                if a.greater(b) and not a == b:
                    edges[b].append(a)
        return edges
        
    def build_edges(self, matroids):
        edges = self.edges
        for a in matroids:
            for b in matroids:
                if a.greater(b) and not a == b: 
                    liste = self.find_all_paths_lengths(b, a, False)
                    for x in liste:
                        if x != 1:
                            if a in edges[b]:
                                edges[b].remove(a)

    def find_all_paths_lengths(self, start, end, final,  path=None,):
        if path is None:
            path = []
        path = path + [start]
        
        if start == end:
            return [len(path) - 1]
        if self.edges is None:
            return []
        if start not in self.edges:
            return []
        
        lengths = []
        for node in self.edges[start]:
            if node not in path:  # Avoid cycles
                new_lengths = self.find_all_paths_lengths(node, end,final ,path )
                lengths.extend(new_lengths)
                if final and lengths:
                     print(f"Added'{new_lengths}'")

        return lengths
    
def save_list_to_json(data_list, filename="output.json"):
    try:
        with open(filename, "w", encoding="utf-8") as json_file:
            json.dump(data_list, json_file, indent=4, ensure_ascii=False)
        print(f"Liste wurde erfolgreich in '{filename}' gespeichert.")
    except Exception as e:
        print(f"Fehler beim Speichern der Liste: {e}")

if __name__ == "__main__":
    print('hello')
    '''ranklist = []
    for n in range(1, 7):
        for r in range(1, 7):
            if r <= n:
                short = 0 
                matroids = get_matroids(n, r)
                print(f"Generated {len(matroids)} matroids for n={n}, r={r}")
                for i in range(len(matroids)): 
                    if len(matroids[i].basis_list) == 1:
                        short = i
                M = MatroidGraph(matroids)
                lengths = M.find_all_paths_lengths(M.matroids[short], M.matroids[-1], True)
                print(f"Lengths of all paths from matroid {short} to last matroid: {lengths}")
                if all(x == lengths[0] for x in lengths):
                    print('r:')
                    print(r)
                    print('n')
                    print(n)
                    print('rank:')
                    print(lengths[0])
                    ranklist.append([n, r, lengths[0]])
                else: 
                    print('failed')
    save_list_to_json(ranklist)
    print("Final ranklist:", ranklist)'''

M1=Matroid(4, [[0,1]])
M2 = Matroid(4, [[0,1], [1,2]])
M3 = Matroid(4, [[0,1], [1,2], [2,3], [1,4]])
#M = MatroidGraph([M1, M2, M3])
#print(M.find_all_paths_lengths(M1, M3))

M = S_matroid_to_matroid(SchubertMatroid([1,2,2,2,3,4,4]))
Mk= S_matroid_to_matroid(SchubertMatroid([1,1,2,3,3,4,4]))
print('hello')
print(M.basis_list)
print(len(Mk.basis_list))