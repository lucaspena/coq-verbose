import subprocess
import re

# take in a Coq file and dpd file and output an equivalent Coq file with verbose definitions
# and theorems encoded as definitions

# generate dpdgraph of Coq file
# dpdgraph contains names of all definitions in a Coq file
def generateModuleGraph(in_file, dpd_file, temp_file):
    in_prefix = in_file.split('.')[0]
    with open(temp_file, 'w') as out, open(in_file, 'r') as coq:
        out.write('Require Import dpdgraph.dpdgraph.')
        out.write('\n')
        out.write('Require Export ' + in_prefix + '.')
        out.write('\n')
        out.write('Set DependGraph File "' + dpd_file + '".')
        out.write('\n')
        out.write('Print FileDependGraph ' + in_prefix + '.')
    subprocess.run(['coqc', temp_file])

# given a dpdgraph containing all definition names:
# create Coq file containing sequence of `Print def.` or `Check def` lines and
# run the file, storing output in a temporary file.
def printAllDefinitions(dpdgraph, in_file, print_option):
    in_prefix = in_file.split('.')[0]
    with open('temp.v', 'w') as out, open(dpdgraph, 'r') as dpd:
        out.write('Require Import ' + in_prefix + '.')
        out.write('\n')
        out.write('Set Printing All.')
        out.write('\n\n')
        for line in dpd:
            path_split = line.strip().split('path=')
            path = ''
            if len(path_split) == 1:
                mod_prefix = ''
            else:
                path = path_split[1].split('"')[1]
                mod_prefix = path + '.'
            curr = path_split[0].strip().split(' ')
            if curr[0] == 'N:':
                out.write(print_option + ' ' + mod_prefix + curr[2].strip('"') + '.')
                out.write('\n')
    with open('temp.txt', 'w') as temp_out:
        subprocess.run(['coqc', 'temp.v'], stdout=temp_out)
    with open('temp.txt', 'r') as temp_out, open('out.txt', 'w') as out:
        for line in temp_out:
            if line != '\n' and ' = ' in line:
                out.write('\n')
            out.write(line)
    subprocess.run(['rm', 'temp.txt'])

# create map from name to Coq definition
# leave placeholder for type to be filled in later
def createDefinitionMap(dpdgraph, in_file):
    printAllDefinitions(dpdgraph, in_file, 'Print')
    out = {}
    with open('out.txt', 'r') as in_file:
        add_def = ''
        curr = ''
        for line in in_file:
            if not add_def and ' = ' in line:
                split_line = line.split(' = ')
                # get non-qualified definition name
                def_name = split_line[0]
                split_def = def_name.split('.')
                if len(split_def) == 2:
                    def_name = split_def[1]
                rest = ' = '.join(split_line[1:]).strip()
                curr += 'Definition ' + def_name + ' TYPE := ' + rest + '\n'
                add_def = def_name
            elif not add_def and line.split(' ')[0] == 'Inductive':
                add_def = line.split(' ')[1]
                curr += line
            elif add_def:
                curr += line
            if add_def and line == '\n':
                out[add_def] = curr
                curr = ''
                add_def = ''
    return out

# create map from name to Coq type
def createTypeMap(dpdgraph, in_file, names):
    printAllDefinitions(dpdgraph, in_file, 'Check')
    out = {}
    with open('out.txt', 'r') as types_file:
        add_def = ''
        curr = ''
        for line in types_file:
            def_name = line.strip()
            split_def = def_name.split('.')
            if len(split_def) == 2:
                def_name = split_def[1]
            if def_name in names:
                if add_def:
                    out[add_def] = curr
                curr = ''
                add_def = def_name
            elif add_def:
                curr += line.strip()
    return out

# remove type from the end of the definition
def removeType(defn, typ):
    stripped_def = re.sub(r"\s+", "", defn)
    stripped_type = re.sub(r"\s+", "", typ)
    j = 0
    for i in range(len(stripped_def)):
        if stripped_def[i:] == stripped_type:
            return defn[:j]
        else:
            j += 1
            while defn[j].isspace():
                j += 1

# create map from name to typed Coq definition. Combine definition map and type map
def createDefMapWithType(defMap, typeMap, module):
    for key in defMap:
        new_def = defMap[key]
        if new_def.split(' ')[0] != 'Inductive':
            curr_type = typeMap[key]
            new_def = removeType(new_def, curr_type)
            new_def = new_def.replace('TYPE', curr_type)[:-4]
        # TODO: remove qualified names in definitions without having to input module
        defMap[key] = new_def[:-2].replace(module + '.', '') + ' .\n'
    return defMap

# generate verbose Coq file from original file. All definitions use completely desugared
# notations, etc. Proofs/lemmas are replaced with the generated definition. The generated
# file is in lockstep with the original file, i.e. definitions/proofs are in the same order
# in the verbose version as the original version.
# current invariants
# - all keywords (Inductive, Definition, etc.) are at start of a line
# - all periods and `Qed.` at end of a line
def generateVerboseCoqFile(orig_file):
    subprocess.run(['coqc', orig_file])
    orig_prefix = orig_file.split('.')[0]
    dpd_file = 'module_graph.dpd'
    temp_file = 'temp.v'
    generateModuleGraph(orig_file, dpd_file, temp_file)
    def_map = createDefinitionMap(dpd_file, orig_file)
    type_map = createTypeMap(dpd_file, orig_file, def_map.keys())
    full_defs = createDefMapWithType(def_map, type_map, 'MLCoq')
    with open(orig_prefix + '_verbose.v', 'w') as result, open(orig_file, 'r') as in_file:
        def_keywords = ['Inductive', 'Definition']
        proof_keywords = ['Lemma', 'Theorem', 'Corollary']
        def_print = True
        proof_print = True
        for line in in_file:
            split_line = line.split(' ')
            if split_line[0] == 'Definition':
                def_print = False
                def_name = split_line[1]
                result.write(def_map[def_name])
            elif split_line[0] == 'Inductive':
                def_print = False
                ind_name = split_line[1]
                result.write(def_map[ind_name])
                # result.write(def_map[ind_name + '_ind'])
                # if ind_name + '_rec' in def_map.keys():
                #     result.write(def_map[ind_name + '_rec'])
                # if ind_name + '_rect' in def_map.keys():
                #     result.write(def_map[ind_name + '_rect'])
            if split_line[0] in proof_keywords:
                proof_print = False
                def_name = split_line[1]
                result.write(def_map[def_name])
            if def_print and proof_print:
                result.write(line)
            elif not def_print:
                if '.' in line:
                    def_print = True
            elif not proof_print:
                if 'Qed' in line or 'Defined' in line:
                    proof_print = True
            else:
                print('ERROR')

generateVerboseCoqFile('ml_coq.v')
