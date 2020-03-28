import subprocess
import re

# take in a Coq file and dpd file and output an equivalent Coq file with verbose definitions
# and theorems encoded as definitions

# new Coq file: import old Coq file
# preamble: Set Printing All.
# for each def in dpd file, add Print Def.
# run temp coq file and store output somewhere
def printAllDefinitions(dpdgraph, file_prefix, print_option):
    with open('temp.v', 'w') as out, open(dpdgraph, 'r') as dpd:
        out.write('Require Import ' + file_prefix + '.')
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
 #   subprocess.run(['rm', 'temp.txt'])

def createDefinitionMap(dpdgraph, file_prefix, module):
    printAllDefinitions(dpdgraph, file_prefix, 'Print')
    out = {}
    with open('out.txt', 'r') as in_file:
        add_def = ''
        curr = ''
        for line in in_file:
            if not add_def and ' = ' in line:
                split_line = line.split(' = ')
                def_name = split_line[0]
                rest = ' = '.join(split_line[1:]).strip()
                curr += 'Definition ' + def_name.split('.')[1] + ' TYPE := ' + rest + '\n'
                add_def = def_name
            elif not add_def and line.split(' ')[0] == 'Inductive':
                add_def = module + '.' + line.split(' ')[1]
                curr += line
            elif add_def:
                curr += line
            if add_def and line == '\n':
                out[add_def] = curr
                curr = ''
                add_def = ''
    return out

def createTypeMap(dpdgraph, file_prefix, module, names):
    printAllDefinitions(dpdgraph, file_prefix, 'Check')
    out = {}
    with open('out.txt', 'r') as in_file:
        add_def = ''
        curr = ''
        for line in in_file:
            if line.strip() in names:
                if add_def:
                    out[add_def] = curr
                curr = ''
                add_def = line.strip()
            elif add_def:
                curr += line.strip()
    return out

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

def createDefMapWithType(defMap, typeMap, module):
    for key in defMap:
        new_def = defMap[key]
        if new_def.split(' ')[0] != 'Inductive':
            curr_type = typeMap[key]
            new_def = removeType(new_def, curr_type)
            new_def = new_def.replace('TYPE', curr_type)[:-4]
        defMap[key] = new_def[:-2].replace(module + '.', '') + ' .\n'
    return defMap

# current invariants
# - all keywords in prefixes are at start of a line
# - all periods and `Qed.` at end of a line
def generateVerboseCoqFile(orig_prefix, def_map, module):
    with open(orig_prefix + '-verbose.v', 'w') as result, open(orig_prefix + '.v', 'r') as in_file:
        def_keywords = ['Inductive', 'Definition']
        proof_keywords = ['Lemma', 'Theorem', 'Corollary']
        def_print = True
        proof_print = True
        for line in in_file:
            split_line = line.split(' ')
            if split_line[0] == 'Definition':
                def_print = False
                def_name = module + '.' + split_line[1]
                result.write(def_map[def_name])
            elif split_line[0] == 'Inductive':
                def_print = False
                ind_name = split_line[1]
                qual_name = module + '.' + ind_name
                result.write(def_map[qual_name])
                # result.write(def_map[qual_name + '_ind'])
                # if qual_name + '_rec' in def_map.keys():
                #     result.write(def_map[qual_name + '_rec'])
                # if qual_name + '_rect' in def_map.keys():
                #     result.write(def_map[qual_name + '_rect'])
            if split_line[0] in proof_keywords:
                proof_print = False
                def_name = module + '.' + split_line[1]
                result.write(def_map[def_name])
                # replace with verbose def here
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
                    
printAllDefinitions('module-graph.dpd', 'ml_coq', 'Print')

def_map = createDefinitionMap('module-graph.dpd', 'ml_coq', 'MLCoq')
type_map = createTypeMap('module-graph.dpd', 'ml_coq', 'MLCoq', def_map.keys())
full_defs = createDefMapWithType(def_map, type_map, 'MLCoq')

# def_map = createDefinitionMap('out.txt', 'MLCoq')
generateVerboseCoqFile('ml_coq', full_defs, 'MLCoq')

for key in full_defs:
    print(key)
    print(full_defs[key])
