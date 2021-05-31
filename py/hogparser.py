import re
import json

# Load the structure description in JSON

class HoGParser:
    
    _structure = {}
    _is_last_line = None

    _graph_pattern = re.compile('(?P<adjacency>(?:[0-9]+:[0-9 ]*\n)*)(?P<invariants>(?:[a-zA-Z- ]+:.+\n)+)')
    _adjacency_pattern = re.compile('(?P<vertex>[0-9])+:(?P<neighbors>[0-9 ]*)\n')
    _invariant_pattern = re.compile('(?:(?P<invariant>[a-zA-Z- ]+): (?P<value>.+))')

    def __init__(self, hog_struct_path):
        with open(hog_struct_path) as j:
            self._structure = json.load(j)
        last_line_start = list(self._structure)[-1]
        self._is_last_line = lambda line: line.startswith(last_line_start)

    def _convert_name(self, name):
        return (name.lower()).replace(' ', '_').replace('-', '_')

    def _get_preadjacency(self, neighborhoods):
        # HoG vertices start at 1
        def to_int_minus1(x):
            return int(x) - 1
        
        def parse_vertex(match):
            vertex = to_int_minus1(match.group('vertex'))
            # sort and filter the neighbors of vertex
            neighbors = sorted(filter(lambda x: vertex < x, map(to_int_minus1, match.group('neighbors').split())))
            return list(map(lambda x: (vertex, x), neighbors))
        
        preadjacency = []
        count = 0
        for m in self._adjacency_pattern.finditer(neighborhoods):
            count += 1
            preadjacency += parse_vertex(m)
        return count, preadjacency
    
    def _check_invariant(self, inv_type, val_str):
        value = None
        if val_str == 'undefined' or val_str == 'Computation time out':
            value = None
        else:        
            if inv_type == 'bool':
                if val_str in ['Yes', 'No']: # valid bool values
                    value = val_str == 'Yes'
                else:
                    raise ValueError # fail early
            elif val_str == 'infinity': # for now, ok for ints and floats
                value = 'infinity'
            elif inv_type == 'int':
                value = int(val_str)
            elif inv_type == 'float':
                value = float(val_str)
            else:
                raise ValueError # fail early
        return value

    def _get_invariants(self, invariants):
        def get_invariant(match):
            inv = match.group('invariant')
            inv_type = self._structure[inv]
            val = match.group('value')
            value = self._check_invariant(inv_type, val)
            return inv, inv_type, value

        inv_list = []
        for m in self._invariant_pattern.finditer(invariants):
            inv_list.append(get_invariant(m))
        return inv_list

    def _get_lean_inv(self, invariants, write_floats):
        def convert(name, inv_type, value):
            if not write_floats and inv_type == 'float':
                return None
            n = self._convert_name(name)
            v = f'some ({value})'
            if value is True:
                v = 'some ff'
            elif value is False:
                v = 'some ff'
            elif value is None or value == 'infinity':
                v = 'none'
            return f'    {n} := {v}'

        return ',\n'.join(filter(lambda s: s != None, map(lambda m: convert(*m), invariants)))

    def _graph_to_lean(self, num, g6, buffer, write_floats):
        match = self._graph_pattern.search(buffer)
        if not match:
            raise ValueError
        size, preadjacency = self._get_preadjacency(match.group('adjacency'))
        invariants = self._get_invariants(match.group('invariants'))
        lean_str = '  { hog .\n    graph6 := "' + g6.strip().replace('\\', '\\\\') + '",\n'
        if num != 1:
            lean_str = ',\n' + lean_str
        lean_str += self._get_lean_inv(invariants, write_floats)
        lean_str += '\n  }'
        # lean_str = f'def HoG{str(num).zfill(4)} : preadjacency := from_adjacency_list {str(preadjacency)}'
        return lean_str

    def parse(self, input_path, g6_path, output_path = None, write_floats = False):
        fh_in = open(input_path, 'r')
        fh_g6 = open(g6_path, 'r')
        if output_path != None:
            fh_out = open(output_path, 'w')
            fh_out.write('import .hog\n\nnamespace hog\n\ndef database := [\n')
        
        count = 1
        buffer = ''
        for line in fh_in:
            if line == '\n':
                continue
            buffer += line
            graph_complete = self._is_last_line(line)
            # clear buffer
            if not graph_complete:
                continue
            #TODO check if this is the correct g6
            lean_code = self._graph_to_lean(count, fh_g6.readline(), buffer, write_floats)
            if output_path != None:
                fh_out.write(lean_code)
            buffer = ''
            count += 1
        
        if output_path != None:
            fh_out.write('\n]\n\nend hog')
            fh_out.close()
        fh_in.close()
        print(count-1)

    def write_lean_structure(self, write_floats = False):
        out = 'structure hog : Type :=\n (graph6 : string)\n'
        for i, t in self._structure.items():
            n = self._convert_name(i)
            if t == 'bool':
                out += f' ({n} : option bool)\n'
            elif t == 'int':
                out += f' ({n} : option nat)\n'
            elif t == 'float':
                if write_floats:
                    out += f' ({n} : option real)\n'
                else: 
                    continue
            else:
                raise ValueError
        print(out)