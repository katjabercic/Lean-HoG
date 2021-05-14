import re
import json

# Load the structure description in JSON

class HoGParser:
    
    _structure = {}
    _is_last_line = None

    _graph_pattern = re.compile('(?P<adjacency>(?:[0-9]+:[0-9 ]*\n)*)(?P<invariants>(?:[a-zA-Z- ]+:.+\n)+)')
    _adjacency_pattern = re.compile('(?P<vertex>[0-9])+:(?P<neighbors>[0-9 ]*)\n')
    _invariant_pattern = re.compile('(?:(?P<invariant>[a-zA-Z- ]+): (?P<value>.+))\n')

    def __init__(self, hog_struct_path):
        with open(hog_struct_path) as j:
            self._structure = json.load(j)
        last_line_start = list(self._structure)[-1]
        self._is_last_line = lambda line: line.startswith(last_line_start)

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
            return inv, value

        inv_list = []
        for m in self._invariant_pattern.finditer(invariants):
            inv, v = get_invariant(m)
            inv_list.append((inv, v))
        return inv_list

    def _graph_to_lean(self, num, buffer):
        match = self._graph_pattern.search(buffer)
        if not match:
            raise ValueError
        size, preadjacency = self._get_preadjacency(match.group('adjacency'))
        invariants = self._get_invariants(match.group('invariants'))
        lean_str = f'def HoG{str(num).zfill(4)} : preadjacency := from_adjacency_list {str(preadjacency)}'
        return lean_str

    
    def parse(self, input_path, output_path = None):
        fh_in = open(input_path, 'r')
        if output_path != None:
            fh_out = open(output_path, 'w')
            fh_out.write('import hog_graph\n\n')
        
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
            lean_code = self._graph_to_lean(count, buffer)
            print(lean_code)
            if output_path != None:
                fh_out.write(lean_code + '\n')
            # else:
            #     print(lean_code)
            buffer = ''
            count += 1
        
        if output_path != None:
            fh_out.close()
        fh_in.close()