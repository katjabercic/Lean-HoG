import json
import lean_hog_template as lht

class HoGParser:
    
    _structure = {}
    _is_last_line = None

    def __init__(self, settings):
        with open(settings['structure_path']) as j:
            self._structure = json.load(j)
        last_line_start = list(self._structure)[-1]
        self._is_last_line = lambda line: line.startswith(last_line_start)
        self._write_floats = settings['write_floats']
        self._output_path = settings['output_path']
        self._inputs = settings['inputs']
        self._limit = settings['limit']

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
        for m in lht.adjacency_pattern.finditer(neighborhoods):
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
        for m in lht.invariant_pattern.finditer(invariants):
            inv_list.append(get_invariant(m))
        return inv_list

    def _get_lean_inv(self, invariants):
        def convert(name, inv_type, value):
            if not self._write_floats and inv_type == 'float':
                return None
            else:
                return lht.lean_property(name, value)

        return ',\n'.join(filter(lambda s: s != None, map(lambda m: convert(*m), invariants)))

    def _graph_to_lean(self, position, g6, buffer):
        match = lht.graph_pattern.search(buffer)
        if not match:
            raise ValueError
        # size, preadjacency = self._get_preadjacency(match.group('adjacency'))
        invariants = self._get_invariants(match.group('invariants'))
        lean_str, end_graph_str = lht.get_graph_boilerplate(position, g6)
        lean_str += self._get_lean_inv(invariants) + end_graph_str
        return lean_str

    def _parse_file(self, inv_path, g6_path, fh_out, external_counter):
        fh_in = open(inv_path, 'r')
        fh_g6 = open(g6_path, 'r')
        count = external_counter
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
            lean_code = self._graph_to_lean(count, fh_g6.readline(), buffer)
            if self._output_path != None:
                fh_out.write(lean_code)
            else:
                print(lean_code)
            buffer = ''
            count += 1
            if self._limit > 0 and count > self._limit:
                break
        fh_g6.close()
        fh_in.close()
        return count

    def parse(self, per_line):
        if self._output_path != None:
            fh_out = open(self._output_path, 'w')
            fh_out.write(lht.get_db_preamble())
        count = 1
        for inv_path, g6_path in self._inputs:
                count = self._parse_file(inv_path, g6_path, fh_out, count)
        if self._output_path != None:
            fh_out.write(lht.get_db_epilog(count, per_line))
            fh_out.close()
        print(count-1)

    def write_lean_structure(self):
        out = 'structure hog : Type :=\n (graph6 : string)\n'
        for i, t in self._structure.items():
            n = lht.convert_invariant_name(i)
            if t == 'bool':
                out += f' ({n} : option bool)\n'
            elif t == 'int':
                out += f' ({n} : option nat)\n'
            elif t == 'float':
                if self._write_floats:
                    out += f' ({n} : option real)\n'
                else: 
                    continue
            else:
                raise ValueError
        print(out)