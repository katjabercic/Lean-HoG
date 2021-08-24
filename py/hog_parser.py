import json
import lean_hog_template as lht
import lean_hog_util
import hog_iterator

class HoGParser:
    
    _structure = {}
    _is_last_line = None

    def __init__(self, settings):
        with open(settings['structure_path']) as j:
            self._structure = json.load(j)
        self._s = settings
        self._hog_iterator = iter(hog_iterator.HoGIterator(settings['inputs'], settings['limit'], list(self._structure)[-1]))
        self._lht = lht.Lean_HoG_Template(self._s)
        self._part = 0

    def _output_file_path(self, id):
        s = self._s['output_path'] + '/' + self._s['db_name']
        if isinstance(id, int):
            s += '_' + self._lht.part_filename(id)
        else:
            s += '_' + id
        return s + '.lean'

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
        for m in self._lht.adjacency_pattern.finditer(neighborhoods):
            count += 1
            preadjacency += parse_vertex(m)
        return count, preadjacency

    def _get_invariants(self, invariants):
        def get_invariant(match):
            inv = match.group('invariant')
            inv_type = self._structure[inv]
            val = match.group('value')
            value = lean_hog_util.check_invariant(inv_type, val)
            return inv, inv_type, value

        inv_list = []
        for m in self._lht.invariant_pattern.finditer(invariants):
            inv_list.append(get_invariant(m))
        return inv_list

    def _get_lean_inv(self, invariants):
        def convert(name, inv_type, value):
            if not self._s['write_floats'] and inv_type == 'float':
                return None
            else:
                return self._lht.lean_property(name, value)

        return ',\n'.join(filter(lambda s: s != None, map(lambda m: convert(*m), invariants)))

    def _graph_to_lean(self, position, g6, buffer):
        match = self._lht.graph_pattern.search(buffer)
        if not match:
            raise ValueError
        # size, preadjacency = self._get_preadjacency(match.group('adjacency'))
        invariants = self._get_invariants(match.group('invariants'))
        lean_str, end_graph_str = self._lht.get_graph_boilerplate(position, g6)
        lean_str += self._get_lean_inv(invariants) + end_graph_str
        return lean_str

    def _write_graph_file(self, start):
        exhausted_all_graphs = False
        had_graphs = False
        count = start - 1
        for i in range(self._s['graphs_per_file']):
            try:
                count, g6, inv = next(self._hog_iterator)
                if i == 0 and self._s['output_path'] != None: # write beginning of file
                    had_graphs = True
                    fh_out = open(self._output_file_path(self._part), 'w')
                    fh_out.write(self._lht.get_db_preamble())
                lean_code = self._graph_to_lean(count, g6, inv)
                if self._s['output_path'] != None:
                    fh_out.write(lean_code)
                else:
                    print(lean_code)
                if self._s['limit'] > 0 and count > self._s['limit']:
                    break
            except StopIteration:
                exhausted_all_graphs = True
                break
        if self._s['output_path'] != None and had_graphs:
            fh_out.write(self._lht.get_db_epilog(start, count, self._part))
            fh_out.close()
        print(count, exhausted_all_graphs)
        return count, exhausted_all_graphs

    def write_lean_files(self):
        self._part = 1
        start = 1
        exhausted_all_graphs = False
        while not exhausted_all_graphs:
            count, exhausted_all_graphs = self._write_graph_file(start)
            print(self._part)
            self._part += 1
            start = count + 1
        with open(self._output_file_path('main'), 'w') as fh_out:
            fh_out.write(self._lht.get_main_db(self._part))
        print(count)

    def write_lean_structure(self):
        out = 'structure hog : Type :=\n (graph6 : string)\n'
        for i, t in self._structure.items():
            n = self._lht.convert_invariant_name(i)
            if t == 'bool':
                out += f' ({n} : option bool)\n'
            elif t == 'int':
                out += f' ({n} : option nat)\n'
            elif t == 'float':
                if self._s['write_floats']:
                    out += f' ({n} : option real)\n'
                else: 
                    continue
            else:
                raise ValueError
        print(out)