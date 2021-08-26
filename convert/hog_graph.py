import re

class HoGGraph:

    # Invariant names in the HoG data, with their declared types
    # NB: The invariants should have the same order as in the input file
    #     in particular, the last invariant is used in parsing as a terminating condition
    _structure = {
        "Acyclic": "bool",
        "Algebraic Connectivity": "float",
        "Average Degree": "float",
        "Bipartite": "bool",
        "Chromatic Index": "int",
        "Chromatic Number": "int",
        "Circumference": "int",
        "Claw-Free": "bool",
        "Clique Number": "int",
        "Connected": "bool",
        "Density": "float",
        "Diameter": "int",
        "Edge Connectivity": "int",
        "Eulerian": "bool",
        "Genus": "int",
        "Girth": "int",
        "Hamiltonian": "bool",
        "Independence Number": "int",
        "Index": "float",
        "Laplacian Largest Eigenvalue": "float",
        "Longest Induced Cycle": "int",
        "Longest Induced Path": "int",
        "Matching Number": "int",
        "Maximum Degree": "int",
        "Minimum Degree": "int",
        "Minimum Dominating Set": "int",
        "Number of Components": "int",
        "Number of Edges": "int",
        "Number of Triangles": "int",
        "Number of Vertices": "int",
        "Planar": "bool",
        "Radius": "int",
        "Regular": "bool",
        "Second Largest Eigenvalue": "float",
        "Smallest Eigenvalue": "float",
        "Vertex Connectivity": "int"
    }

    last_line_start = "Vertex Connectivity"

    def __init__(self, name, g6, txt, write_floats):
        self.name = name
        self.escaped_g6 = g6.strip().replace('\\', '\\\\')
        self._raw = txt
        self._write_floats = write_floats
    
    def _get_invariants(self, invariants):

        def checked_invariant_value(inv_type, val_str):
            """Validate and convert a string to given value type."""
            value = None
            if val_str in ['undefined', 'Computation time out', 'Computing']:
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

        def get_invariant(match):
            inv = match.group('invariant')
            inv_type = self._structure[inv]
            val = match.group('value')
            value = checked_invariant_value(inv_type, val)
            return inv, inv_type, value

        inv_list = []
        invariant_pattern = re.compile('(?:(?P<invariant>[a-zA-Z- ]+): (?P<value>.+))')
        for m in invariant_pattern.finditer(invariants):
            inv_list.append(get_invariant(m))
        return inv_list

    def graph_to_lean(self):

        # just prints out default for floats
        def lean_property(name, inv_type, value):
            n = (name.lower()).replace(' ', '_').replace('-', '_')
            v = f'some ({value})'
            if value is True:
                v = 'some tt'
            elif value is False:
                v = 'some ff'
            elif value is None or value == 'infinity':
                v = 'none'
            return f'  {n} := {v}'

        graph_pattern = re.compile('(?P<adjacency>(?:[0-9]+:[0-9 ]*\n)*)(?P<invariants>(?:[a-zA-Z- ]+:.+\n)+)')
        match = graph_pattern.search(self._raw)
        if not match:
            raise ValueError
        # size, preadjacency = self._get_preadjacency(match.group('adjacency'))
        
        invariants = ',\n'.join(
            lean_property(*m) for m in self._get_invariants(match.group('invariants'))
            if m[1] != 'float' or self._write_floats # m: (name, inv_type, value)
        )
        
        return (
            f'\n\n'
            f'def {self.name} := {{ hog .\n'
            f'  graph6 := "{self.escaped_g6}",\n'
            f'{invariants}'
            f'\n}}'
        )
    
    def structure_to_lean(self):
        """Output a single graph as a Lean structure."""

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