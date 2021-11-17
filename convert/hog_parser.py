import re
import os
import math

class HoGGraph:
    """Holds structural information about HoG graphs. 
    Instances represent single graphs and provide a method to output Lean code."""

    # Invariant names in the HoG data, with their declared types
    # NB: The invariants should have the same order as in the input file.
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
    # The last line is used to check the terminating condition
    last_line_start = "Vertex Connectivity"

    def __init__(self, name, g6, txt, lean_type, write_floats):
        self.name = name
        self.escaped_g6 = g6.strip().replace('\\', '\\\\')
        self._raw = txt
        self._write_floats = write_floats
        self._raw_hog_type = lean_type
    
    # def _graph_from_preadjacency(self, num, preadjacency):
    #     return f'def {self._graph_name(num)} : preadjacency := from_adjacency_list {str(preadjacency)}'

    def _get_preadjacency(self, neighborhoods):
        adjacency_pattern = re.compile('(?P<vertex>[0-9])+:(?P<neighbors>[0-9 ]*)\n')

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
        for m in adjacency_pattern.finditer(neighborhoods):
            count += 1
            preadjacency += parse_vertex(m)
        return count, preadjacency

    def _get_invariants(self, invariants):
        """Convert an iterator of invariant strings into a list of tuples (name, type, value)"""

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

        inv_list = []
        invariant_pattern = re.compile('(?:(?P<invariant>[a-zA-Z- ]+): (?P<value>.+))')
        for m in invariant_pattern.finditer(invariants):
            name = m.group('invariant')
            inv_type = self._structure[name]
            value = checked_invariant_value(inv_type, m.group('value'))
            inv_list.append((name, inv_type, value))
        return inv_list

    def to_lean(self):
        """Output a single graph as a Lean structure."""

        # just prints out default for floats
        def lean_property(name, value):
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
        
        count, adj = self._get_preadjacency(match.group('adjacency'))
        adjacency = '\n'.join(
            f'  | {e[0]}, {e[1]} := tt | {e[1]}, {e[0]} := tt' for e in adj
        ) + '\n  | _, _ := ff -- catch all case for false'

        invariants = ',\n'.join(
            lean_property(m[0], m[2]) for m in self._get_invariants(match.group('invariants'))
            if m[1] != 'float' or self._write_floats # m: (name, inv_type, value)
        )
        
        return (
            f'\n\n'
            f'def {self.name} : simple_graph (fin {count}) :=\n'
            f'by from_adjacency {count} with\n'
            f'  λ (i : ℕ) (j : ℕ), (match i, j with'
            f'{adjacency}'
            f'\n'
            f'  end : bool)'
        )
            # f'  graph6 := "{self.escaped_g6}",\n'
            # f'{invariants}'
    
    def structure_to_lean(self):
        """Output the Lean structure definition."""

        out = f'structure {self._raw_hog_type} : Type :=\n (graph6 : string)\n'
        for i, t in self._structure.items():
            n = self.convert_invariant_name(i)
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


# Iterates over the given list of files with HoG exports, graph by graph
# Returns the consecutive number of the current graph, the graph6 and the 
# chunk containing graph theoretic invariants

# Needs a string that appears at the beginning of the last line of the 
# invariant chunk to recognise that it has read data on the current graph.

# If the limit is given as n > 0, the iterator stops after n graphs.
# To process all files, limit should be 0.

class HoGIterator:
    """Iterate through the HoG graphs loaded from given input graphs."""

    def __init__(self, srcdir, limit, last_line_start):
        data_files = list({
            # Assumes files come in pairs, ending with "-g6.txt" and "-inv.txt"
            re.sub('(-g6\.txt|-inv\.txt)$', '', f) for 
            f in os.listdir(srcdir) if os.path.isfile(os.path.join(srcdir, f))
            })
        if len(data_files) == 0:
            raise StopIteration
        data_files.sort()
        self._inputs = iter(data_files)
        self._limit = limit
        self._get_filenames = lambda f: ((f'{srcdir}/{f}-inv.txt', f'{srcdir}/{f}-g6.txt'))
        self._is_last_line = lambda line: line.startswith(last_line_start)

    def __iter__(self):
        self._next_input()
        self._counter = 1
        return self

    def __next__(self):
        if self._limit > 0 and self._counter > self._limit:
            raise StopIteration
        x = self._counter
        inv, g6 = self._read_next_graph()
        self._counter += 1
        return x, g6, inv

    def _next_input(self):
        try:
            self._fh_in.close()
            self._fh_g6.close()
        except:
            pass
        try:
            file_in, file_g6 = self._get_filenames(next(self._inputs))
            self._fh_in = open(file_in, 'r')
            self._fh_g6 = open(file_g6, 'r') # DO NOT USE, THIS IS NOT THE CORRECT GRAPH6!
        except: # stop iterating if out of inputs or can't open file
            raise StopIteration

    def _read_next_graph(self):
        graph = ''
        for line in self._fh_in:
            if line == '\n':
                continue
            graph += line
            if self._is_last_line(line):
                break
        if graph == '':
            self._next_input()
            return self._read_next_graph()
        return graph, self._fh_g6.readline()



class HoGParser:
    """Converter from original HoG data to Lean code."""

    def __init__(self, settings):
        def number_of_digits(n):
            return int(math.log10(math.ceil(n))) + 1

        self._s = settings
        self._hog_iterator = iter(HoGIterator(settings['srcdir'], settings['limit'], HoGGraph.last_line_start))
        self._part = 0
        max_estimate = self._s['graph_id_length']
        if self._s['limit'] > 0:
            max_estimate = number_of_digits(self._s['limit'])
        self._graph_name_length = max_estimate
        self._part_name_length = number_of_digits(pow(10, max_estimate) / self._s['graphs_per_file'])
        self._obj_name = self._s['obj_name']
        self._raw_hog_type = self._s['raw_hog_type']
        self._raw_hog_namespace = self._s['raw_hog_namespace']

    def _ensure_output_directory(self):
        """Create the output directory if it does not exist yet."""
        d = self._s['output_path']
        if not os.path.exists(d):
            print (f'Creating {d}')
            os.mkdir(d)

    # Naming conventions

    def _part_number(self, n):
        """Data part number as a string with leading zeroes."""
        return str(n).zfill(self._part_name_length)

    def _graph_name(self, num):
        """The name of the n-th graph in Lean data modules."""
        return self._obj_name + str(num).zfill(self._graph_name_length)

    def _lean_module_part(self, n):
        """The name of the n-th Lean data module."""
        return f"{self._s['db_name']}{self._part_number(n)}"

    def _output_file_main(self):
        """The name of main Lean data file."""
        return os.path.join(self._s['output_path'], f"{self._s['db_main']}.lean")

    def _output_file_part(self, n):
        """The name of the n-th Lean data file."""
        return os.path.join(self._s['output_path'], f"{self._lean_module_part(n)}.lean")
    
    # Templates

    def _names_list(self, start, end):
        """Prints a list of graph names from start to end (including end)"""
        if self._s['graphs_per_file'] < 1:
            return ''
        r = '[' + self._graph_name(start)
        for i in range(1, end - start + 1):
            br = '],\n[' if ((i) % self._s['graphs_per_line']) == 0 else ', '
            r += br + self._graph_name(start + i)
        return r + ']'
    
    def _get_db_preamble(self):
        return f'import ..tactic\n\nnamespace hog\n\n'

    def _get_db_epilog(self, start, end, part):
        identifier = 'db_' + self._part_number(part)
        return '\n\n\ndef ' + identifier + ' := [\n' + self._names_list(start, end) + '\n]\n\nend hog'
    
    # Write a single file

    def _write_graph_file(self, start):
        exhausted_all_graphs = False
        had_graphs = False
        count = start - 1
        for i in range(self._s['graphs_per_file']):
            try:
                count, g6, inv = next(self._hog_iterator)
                if i == 0 and self._s['output_path'] != None: # write beginning of file
                    had_graphs = True
                    fh_out = open(self._output_file_part(self._part), 'w')
                    fh_out.write(self._get_db_preamble())
                graph = HoGGraph(self._graph_name(count), g6, inv, self._raw_hog_type, self._s['write_floats'])
                lean_code = graph.to_lean()
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
            fh_out.write(self._get_db_epilog(start, count, self._part))
            fh_out.close()
        print(f'Converting graphs: {count}  ', end='\r')
        return count, exhausted_all_graphs

    def _get_main_db(self, num_parts):
        module_imports = '\n'.join([
            f'import .{self._lean_module_part(p)}'
            for p in range(1, num_parts)
            ])
        module_part_names = ', '.join([
            f'db_{self._part_number(p)}'
            for p in range(1, num_parts)
            ])
        return (
            f'import ..tactic\n\n'
            f'{module_imports}\n'
            f'\n\nnamespace hog\n\ndef data := ['
            f'{module_part_names}\n'
            f']\n\nend hog\n'
        )

    # Write all Lean module files

    def write_lean_files(self):
        """Write the output data to Lean files."""

        # Make sure the output directory exists
        self._ensure_output_directory()

        # Write out data files
        self._part = 1
        start = 1
        exhausted_all_graphs = False
        while not exhausted_all_graphs:
            count, exhausted_all_graphs = self._write_graph_file(start)
            self._part += 1
            start = count + 1

        # Write out the main data file
        with open(self._output_file_main(), 'w') as fh_out:
            fh_out.write(self._get_main_db(self._part))
        print(f'Total number of graphs: {count}')