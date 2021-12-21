import re
import os
import math
from string import Template

############################################################################################
# UTILITIES
############################################################################################

def _get_template(name):
    fh_template = open(os.path.join('convert', f'template_{name}.txt'), 'r')
    raw_template = fh_template.read()
    fh_template.close()
    return Template(raw_template), raw_template

# Returns two templates:
# everything before the `split_on` string, the preamble template, and
# everything after the `split_on` string, the epilog template, and
def _get_split_template(name, split_on):
    t_raw = _get_template(name)[1]
    splt_tmpl = t_raw.split(split_on)
    assert len(splt_tmpl) == 2
    return Template(splt_tmpl[0]), Template(splt_tmpl[1])

def _join_templates(join_string, template, start, end, prefix='', suffix=''):
    r = prefix
    r += join_string.join(template(i) for i in range(start, end))
    return r + suffix
    
############################################################################################
# GRAPH CLASS
############################################################################################

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

    def __init__(self, name, g6, txt, write_floats):
        self.name = name
        self.escaped_g6 = g6.strip().replace('\\', '\\\\')
        self._write_floats = write_floats

        graph_pattern = re.compile('(?P<adjacency>(?:[0-9]+:[0-9 ]*\n)*)(?P<invariants>(?:[a-zA-Z- ]+:.+\n)+)')
        match = graph_pattern.search(txt)
        if not match:
            raise ValueError
        self._size, self._adjacency = self._get_size_adjacency(match.group('adjacency'))
        self._invariants = self._get_invariants(match.group('invariants'))
        
        # INSTANCES DICTIONARY
        # This gets used in the main loop to write out Lean database files for all invariants
        # The key should be just instance_name, without the prefix
        # self.name - name of the graph (i.e. hog007)
        # self._invariants is a dictionary containing a type and a value for each invariant:
        #   { 'type': inv_type, 'value': value }
        # The keys are invariant names used in the HoG exports (also listed in HoGGraph._structure)
        # The values are checked minimally in _get_invariants.
        self.lean_instances = {
            'edge_size': f'\ninstance: hog_edge_size {self.name} := ⟨ {self._invariants["Number of Edges"]["value"]} , rfl ⟩\n'
        }
        
    def _get_size_adjacency(self, raw_adjacency):
        """Return the number of vertices and the list of edges (i, j), such that i < j."""

        adjacency_pattern = re.compile('(?P<vertex>[0-9]+):(?P<neighbors>[0-9 ]*)\n')

        # HoG vertices start at 1
        def to_int_minus1(x):
            """Convert a vertex label of type 1--n to one of type 0--(n-1)"""
            assert int(x) > 0
            return int(x) - 1

        def parse_vertex(match):
            """Given a match group for a list of neighbors of a vertex, return a list of edges"""
            vertex = to_int_minus1(match.group('vertex'))
            # sort and filter the neighbors of vertex
            neighbors = sorted(filter(lambda x: vertex < x, map(to_int_minus1, match.group('neighbors').split())))
            return list(map(lambda x: (vertex, x), neighbors))

        preadjacency = []
        count = 0
        for m in adjacency_pattern.finditer(raw_adjacency):
            count += 1
            preadjacency += parse_vertex(m)
        for p in preadjacency:
            assert p[0] >= 0 and p[1] >= 0
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

        inv_list = {}
        invariant_pattern = re.compile('(?:(?P<invariant>[a-zA-Z- ]+): (?P<value>.+))')
        for m in invariant_pattern.finditer(invariants):
            name = m.group('invariant')
            inv_type = self._structure[name]
            value = checked_invariant_value(inv_type, m.group('value'))
            inv_list[name] = { 'type': inv_type, 'value': value }
        return inv_list

    def lean_graph_def(self):
        """Output a single graph as a Lean structure."""

        template, raw_template = _get_template('graph')
        pad = len(re.search('(?P<indent> *)\$adjacency', raw_template).group('indent'))
        def arc(v1, v2):
            return f'| {v1}, {v2} := tt'
        def line(v1, v2):
            return pad*' ' + arc(v1, v2) + ' ' + arc(v2, v1)
        catch_all = pad*' ' + '| _, _ := ff -- catch all case for false'

        adj = ('\n'.join(line(*e) for e in self._adjacency) + '\n' + catch_all).lstrip()

        return '\n\n' + template.substitute(name=self.name, size=self._size, adjacency=adj)


############################################################################################
# ITERATOR
############################################################################################

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


############################################################################################
# PARSER
############################################################################################

# The main loop
# Writes out all the Lean files

class HoGParser:
    """Converter from original HoG data to Lean code."""

    def __init__(self, settings):
        def number_of_digits(n):
            return int(math.log10(math.ceil(n))) + 1

        self._s = settings
        max_estimate = self._s['graph_id_length']

        if settings['range'] is not None:
            self._first_graph = settings['range']['start']
            self._last_graph = settings['range']['end']
            if self._last_graph > 0:
                max_estimate = number_of_digits(self._last_graph - self._first_graph)
        else:
            self._first_graph = 1
            self._last_graph = 0

        # Set up iterator, possibly skip some graphs
        self._iterator = iter(HoGIterator(settings['srcdir'], self._last_graph, HoGGraph.last_line_start))
        if self._first_graph != 1:
            for _ in range(self._first_graph - 1): # skip self._first_graph-1 graphs
                next(self._iterator)
        
        self._part = 0        
        self._graph_name_length = max_estimate
        self._part_name_length = number_of_digits(pow(10, max_estimate) / self._s['graphs_per_file'])
        self._obj_name = self._s['obj_name']

    def _ensure_output_directory(self):
        """Create the output directory if it does not exist yet."""
        d = self._s['output_path']
        if not os.path.exists(d):
            print (f'Creating {d}')
            os.mkdir(d)

    # Naming conventions, file paths

    def _part_number(self, n):
        """Data part number as a string with leading zeroes."""
        return str(n).zfill(self._part_name_length)

    def _graph_name(self, num):
        """The name of the n-th graph in Lean data modules."""
        return self._obj_name + str(num).zfill(self._graph_name_length)

    def _lean_module_part(self, invariant, n):
        """The name of the n-th Lean data module for an invariant."""
        return f"{self._s['db_name']}{invariant}_{self._part_number(n)}"
    
    def _db_part(self, p):
        """Name of the n-th database structure part"""
        return f'db_{self._part_number(p)}'

    def _output_file_part(self, invariant):
        """The file for the n-th Lean data module for an invariant."""
        return os.path.join(self._s['output_path'], f"{self._lean_module_part(invariant, self._part)}.lean")

    def _output_file_main(self):
        """The name of main Lean data file."""
        return os.path.join(self._s['output_path'], f"{self._s['db_name']}{self._s['db_main']}.lean")
    
    # Templates, files

    def _names_list(self, start, end):
        """Prints a list of lists of graph names from start to end (including end)"""
        gpl = self._s['graphs_per_line']
        if gpl < 1: return ''
        else: return ',\n'.join(
            _join_templates(', ', self._graph_name, i, min(i + gpl, end + 1), '[', ']')
            for i in [start + j*gpl for j in range((end-start)//gpl + 1)]
            )

    def _write_graph_files(self, start):
        """Write a set of graph files, one file for graph definitions, one for each of the invariants"""

        def pfile_open_write_preamble(invariant, preamble):
            """Open the n-th Lean data file for graphs or invariant and write the preamble."""
            fh = open(self._output_file_part(invariant), 'w')
            fh.write(preamble)
            return fh
        def pfile_write_epilog_close(fh, epilog):
            """Write the epilog onto then-th Lean data file for graphs or invariant and close."""
            fh.write(epilog)
            fh.close()

        it_pre, it_epl = _get_split_template('instance', '$instances')
        gt_pre, gt_epl = _get_split_template('db_part', '$graphs')

        # Main loop
        exhausted_all_graphs = False
        had_graphs = False
        for i in range(self._s['graphs_per_file']):
            try:
                count, g6, inv = next(self._iterator)
                graph = HoGGraph(self._graph_name(count), g6, inv, self._s['write_floats'])
                instances = graph.lean_instances

                # If the output path is set, open files at the beginning
                if i == 0 and self._s['output_path'] != None: # write beginning of file
                    had_graphs = True
                    fhg = pfile_open_write_preamble('graph', gt_pre.substitute())
                    fhi = {}
                    for type_class in instances.keys():
                        fhi[type_class] = pfile_open_write_preamble(type_class, it_pre.substitute(module_part=self._lean_module_part('graph', self._part)))

                # Print the graph definition 
                lean_graph = graph.lean_graph_def()
                if self._s['output_path'] != None:
                    fhg.write(lean_graph)
                    for type_class, instance in instances.items():
                        fhi[type_class].write(instance)
                else: # When not writing to files
                    print(lean_graph)

                # Stop if printed enough graphs
                if self._last_graph > 0 and count >= self._last_graph:
                    break

            except StopIteration:
                exhausted_all_graphs = True
                break

        # Close all files that need closing
        if self._s['output_path'] != None and had_graphs:
            pfile_write_epilog_close(fhg, gt_epl.substitute(db_part=self._db_part(self._part), lists=self._names_list(start, count)))
            for type_class in instances.keys():
                pfile_write_epilog_close(fhi[type_class], it_epl.substitute())
        print(f'Converting graphs: {count}  ', end='\r')
        if count == self._last_graph: exhausted_all_graphs = True
        return count, exhausted_all_graphs

    # Write all Lean module files

    def write_lean_files(self):
        """Write the output data to Lean files."""

        # Make sure the output directory exists
        self._ensure_output_directory()

        # Write out data files
        self._part = 1
        exhausted_all_graphs = False
        start_graphs_at = self._first_graph
        while not exhausted_all_graphs:
            count, exhausted_all_graphs = self._write_graph_files(start_graphs_at)
            self._part += 1
            start_graphs_at = count + 1

        # Write out the main data file
        with open(self._output_file_main(), 'w') as fh_out:
            module_imports = _join_templates('\n', lambda p: f'import .{self._lean_module_part("graph", p)}', 1, self._part)
            module_part_names = _join_templates(', ', lambda p: self._db_part(p), 1, self._part)
            template = _get_template('db_main')[0]
            fh_out.write(template.substitute(import_graph_modules=module_imports, db_parts_list=module_part_names))

        # Report on the number of graphs processed
        print(f'Total number of graphs: {count - self._first_graph + 1}')
 