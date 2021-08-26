import re
import math

class Lean_HoG_Template:
    """Helper functions for outputing Lean code."""

    graph_pattern = re.compile('(?P<adjacency>(?:[0-9]+:[0-9 ]*\n)*)(?P<invariants>(?:[a-zA-Z- ]+:.+\n)+)')
    adjacency_pattern = re.compile('(?P<vertex>[0-9])+:(?P<neighbors>[0-9 ]*)\n')
    invariant_pattern = re.compile('(?:(?P<invariant>[a-zA-Z- ]+): (?P<value>.+))')

    def __init__(self, settings):
        self._s = settings
        max_estimate = self._s['total_graphs']
        if self._s['limit'] > 0:
            max_estimate = self._s['limit']
        self._graph_name_length = len(str(max_estimate))
        self._part_name_length = len(str(math.ceil(max_estimate / self._s['graphs_per_file'])))

    def _graph_name(self, num):
        return 'hog' + str(num).zfill(self._graph_name_length)

    # Prints a list of graph names from 1 to n-1
    def _names_list(self, start, end):
        if self._s['graphs_per_file'] < 1:
            return ''
        r = '[' + self._graph_name(start)
        for i in range(1, end - start + 1):
            br = '],\n[' if ((i) % self._s['graphs_per_line']) == 0 else ', '
            r += br + self._graph_name(start + i)
        return r + ']'

    def _graph_from_preadjacency(self, num, preadjacency):
        return f'def {self._graph_name(num)} : preadjacency := from_adjacency_list {str(preadjacency)}'

    def _part_number(self, n):
        """Data part number as a string with leading zeroes."""
        return str(n).zfill(self._part_name_length)

    def lean_module_part(self, n):
        """The name of the n-th Lean data module."""
        return "{0}{1}".format(self._s['db_name'], self._part_number(n))

    def convert_invariant_name(self, name):
        return (name.lower()).replace(' ', '_').replace('-', '_')

    # just prints out default for floats
    def lean_property(self, name, value):
        n = self.convert_invariant_name(name)
        v = f'some ({value})'
        if value is True:
            v = 'some tt'
        elif value is False:
            v = 'some ff'
        elif value is None or value == 'infinity':
            v = 'none'
        return f'  {n} := {v}'

    def get_graph_boilerplate(self, position, g6):
        g6_lean = g6.strip().replace('\\', '\\\\')
        begin = (
            f'\ndef {self._graph_name(position)} := {{ hog .\n'
            f'  graph6 := "{g6_lean}",\n'
        )
        if position != 1:
            begin = '\n' + begin
        end = '\n}'
        return begin, end

    def get_db_preamble(self):
        return 'import ..hog\n\nnamespace hog\n\n'

    def get_db_epilog(self, start, end, part):
        identifier = 'db_' + self._part_number(part)
        return '\n\ndef ' + identifier + ' := [\n' + self._names_list(start, end) + '\n]\n\nend hog'

    def get_main_db(self, num_parts):
        contents = 'import ..hog\n\n'
        for p in range(1, num_parts):
            contents += 'import .{0}\n'.format(self.lean_module_part(p))
        contents += '\n\nnamespace hog\n\ndef data := ['
        contents += ', '.join(['db_' + self._part_number(p) for p in range(1, num_parts)])
        contents += ']\n\nend hog\n'
        return contents
