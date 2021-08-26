import os
import lean_hog_template as lht
import hog_iterator
import hog_graph

class HoGParser:
    """Converter from original HoG data to Lean code."""

    def __init__(self, settings):
        self._s = settings
        self._hog_iterator = iter(hog_iterator.HoGIterator(settings['inputs'], settings['limit'], hog_graph.HoGGraph.last_line_start))
        self._lht = lht.Lean_HoG_Template(self._s)
        self._part = 0

    def _ensure_output_directory(self):
        """Create the output directory if it does not exist yet."""
        d = self._s['output_path']
        if not os.path.exists(d):
            print ("Creating {0}".format(d))
            os.mkdir(d)

    def _output_file_main(self):
        """The name of main Lean data file."""
        return os.path.join(self._s['output_path'], "{0}.lean".format(self._s['db_main']))

    def _output_file_part(self, n):
        """The name of the n-th Lean data file."""
        return os.path.join(self._s['output_path'], "{0}.lean".format(self._lht.lean_module_part(n)))

    # def _get_preadjacency(self, neighborhoods):
    #     # HoG vertices start at 1
    #     def to_int_minus1(x):
    #         return int(x) - 1

    #     def parse_vertex(match):
    #         vertex = to_int_minus1(match.group('vertex'))
    #         # sort and filter the neighbors of vertex
    #         neighbors = sorted(filter(lambda x: vertex < x, map(to_int_minus1, match.group('neighbors').split())))
    #         return list(map(lambda x: (vertex, x), neighbors))

    #     preadjacency = []
    #     count = 0
    #     for m in self._lht.adjacency_pattern.finditer(neighborhoods):
    #         count += 1
    #         preadjacency += parse_vertex(m)
    #     return count, preadjacency

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
                    fh_out.write(self._lht.get_db_preamble())
                graph = hog_graph.HoGGraph(self._lht.graph_name(count), g6, inv, self._s['write_floats'])
                lean_code = graph.graph_to_lean()
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
        print("Converting graphs: {0}  ".format(count), end='\r')
        return count, exhausted_all_graphs

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
            fh_out.write(self._lht.get_main_db(self._part))
        print("Total number of graphs: {0}".format(count))