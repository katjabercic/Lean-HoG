# Iterates over the given list of files with HoG exports, graph by graph
# Returns the consecutive number of the current graph, the graph6 and the 
# chunk containing graph theoretic invariants

# Needs a string that appears at the beginning of the last line of the 
# invariant chunk to recognise that it has read data on the current graph.

# If the limit is given as n > 0, the iterator stops after n graphs.
# To process all files, limit should be 0.

class HoGIterator:
    """Iterate through the HoG graphs loaded from given input graphs."""

    def __init__(self, inputs, limit, last_line_start):
        if len(inputs) == 0:
            raise StopIteration
        self._inputs = iter(inputs)
        self._limit = limit
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
            file_in, file_g6 = next(self._inputs)
            self._fh_in = open(file_in, 'r')
            self._fh_g6 = open(file_g6, 'r')
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
