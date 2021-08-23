class HoGIterator:

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
        if self._counter > self._limit:
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
        return graph, self._fh_g6.readline()