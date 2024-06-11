import re
from functools import reduce

FILE="./computation-result-gregor.txt"
# FILE="./batch-10.txt"

IDS_START_REGEX = re.compile(r"Doing ids (\d*) to (-?\d*).")
IDS_END_REGEX = re.compile(r"Done ids (\d*) to (-?\d*).")
STATS_REGEX = re.compile(r"Time (\d*):(\d*)\.(\d*) .* Max mem (\d*)")

def get_ids(line):
    start = IDS_START_REGEX.fullmatch(line)
    if start is not None:
        return (int(start.group(1)), int(start.group(2)))

def get_stats(line):
    stats = STATS_REGEX.fullmatch(line)
    if stats is not None:
        time = int(stats.group(1))*6000+int(stats.group(2))*100+int(stats.group(3))
        mem = int(stats.group(4))
        return (time, mem)

class Batch:
    def __init__(self, ids, stats):
        self.start = max(min(ids[0], ids[1]), 0)
        self.end = max(ids[0], ids[1])
        self.time = stats[0]
        self.mem = stats[1]

    def __str__(self):
        return f"{self.start} -> {self.end}: {self.time*10}ms {self.mem}Kb"

    def __add__(self, other):
        start = min(self.start, other.start)
        end = max(self.end, other.end)
        time = self.time + other.time
        mem = (self.mem + other.mem) / 2
        return Batch((start, end), (time, mem))

    def csv(self):
        return f"{self.start},{self.end},{self.time*10},{self.mem}"

def build_list(filename):
    with open(filename) as data:
        batches = []
        start = None
        stats = None
        for line in data:
            line = line.strip()
            res = get_ids(line)
            if res is not None:
                start = res
            else:
                res = get_stats(line)
                if res is not None:
                    stats = res
                else:
                    end = IDS_END_REGEX.fullmatch(line)
                    if end is not None:
                        batches.append(Batch(start, stats))
                        start = None
                        stats = None
        return batches

def analyze(filename):
    batches = build_list(filename)
    total = reduce(lambda x,y : x + y, batches)
    print(total)

def to_csv(filename):
    batches = build_list(filename)
    for batch in batches[::-1]:
        print(batch.csv())

# analyze(FILE)
to_csv(FILE)
