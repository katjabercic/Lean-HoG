### Configuration

# Folder with original HoG data file (if you do not have it, comment this out)
DATADIR=data/raw-hog

# Use this instead if you don't have the real HoG data
# DATADIR=sample-data

# Folder where generated Lean files are placed
LEANDIR=src/hog/data/Data

# The script that converts HoG data files to Lean files
CONVERT=convert/convert.py

# We compile everything using lake - the lean build system
LAKE=lake

LIMIT=100
SKIP=0

.PHONY: convert-data build-lean build-graphs clean-data clean-lean

all: convert build

clean-lean:
	$(LAKE) clean

build-lean:
	$(LAKE) build
	echo "(If you want to compile the graphs, use this instead: make build-graphs)"

convert-data: clean-graphs
	python3 $(CONVERT) --datadir $(DATADIR) --out $(LEANDIR) --limit $(LIMIT) --skip $(SKIP)

build-graphs:
	for g in $(LEANDIR)/hog*.lean ; do \
	  echo "Compiling $$g." ; \
          $(LAKE) build Data.`basename "$$g" .lean` ; \
        done

clean-graphs:
	/bin/rm -rf $(LEANDIR)
