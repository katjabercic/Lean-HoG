### Configuration

# Folder with original HoG data file (if you do not have it, comment this out)
DATADIR=input-data/raw-hog

# Use this instead if you don't have the real HoG data
# DATADIR=sample-data

# Folder where generated JSON files are placed
JSONDIR=pigpen

# The script that converts HoG data files to Lean files
CONVERT=convert/convert.py

# We compile everything using lake - the lean build system
LAKE=lake

LIMIT=100
SKIP=0

.PHONY: build-lean build-graphs clean-data clean-lean

all: build-graphs build-lean

clean: clean-graphs clean-lean

clean-lean:
	$(LAKE) clean

build-lean:
	$(LAKE) build

build-graphs: clean-graphs
	python3 $(CONVERT) --datadir $(DATADIR) --outdirData $(JSONDIR) --limit $(LIMIT) --skip $(SKIP)

clean-graphs:
	/bin/rm -rf $(LEANDIR)
