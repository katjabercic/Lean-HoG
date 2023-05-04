### Configuration

# Folder with original HoG data file (if you do not have it, comment this out)
SRCDIR=data/raw-hog

# Use this instead if you don't have the real HoG data
# SRCDIR=sample-data

# Folder where generated JSON files are placed
DESTDIR=pigpen

# The script that converts HoG data files to Lean files
CONVERT=convert/convert.py

# We compile everything using lake - the lean build system
LAKE=lake
LOGLEVEL=30
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
	python3 $(CONVERT) --loglevel $(LOGLEVEL) --srcdir $(SRCDIR) --destdir $(DESTDIR) --limit $(LIMIT) --skip $(SKIP)

clean-graphs:
	/bin/rm -rf $(LEANDIR)
