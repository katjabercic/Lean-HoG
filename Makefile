OUTDIR=src/hog/data
CONVERT=convert/convert.py
LEANPKG=leanpkg
LEAN=lean
DATADIR=data/raw-hog

LIMIT=100
SKIP=0

.PHONY: convert build buildall cleandata

all: convert build

convert: cleandata
	python3 $(CONVERT) --datadir $(DATADIR) --out $(OUTDIR) --limit $(LIMIT) --skip $(SKIP)

build:
	$(LEAN) --make $(OUTDIR)

buildall:
	$(LEANPKG) build
	
test: cleandata
	python3 $(CONVERT) --out $(OUTDIR) --limit 100 --skip $(SKIP) --datadir "sample_data"
	$(LEAN) --make $(OUTDIR)

cleandata:
	/bin/rm -rf $(OUTDIR)
