OUTDIR=src/hog/data
CONVERT=convert/convert.py
LEANPKG=leanpkg

LIMIT=100
SKIP=0

.PHONY: convert build cleandata

all: convert build

convert: cleandata
	python3 $(CONVERT) --out $(OUTDIR) --skip $(SKIP) --limit $(LIMIT)

src/hog/data: convert

build:
	$(LEANPKG) build

cleandata:
	/bin/rm -rf $(OUTDIR)
