OUTDIR=src/hog/data
CONVERT=convert/convert.py
LEANPKG=leanpkg

LIMIT=0

.PHONY: convert build

all: convert build

convert:
	python3 $(CONVERT) --out $(OUTDIR) --limit $(LIMIT)

src/hog/data: convert

build:
	$(LEANPKG) build

clean:
	/bin/rm -rf $(OUTDIR)
