OUTDIR=src/hog/data/Data
CONVERT=convert/convert.py
LEANPKG=leanpkg
LEAN=lean
LAKE=lake
BASE_MODULE=Data

LIMIT=100
SKIP=0

.PHONY: convert build buildall cleandata

all: convert build

%.olean: %.lean
	$(LAKE) build $(BASE_MODULE).$(notdir $(basename $<)) -v

clean:
	$(LAKE) clean

convert: cleandata
	python3 $(CONVERT) --out $(OUTDIR) --limit $(LIMIT) --skip $(SKIP)

build: $(OUTDIR)/*.olean

buildall:
	$(LEANPKG) build
	
test: cleandata
	python3 $(CONVERT) --out $(OUTDIR) --limit 100 --skip $(SKIP) --datadir "sample_data"
	$(LEAN) --make $(OUTDIR)

cleandata:
	/bin/rm -rf $(OUTDIR)
