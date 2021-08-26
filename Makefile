OUTDIR=src/hog/data
CONVERT=convert/convert.py
LEANPKG=leanpkg

.PHONY: convert build

all: convert build

convert:
	python3 $(CONVERT)

src/hog/data: convert

build: src/hog/data
	$(LEANPKG) build
