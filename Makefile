OUTDIR=src/hog/data
CONVERT=convert/convert.py
LEAN=lean

.PHONY: convert compile

default: convert compile

convert:
	python3 $(CONVERT)

compile: convert
	$(LEAN) --make db_test_main.lean
