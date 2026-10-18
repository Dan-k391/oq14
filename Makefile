PYTHON ?= python

.PHONY: all verify pdf formal
all: verify pdf
verify:
	$(PYTHON) scripts/verify.py
pdf:
	$(PYTHON) scripts/build.py
formal:
	$(PYTHON) lean/build.py --log-dir output/lean
