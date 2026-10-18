PYTHON ?= python

.PHONY: all verify pdf
all: verify pdf
verify:
	$(PYTHON) scripts/verify.py
pdf:
	$(PYTHON) scripts/build.py
