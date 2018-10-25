ALL_VFILES := $(shell find -L 'src' 'vendor' -name "*.v")
ALL_TEST_VFILES := $(shell find -L 'src' 'vendor' -name "*Tests.v")
TEST_VFILES := $(shell find -L 'src' -name "*Tests.v")
VFILES := $(filter-out $(ALL_TEST_VFILES),$(ALL_VFILES))

default: $(VFILES:.v=.vo)

test: $(TEST_VFILES:.v=.vo) $(VFILES:.v=vo)


_CoqProject: libname $(wildcard vendor/*/)
	@echo "-R src $$(cat libname)" > $@
	@for libdir in $(wildcard vendor/*/); do \
		echo "-R $$libdir/src $$(cat $$libdir/libname)" >> $@; \
	done
	@echo "_CoqProject:"
	@cat $@

.coqdeps.d: $(ALL_VFILES) _CoqProject
	coqdep -f _CoqProject $(ALL_VFILES) > $@

-include .coqdeps.d

%.vo: %.v .coqdeps.d _CoqProject
	@echo "COQC $<"
	@coqc $(shell cat '_CoqProject') $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	@rm -f $(ALL_VFILES:.v=.vo) $(ALL_VFILES:.v=.glob) .coqdeps.d _CoqProject
	@find . -name ".*.aux" -exec rm {} \;

.PHONY: default test clean
