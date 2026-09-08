# PV-Bench — build the Coq files of every problem.
#
#   make            build every .v file in $(CORPORA) (use -j for parallelism)
#   make <file>.vo  build one file
#   make clean      remove .vo/.glob/... but keep the generated makefile
#   make distclean  also remove the generated makefile
#
# The real work is done by a coq_makefile-generated Makefile.coq, which gets the
# library mappings from _CoqProject and the file list from this makefile.
#
# _CoqProject holds an absolute path to your QCP checkout, so it is machine-local:
# it is generated from _CoqProject.example using QCP_ROCQ, which you set once in a
# local `CONFIGURE` file (copy CONFIGURE.example). Both are gitignored.

CONFIGURE := CONFIGURE
-include $(CONFIGURE)

COQ_MAKEFILE := coq_makefile
COQPROJECT   := _CoqProject
COQMK        := Makefile.coq
VSTAMP       := .vfiles.stamp

# What gets built. Rocq files live in <entry>/rocq/ or a project-family rocq/
# shared by several entries; coqdep works out their dependency order.
# Only the populated Codeforces shards are listed -- add a number to SHARDS to
# bring another one in. The other shard directories hold a handful of entries
# that are not part of the build.
SHARDS  := 00 01
CORPORA := $(addprefix Codeforces/examples_shard,$(SHARDS)) Algorithms Data_structures Engineering
VFILES := $(shell find $(CORPORA) -name '*.v' | sort)

.PHONY: all clean distclean force

all: $(COQMK)
	@$(MAKE) --no-print-directory -f $(COQMK)

# Build a single file: make Codeforces/examples_shard01/P001_.../rocq/spec_lib.vo
%.vo: $(COQMK)
	@$(MAKE) --no-print-directory -f $(COQMK) $@

$(COQMK): $(COQPROJECT) $(VSTAMP)
	@$(COQ_MAKEFILE) -f $(COQPROJECT) $(VFILES) -o $(COQMK) 2>/dev/null
	@echo "wrote $(COQMK) ($(words $(VFILES)) .v files)"

# Regenerate Makefile.coq only when the *set* of .v files changes, not on every edit.
$(VSTAMP): force
	@printf '%s\n' $(VFILES) > $@.tmp
	@cmp -s $@.tmp $@ || mv $@.tmp $@
	@rm -f $@.tmp

$(COQPROJECT): $(COQPROJECT).example $(wildcard $(CONFIGURE))
ifeq ($(strip $(QCP_ROCQ)),)
	@echo "QCP_ROCQ is not set. Create your local $(CONFIGURE):"
	@echo "    cp $(CONFIGURE).example $(CONFIGURE)   # then put your QCP path in it"
	@exit 1
else
	@test -d "$(QCP_ROCQ)/SeparationLogic" || \
	  { echo "no SeparationLogic/ in $(QCP_ROCQ) — is that a QCP Rocq/ directory?"; exit 1; }
	@sed -e '/^#/d' -e 's#@QCP_ROCQ@#$(QCP_ROCQ)#g' $(COQPROJECT).example > $@
	@echo "wrote $@ with QCP_ROCQ=$(QCP_ROCQ)"
endif

clean:
	@if [ -f $(COQMK) ]; then $(MAKE) --no-print-directory -f $(COQMK) clean; fi

distclean: clean
	rm -f $(COQMK) $(COQMK).conf .$(COQMK).d $(VSTAMP)
