CURRENT_DIR = .
COQBIN ?=
SUF ?=

-include CONFIGURE

COQC = $(COQBIN)coqc$(SUF)
COQDEP = $(COQBIN)coqdep$(SUF)

COQ_FLAG = -R flocq/src Flocq -R SeparationLogic SimpleC.SL -R unifysl Logic -R sets SetsClass -R compcert_lib compcert.lib -R auxlibs AUXLib -R examples SimpleC.EE -R stdlib SimpleC.StdLib -R Common SimpleC.Common -R fixedpoints FP -R MonadLib MonadLib -R listlib ListLib -R MaxMinLib MaxMinLib -R GraphLib GraphLib -R SumLib SumLib -R tracelib TraceLib -R coq-record-update/src RecordUpdate -Q algorithms Algorithms
DEP_FLAG = $(COQ_FLAG)

FILES = $(shell find . -name '*.v' | sed 's|^\./||' | sort)

all: $(FILES:%.v=%.vo)

%.vo: %.v
	@printf "%s\n" "COQC $<"
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$<

.depend: $(FILES)
	@printf '%s ' '$(DEP_FLAG)' > .coqdep.args.tmp
	@printf '%s ' $(FILES) >> .coqdep.args.tmp
	@printf '\n' >> .coqdep.args.tmp
	@$(COQDEP) -f .coqdep.args.tmp > .depend.tmp
	@mv -f .depend.tmp .depend
	@rm -f .coqdep.args.tmp

depend: .depend

clean:
	@find . \( -name '*.vo' -o -name '*.vok' -o -name '*.vos' -o -name '*.glob' -o -name '.*.aux' \) -delete
	@rm -f .depend .depend.tmp .coqdep.args.tmp

.PHONY: all depend clean
.DEFAULT_GOAL := all

ifeq ($(filter clean,$(MAKECMDGOALS)),)
-include .depend
endif
