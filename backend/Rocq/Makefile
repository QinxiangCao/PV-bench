# QCP libraries — build the subset PV-Bench needs.
#
#   make            build everything (use -j6)
#   make depend     regenerate .depend
#   make clean      remove build products
#
# Runs on macOS, Linux and native Windows: no recipe assumes a POSIX shell.
# On native Windows the file operations switch to PowerShell, the same way
# QCP's own Rocq/Makefile does it.

CURRENT_DIR = .
COQBIN ?=
SUF ?=
empty :=
space := $(empty) $(empty)
comma := ,
powershell_list = $(subst $(space),$(comma) ,$(strip $(foreach item,$(1),'$(item)')))

-include CONFIGURE

# Cygwin also exports OS=Windows_NT, but its make is built for *-cygwin and
# expects POSIX recipes. Native/MinGW/MSYS make must use the Windows branch.
USE_WINDOWS_COMMANDS := $(if $(and $(filter Windows_NT,$(OS)),$(if $(findstring cygwin,$(MAKE_HOST)),,yes)),yes)

ifeq ($(USE_WINDOWS_COMMANDS),yes)
SHELL := cmd
print_line = @powershell -NoProfile -Command "[Console]::Out.Write('$(1)' + [char]10)"

define REMOVE_FILES
powershell -NoProfile -Command "Remove-Item -Force -LiteralPath $(call powershell_list,$(1)) -ErrorAction SilentlyContinue; exit 0"
endef

define REMOVE_TREE_OUTPUTS
powershell -NoProfile -Command "Get-ChildItem -Path $(call powershell_list,$(1)) -Recurse -Force -Include *.vo,*.glob,*.vos,*.vok,.*.aux,.lia.cache -ErrorAction SilentlyContinue | Remove-Item -Force -ErrorAction SilentlyContinue; exit 0"
endef

define MOVE_FILE
powershell -NoProfile -Command "Move-Item -Force '$(1)' '$(2)'"
endef

# $(file >) keeps a several-hundred-entry argument list out of cmd.exe, whose
# command line tops out at 8191 characters. GNU make on Windows is 4.x.
define WRITE_LINE
$(file >$(1),$(2))
endef
else
print_line = @printf "%s\n" "$(1)"

define REMOVE_FILES
rm -f $(1)
endef

define REMOVE_TREE_OUTPUTS
find $(1) -type f \( -name '*.vo' -o -name '*.glob' -o -name '*.vos' -o -name '*.vok' -o -name '.*.aux' -o -name '.lia.cache' \) -delete
endef

define MOVE_FILE
mv -f $(1) $(2)
endef

define WRITE_LINE
printf '%s\n' '$(2)' > $(1)
endef
endif

COQC = $(COQBIN)coqc$(SUF)
COQDEP = $(COQBIN)coqdep$(SUF)

COQ_FLAG = -R flocq/src Flocq -R SeparationLogic SimpleC.SL -R unifysl Logic -R sets SetsClass -R compcert_lib compcert.lib -R auxlibs AUXLib -R examples SimpleC.EE -R stdlib SimpleC.StdLib -R Common SimpleC.Common -R fixedpoints FP -R MonadLib MonadLib -R listlib ListLib -R MaxMinLib MaxMinLib -R GraphLib GraphLib -R SumLib SumLib -R tracelib TraceLib -R coq-record-update/src RecordUpdate -Q algorithms Algorithms
DEP_FLAG = $(COQ_FLAG)

# Pure-make recursive wildcard: no `find`, which on Windows would hit
# System32\find.exe. `./` is stripped so the paths match what coqdep emits.
rwildcard = $(foreach d,$(wildcard $(1:=/*)),$(call rwildcard,$d,$2) $(filter $(subst *,%,$2),$d))
FILES := $(patsubst ./%,%,$(sort $(call rwildcard,.,*.v)))

DEPEND      := .depend
COQDEP_ARGS := .coqdep.args.tmp

all: $(FILES:%.v=%.vo)

%.vo: %.v
	$(call print_line,COQC $<)
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$<

# coqdep takes the file list through an args file: the paths do not fit on a
# Windows command line.
$(DEPEND): $(FILES)
	$(call print_line,COQDEP $(words $(FILES)) files)
	@$(call WRITE_LINE,$(COQDEP_ARGS),$(DEP_FLAG) $(FILES))
	@$(COQDEP) -f $(COQDEP_ARGS) > $(DEPEND).tmp
	@$(call MOVE_FILE,$(DEPEND).tmp,$(DEPEND))
	@$(call REMOVE_FILES,$(COQDEP_ARGS))

depend: $(DEPEND)

clean:
	$(call print_line,Cleaning build artifacts...)
	@$(call REMOVE_TREE_OUTPUTS,$(CURRENT_DIR))
	@$(call REMOVE_FILES,$(DEPEND) $(DEPEND).tmp $(COQDEP_ARGS))

.PHONY: all depend clean
.DEFAULT_GOAL := all

ifeq ($(filter clean,$(MAKECMDGOALS)),)
-include $(DEPEND)
endif
