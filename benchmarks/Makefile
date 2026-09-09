# PV-Bench — build the Rocq files of every problem.
#
#   make            build everything (use -j6; never a bare -j)
#   make <file>.vo  build one file
#   make depend     regenerate .depend
#   make _CoqProject  write the file your editor reads
#   make clean      remove build products and .depend
#
# Runs on macOS, Linux and native Windows. The recipes never assume a POSIX
# shell: on native Windows they switch to PowerShell, following the same
# structure as QCP's own Rocq/Makefile.
#
# QCP's libraries live outside this repository and their location differs per
# machine, so set QCP_ROCQ once in a local CONFIGURE file (copy
# CONFIGURE.example). CONFIGURE and the generated _CoqProject are gitignored.

CURRENT_DIR = .
COQBIN ?=
SUF ?=
empty :=
space := $(empty) $(empty)
comma := ,
powershell_list = $(subst $(space),$(comma) ,$(strip $(foreach item,$(1),'$(item)')))

CONFIGURE := CONFIGURE
-include $(CONFIGURE)

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

# $(file >) keeps a 1500-line argument list out of cmd.exe, whose command line
# tops out at 8191 characters. GNU make on Windows is 4.x, which has it.
define WRITE_LINES
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

define WRITE_LINES
printf '%s\n' '$(2)' > $(1)
endef
endif

COQC   = $(COQBIN)coqc$(SUF)
COQDEP = $(COQBIN)coqdep$(SUF)

# The library mappings, in one place. `make _CoqProject` writes the same list
# out for your editor; nothing here parses that file back.
QCP_LIBS_R = \
  sets:SetsClass unifysl:Logic compcert_lib:compcert.lib auxlibs:AUXLib \
  flocq/src:Flocq coq-record-update/src:RecordUpdate fixedpoints:FP \
  MonadLib:MonadLib tracelib:TraceLib listlib:ListLib MaxMinLib:MaxMinLib \
  GraphLib:GraphLib SumLib:SumLib SeparationLogic:SimpleC.SL \
  Common:SimpleC.Common examples:SimpleC.EE stdlib:SimpleC.StdLib
QCP_LIBS_Q = algorithms:Algorithms

dir_of  = $(word 1,$(subst :, ,$(1)))
name_of = $(word 2,$(subst :, ,$(1)))
COQ_MAPPINGS = \
  $(foreach l,$(QCP_LIBS_R),-R $(QCP_ROCQ)/$(call dir_of,$l) $(call name_of,$l)) \
  $(foreach l,$(QCP_LIBS_Q),-Q $(QCP_ROCQ)/$(call dir_of,$l) $(call name_of,$l)) \
  -R . PVbench
COQ_FLAG = $(COQ_MAPPINGS)
DEP_FLAG = $(COQ_MAPPINGS)

# What gets built. Rocq files live in <entry>/rocq/. Only the populated
# Codeforces shards are listed -- add a number to SHARDS to bring another in.
SHARDS  := 00 01
CORPORA := $(addprefix Codeforces/examples_shard,$(SHARDS)) Algorithms Data_structures Engineering

# Pure-make recursive wildcard: no `find`, which on Windows would hit
# System32\find.exe, and which errors out on a corpus directory that is absent.
rwildcard = $(foreach d,$(wildcard $(1:=/*)),$(call rwildcard,$d,$2) $(filter $(subst *,%,$2),$d))
VFILES := $(sort $(call rwildcard,$(CORPORA),*.v))
VOFILES := $(VFILES:.v=.vo)

DEPEND      := .depend
COQDEP_ARGS := .coqdep.args.tmp

.PHONY: all depend clean distclean check-config

all: check-config $(VOFILES)

check-config:
ifeq ($(strip $(QCP_ROCQ)),)
	$(call print_line,QCP_ROCQ is not set. Create your local $(CONFIGURE):)
	$(call print_line,    copy $(CONFIGURE).example to $(CONFIGURE)$(comma) then put your QCP path in it)
	@exit 1
endif

# A static pattern rule, so it matches only this repository's files: the
# dependency file also names .vo targets inside the QCP checkout, and those must
# be built there, not here.
$(VOFILES): %.vo: %.v
	$(call print_line,COQC $*.v)
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

# coqdep takes the file list through an args file: 1500 paths do not fit on a
# Windows command line, and passing them one per make invocation is far slower.
depend:
	$(call print_line,COQDEP $(words $(VFILES)) files)
	@$(call WRITE_LINES,$(COQDEP_ARGS),$(DEP_FLAG) $(VFILES))
	@$(COQDEP) -f $(COQDEP_ARGS) > $(DEPEND).tmp
	@$(call MOVE_FILE,$(DEPEND).tmp,$(DEPEND))
	@$(call REMOVE_FILES,$(COQDEP_ARGS))

$(DEPEND): Makefile $(wildcard $(CONFIGURE))
	@$(MAKE) --no-print-directory depend

_CoqProject:
	@$(call WRITE_LINES,$@,$(foreach l,$(QCP_LIBS_R),-R $(QCP_ROCQ)/$(call dir_of,$l) $(call name_of,$l)) $(foreach l,$(QCP_LIBS_Q),-Q $(QCP_ROCQ)/$(call dir_of,$l) $(call name_of,$l)) -R . PVbench)
	$(call print_line,wrote $@ with QCP_ROCQ=$(QCP_ROCQ))

clean:
	$(call print_line,Cleaning build artifacts...)
	@$(call REMOVE_TREE_OUTPUTS,$(CORPORA))
	@$(call REMOVE_FILES,$(DEPEND) $(DEPEND).tmp $(COQDEP_ARGS))

distclean: clean
	@$(call REMOVE_FILES,_CoqProject)

ifeq ($(filter depend clean distclean _CoqProject,$(MAKECMDGOALS)),)
-include $(DEPEND)
endif
