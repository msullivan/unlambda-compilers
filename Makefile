all: unlambda-smlnj unlambda

unlambda: *.sml *.sig *.grm *.lex unlambda.mlb Makefile
	mlton unlambda.mlb


PLATFORM=x86-linux

define SMLNJ_BUILD_SCRIPT
CM.make "sources.cm";
SMLofNJ.exportFn ("unlambda.heap", Main.main);
endef
export SMLNJ_BUILD_SCRIPT

define SMLNJ_RUN_SCRIPT
#!/bin/sh
sml "@SMLcmdname=$$0" @SMLload=unlambda.heap.$(PLATFORM) "$$@"
endef
export SMLNJ_RUN_SCRIPT


unlambda.heap.$(PLATFORM): *.sml *.sig *.grm *.lex sources.cm Makefile
	echo "$$SMLNJ_BUILD_SCRIPT" | sml

unlambda-smlnj: unlambda.heap.$(PLATFORM)
	echo "$$SMLNJ_RUN_SCRIPT" > unlambda-smlnj
	chmod +x unlambda-smlnj
