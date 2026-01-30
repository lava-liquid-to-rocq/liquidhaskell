# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile
# KNOWNFILES will not get implicit targets from the final rule, and so depending on them won’t invoke the submake
# Warning: These files get declared as PHONY, so any targets depending on them always get rebuilt
KNOWNFILES := Makefile _CoqProject

.DEFAULT_GOAL := rocq

CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile TIMED = 1 TIMING = 1 -f _CoqProject -o CoqMakefile # since the profiler is not working correctly we can't use it here: -arg -profile-ltac

rocq: CoqMakefile
	$(MAKE) clean
	$(MAKE) pretty-timed --no-print-directory -f CoqMakefile
	cp -f time-of-build-pretty.log out/time-of-build-pretty.log

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))
	
.PHONY: invoke-coqmakefile $(KNOWNFILES)

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
