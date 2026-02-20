# This script assumes the paper and implementation repos to be up to date and placed in the same parent folder

#! /usr/bin/bash


# rm -rf ICFP2026 && mkdir ICFP2026
#cd ICFP2026
#cp ../../Paper/*.tex .
#cp ../../Paper/*.cls .
#cp ../../Paper/*.bst .
#cp ../../Paper/*.bib .
#cp ../../Paper/*.bbl .
#latexmk -f paper.tex
#cd ..

rm -rf lava/out
rm -f lava/coqDeps/*.vo*
rm -f lava/coqDeps/*.aux*
rm -rf lava/.CoqMakefile.d lava/CoqMakefile.conf

zip -r artifact.zip supplementary.pdf cabal.project Setup.hs liquidhaskell.cabal Makefile README.md stack.yaml stack.yaml.lock lava liquid-finfield liquid-fixpoint liquidhaskell-boot liquid-parallel liquid-prelude liquid-vector resources scripts src tests typeclass-tests benchmark-timings
