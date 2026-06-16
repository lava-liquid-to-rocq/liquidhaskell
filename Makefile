THREADS=1
SMTSOLVER=z3

FASTOPTS=-O0
DISTOPTS=-O2
PROFOPTS=-O2 --enable-library-profiling --enable-executable-profiling
LIQUIDOPTS=

CABAL=cabal
CABALI=$(CABAL) install
CABALP=$(CABAL) install --enable-library-profiling

EXT := *.vo *.vok *.vos *.glob *.aux *.v.timing
GHCO := *.o *.hi *.dyn_o *.dyn_hi

# to deal with cabal sandboxes using dist/dist-sandbox-xxxxxx/build/test/test
# TASTY=find dist -type f -name test | head -n1
TASTY=./dist/build/test/test

DEPS=--dependencies-only

ghcid: 
	stack exec -- ghcid --command="stack ghci --ghci-options=-fno-code"


##############################################################################
##############################################################################
##############################################################################

fast:
	$(CABAL) install -fdevel $(FASTOPTS)

first:
	$(CABAL) install $(FASTOPTS) --only-dependencies --enable-tests --enable-benchmarks

dist:
	# $(CABAL) install $(DISTOPTS)
	$(CABAL) configure -fdevel --enable-tests --disable-library-profiling -O2
	$(CABAL) build
	
prof:
	$(CABAL) install $(PROFOPTS)

igotgoto:
	$(CABAL) build $(OPTS)
	cp dist/build/liquid/liquid ~/.cabal/bin/

clean:
	cabal clean

docs:
	$(CABAL) hscolour
	$(CABAL) haddock --hoogle

deps:
	$(CABALI) $(DEPS)

pdeps:
	$(CABALP) $(DEPS)

all-test-py:
	cd tests && ./regrtest.py -a -t $(THREADS) && cd ../

test-py:
	cd tests && ./regrtest.py -t $(THREADS) && cd ../

test:
	$(CABAL) configure -fdevel --enable-tests --disable-library-profiling -O2
	$(CABAL) build
	$(CABAL) exec $(TASTY) -- --smtsolver $(SMTSOLVER) --hide-successes --rerun-update -p 'Unit/' -j$(THREADS) +RTS -N$(THREADS) -RTS
	# $(CABAL) exec $(TASTY) -- --smtsolver $(SMTSOLVER) --liquid-opts='$(LIQUIDOPTS)' --hide-successes --rerun-update -p 'Unit/' -j$(THREADS) +RTS -N$(THREADS) -RTS

test710:
	$(CABAL) configure -fdevel --enable-tests --disable-library-profiling -O2
	$(CABAL) build
	$(TASTY) --smtsolver $(SMTSOLVER) --hide-successes --rerun-update -p 'Unit/' -j$(THREADS) +RTS -N$(THREADS) -RTS


retest:
	cabal configure -fdevel --enable-tests --disable-library-profiling -O2
	cabal build
	cabal exec $(TASTY) -- --smtsolver $(SMTSOLVER) --hide-successes --rerun-filter "exceptions,failures,new" --rerun-update -p 'Unit/' -j$(THREADS) +RTS -N$(THREADS) -RTS

all-test:
	cabal configure -fdevel --enable-tests --disable-library-profiling -O2
	cabal build
	cabal exec $(TASTY) -- --smtsolver $(SMTSOLVER) --hide-successes --rerun-update -j$(THREADS) +RTS -N$(THREADS) -RTS

all-test-710:
	cabal configure -fdevel --enable-tests --disable-library-profiling -O2
	cabal build
	$(TASTY) --smtsolver $(SMTSOLVER) --hide-successes --rerun-update -j$(THREADS) +RTS -N$(THREADS) -RTS



all-retest:
	cabal configure -fdevel --enable-tests --disable-library-profiling -O2
	cabal build
	cabal exec $(TASTY) -- --smtsolver $(SMTSOLVER) --hide-successes --rerun-filter "exceptions,failures,new" --rerun-update -j$(THREADS) +RTS -N$(THREADS) -RTS

all-retest-710:
	cabal configure -fdevel --enable-tests --disable-library-profiling -O2
	cabal build
	$(TASTY) --smtsolver $(SMTSOLVER) --hide-successes --rerun-filter "exceptions,failures,new" --rerun-update -j$(THREADS) +RTS -N$(THREADS) -RTS



lint:
	hlint --colour --report .

tags:
	hasktags -x -c src/
	# hasktags -c src/
	# hasktags -e src/

timeTranslation: 
	$(MAKE) cleanTrans
	# time stack exec --rts-options -t -- ghc tests/lava/Benchmark/FoldrUniversal.hs
	time cabal exec -- ghc -fplugin=LiquidHaskell tests/lava/Benchmark/Overview.hs
	time stack exec --rts-options -t -- ghc tests/lava/Benchmark/PeanoNats.hs
	time stack exec --rts-options -t -- ghc tests/lava/Benchmark/SoftwareFoundations.hs
	time stack exec --rts-options -t -- ghc tests/lava/Benchmark/RBinsToBins.hs
	time stack exec --rts-options -t -- ghc tests/lava/Benchmark/PLE/MonadId.hs
	time stack exec --rts-options -t -- ghc tests/lava/Benchmark/PLE/MonadMaybe.hs
	time stack exec --rts-options -t -- ghc tests/lava/Benchmark/PLE/MonoidList.hs
	time stack exec --rts-options -t -- ghc tests/lava/Benchmark/PLE/MonoidMaybe.hs
	time stack exec --rts-options -t -- ghc tests/lava/Benchmark/PLE/Lists.hs
	time stack exec --rts-options -t -- ghc tests/lava/Benchmark/PLE/Compose.hs
	time stack exec --rts-options -t -- ghc tests/lava/TranslationTests/Append.hs
	time stack exec --rts-options -t -- ghc tests/lava/TranslationTests/ApplicativeId.hs
	time stack exec --rts-options -t -- ghc tests/lava/TranslationTests/ApplicativeMaybe.hs
	time stack exec --rts-options -t -- ghc tests/lava/TranslationTests/FoldrUniversal.hs
	time stack exec --rts-options -t -- ghc tests/lava/TranslationTests/FunctorId.hs
	time stack exec --rts-options -t -- ghc tests/lava/TranslationTests/FunctorList.hs
	time stack exec --rts-options -t -- ghc tests/lava/TranslationTests/FunctorMaybe.hs
	time stack exec --rts-options -t -- ghc tests/lava/TranslationTests/MonadList.hs

translation: 
	clear && time cabal run tests:benchmark-refcore; cd lava; cabal build; ./run-benchmarks.sh; echo "Translation finished!"

cleanLava:
	cd dist-newstyle/build/x86_64-linux/ghc-9.12.2/liquidhaskell-boot-0.9.12.2.1/opt/build/Language/Haskell/Liquid/Lava && rm $(GHCO) || echo ""
	cd dist-newstyle/build/x86_64-linux/ghc-9.12.2/lava-0.9.12.2.1/opt/build/Lava && rm $(GHCO) || echo ""

cleanTrans: 
	for i in $(EXT); do find tests/lava -name "$$i" -delete; done

CoqMakefile: Makefile lava/_CoqProject
	cd lava && $(COQBIN)coq_makefile TIMED = 1 TIMING = 1 -f _CoqProject -o CoqMakefile # since the profiler is not working correctly we can't use it here: -arg -profile-ltac

rocq: CoqMakefile
	cd lava && $(MAKE) clean && $(MAKE) pretty-timed --no-print-directory -f CoqMakefile && cp time-of-build-pretty.log "verificationTime/time-of-build-pretty-$(date -Iseconds).log"
	
lava: translation rocq
	echo "Lava ran sucessfully on all benchmarks."
