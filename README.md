# liquidhaskell
This repository is a fork of the liquidhaskell repository extending liquidhaskell with the lava tool.

Note that the original liquid haskell code is required to build lava and retains its existing copyrights.

## Building the tool
The tool can be build by running
```
cabal build
```

## Lava benchmarks and tests
The benchmarks and tests for the lava tool can be found at [Benchmark](tests/lava/Benchmark). 
They can be translated by the lava tool by running
```
make translation
```
The translated files will be placed in the [out](lava/out) folder.

## Checking translated benchmarks
To run Rocq on the translated benchmarks run
```
make rocq
```

## Supplementary pdf
The file supplementary.pdf contains the paper introducing the lava tool as submitted to ICFP 2026 along with its appendices.
