# Status of the examples

## Directories

Everything in Benchmark gets translated and verified.

Everything in TranslationTest gets translated, but does not verify.
Maybe we could do something where all proofs are replaced by assumed to check
that everything typechecks and is syntactically correct.

Todo contains files that should translate but currently do not.

PLE are additional files from the PLE benchmark, some could be adapted.

## Current situation

Everything in Benchmark is translated. It should be verified automatically.

Everything in TranslationTest is translated. Not sure if the transaltion of ApplicativeList is correct.

Todo.Lambdas translates but incorrectly, we need to make the translation of λs clear.

In PLE, nothing translates.
