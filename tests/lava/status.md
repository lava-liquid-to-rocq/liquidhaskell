# Status of the examples

## Directories

Everything in Benchmark gets translated and verified.

Everything in TranslationTest gets translated, but does not verify.

Todo contains files that should translate but currently do not.

PLE are additional files from the PLE benchmark, some could be adapted.

## Current situation

Everything in Benchmark is translated. It should be verified automatically.

TranslationTest.ApplicativeList is not translated:
—— Type synthesis  failed with error: Variable or constructor "compose" not bound in context with a simple refinement type. ——

Todo.Lambdas translates but incorrectly, we need to make the translation of λs clear.

In PLE, nothing translates.
