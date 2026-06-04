# TODO

## Before submission

### Core to λr:
- [ ] merge implementation and minimize dependencies in liquidhaskell

### λr to Rocq:
- [ ] fix position of assertions using proof combinators
- [ ] bind arguments to function calls in hints if they appear in the type of subsequent hints, possibly bind other recurring subterms as well
- [ ] fix [missing brackets](https://github.com/lava-liquid-to-rocq/liquidhaskell/blob/e161493afe617ed8e9ca5bd4cb10e0972b9cb795/lava/out/Benchmark/PeanoNats.v#L1330-L1331) in printer
- [X] fix printing of recurring branch delimiters -, +, *, ...
- [X] fix overload of names imported in Rocq (ex: SFBin.Z)
- [X] fix type annotation in andb_commutative
- [X] fix `getUPackRel` in SoftwareFoundations.identity_fn_applied_twice
- [X] do not create pack for function arguments that are of unit return type
- [X] something with SoftwareFoundations.identity_fn_applied_twice, where a subsumption might be necessary

### Rocq:
- [ ] test automation tactics on fixed translation output
- [ ] figure out why axiomatize_next_term loops (or just takes a long time) in foldrUniversal

## Possible improvements (non-priorities)

- [ ] create separate inversion lemmas not only based on the patterns of the
      parameters but also of the result. we can also factorize common assumption in
      disjuncts (e.g. in applyLatePolicy)
- [ ] cleanup Rocq grammar
- [ ] bind opaque subsumption witnesses of hints before translating the hints themselves for simpler proof states and reduced memory-load (using the letSubCast tactic)
- [ ] ensure let bound subterms and hints are declared one at a time (one binding per tactic, using refine (let : ... := ... in _) for typed hints (or assert if Prop-sorted) or pose proof for untyped ones)
- [ ] assert injection and subsumption witnesses of hints before translating the hints, resulting in easier to read proof states and avoiding proving subgoals twice
- [ ] simplify subsumptionCasts of existentials

## Extension with higher-order datatypes

- [ ] add support for nested packs in functions and data types, modulo boolean equality instances (and anything that depends on those missing instances)
- [ ] utilize Leibnitz equality whereever possible instead of boolean equality to avoid missing equality instances preventing us from producing inversion lemmas
- [x] add lookup instances for functionhood lemmas (in the presence of higher-order arguments eauto sometimes fails to infer implicit arguments and we need to explicitely apply the functionhood lemma explicitely instantiating the implicit arguments)

## Support for Equations (non-priority)

- [ ] add missing branches to the paths
- [ ] use decidable boolean equality
- [ ] maybe do not translate non recursive function to Equations
