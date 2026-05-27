# TODO

## Before submission

- [ ] merge implementation and minimize dependencies in liquidhaskell
- [ ] something with SoftwareFoundations.identity_fn_applied_twice, where a subsumption might be necessary
- [ ] fix `getUPackRel` in SoftwareFoundations.identity_fn_applied_twice
- [ ] test automation tactics on fixed translation output
- [ ] figure out why axiomatize_next_term loops (or just takes a long time) in foldrUniversal
- [ ] do not create pack for function arguments that are of unit return type
- [ ] fix position of assertions using proof combinators
- [ ] fix overload of names imported in Rocq (ex: SFBin.Z)
- [X] fix type annotation in andb_commutative

## Possible improvements (non-priorities)

- [ ] create separate inversion lemmas not only based on the patterns of the
      parameters but also of the result. we can also factorize common assumption in
      disjuncts (e.g. in applyLatePolicy)
- [ ] cleanup Rocq grammar

## Extension with higher-order datatypes

- [ ] add support for nested packs in functions and data types, modulo boolean equality instances (and anything that depends on those missing instances)
- [ ] utilize Leibnitz equality whereever possible instead of boolean equality to avoid missing equality instances preventing us from producing inversion lemmas
- [x] add lookup instances for functionhood lemmas (in the presence of higher-order arguments eauto sometimes fails to infer implicit arguments and we need to explicitely apply the functionhood lemma explicitely instantiating the implicit arguments)

## Support for Equations (non-priority)

- [ ] add missing branches to the paths
- [ ] use decidable boolean equality
- [ ] maybe do not translate non recursive function to Equations
