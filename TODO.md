# TODO

- [ ] merge implementation and minimize dependencies in liquidhaskell
- [ ] something with SoftwareFoundations.identity_fn_applied_twice, where a subsumption might be necessary
- [ ] fix `getPackRel` being used on upacks instead of the correct `getUPackRel`
- [ ] merge inversion lemmas that can have the same result
- [ ] test automation tactics on fixed translation output

# TODO for extension with higher-order datatypes

- [ ] add support for nested packs in functions and data types, modulo boolean equality instances (and anything that depends on those missing instances)
- [ ] utilize Leibnitz equality whereever possible instead of boolean equality to avoid missing equality instances preventing us from producing inversion lemmas
- [x] add lookup instances for functionhood lemmas (in the presence of higher-order arguments eauto sometimes fails to infer implicit arguments and we need to explicitely apply the functionhood lemma explicitely instantiating the implicit arguments)

## Inversion lemmas

So we want to unify branches returning ?rel t_1 ... t_n res iff the t_i and res can all overlap. So if the t_i or res are results of applying different constructors, we don't need to merge the branches but otherwise we do.
Then, we need to find necessary and sufficient conditions for each possible shape of results of the relation to be attained.
So overall we improve upon the inversion tactic by generating existentials for required intermediate values corresponding to variables in the branches,
merging branches that can overlap and producing conjuncts corresponding to the different branches.
On top of that we also generate the (common) conditions for the branches to produce the expected output (just like inversion does).
This means that applying an inversion lemma is always a reasonable thing to do whenever possible (and usually helpful when possible), whereas inversion may just result in additional branches without helping at all.
This used to be implemented in some probably needlessly complicated algorithm that first generated unification variables for the largest subterms that aren't constructor applications along with the required substitutions for those unification variables in each branch (subterms that appear repeatedly get several unification variables). Then it compared the branches result relation application with the unification variables. Two branches need to be merged iff those coincide. Then the required substitutions are used to work out the necessary and sufficient condition corresponding to those merged branches.
