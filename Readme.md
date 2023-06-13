A simple verified compiler, from the (simple typed, call-by-value) lambda calculus to a simple RAM machine

Goals:

- Figure out use for other direction of correctness proofs?
- do reverse of type-saftey for conversions
- Do reverse proofs for typechecking, assembly, machine?
- Modularize code with classes
- Add Parser?
- Add pairs, sums, unit, void, nats, primrec? sructured types?
- Make printing part of the code
- Make initialization part of the code

Refactorings: 

- constr_subst -> full substitution?
- Make contraint functions use list functions?
- Make all definitions abstract outside their file
- rename closure stuff
- Make late stage closures (post bytecode) a single parametric datatype?
- Clean up isabelle - declare x.simps[intros], assumes/shows, patterns in pfs
- Use ints insted of nats for machine code
- Flip environment layout