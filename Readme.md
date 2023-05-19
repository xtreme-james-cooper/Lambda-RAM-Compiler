A simple verified compiler, from the (simple typed, call-by-value) lambda calculus to a simple RAM machine

Goals:

- Figure out use for other direction of correctness proofs?
- do reverse of type-saftey for conversions
- Do reverse proofs for typechecking, assembly, machine?
- Modularize code with classes
- Remove runtime tags
- Add Parser?
- Add pairs, sums, unit, void, nats, primrec? sructured types?
- Make printing part of the code
- Make initialization part of the code

Refactorings: 

- constr_subst -> full substitution?
- Make contraint functions use list functions?
- Make all definitions abstract outside their file
- rename closure stuff