# STLC Machine
Implementation of the Simply Typed Lambda Calculus to play with some properties of types, such as inference, checking and inhabitation (theorem proving), as well as evaluating both typed and untyped terms.

### Build

	$ cabal build

## Inference
Type inference for the STLC is fully decidable and uses syntactic unification internally. Of course, not all terms have a type in the theory (starting from all diverging terms).

	$ stlc-machine
	Welcome to STLC Machine!
	> infer λx.λy.x
	 ⊢ λx0.λy0.x0 : a -> b -> a
	> infer λx.λy.λz.(x z)(y z)
	 ⊢ λx0.λy0.λz0.((x0)(z0))((y0)(z0)) : (c -> i -> j) -> (c -> i) -> c -> j
	> infer λx.(x x)
	error: cannot unify

The tool can also infer types for open terms, for which a context telling how to type free variables is provided.

	> infer (x y)
	x0 : b -> c, y0 : b ⊢ (x0)(y0) : c

## Theorem Proving (type inhabitation)
Due to the decidability of the implicational fragment of intuitionistic propositional logic, the tool can output terms that represent proofs of propositions via the Curry-Howard isomorphism.

Propositions that are not intuitionistically valid do not have a corresponding proof term and are therefore rejected.

	$ stlc-machine
	Welcome to STLC Machine!
	> prove a -> b -> a
	λx0.λy0.x0
	> prove (a -> b -> c) -> (a -> b) -> (a -> c)
	λx0.λy0.λz0.((x0)(z0))((y0)(z0))
	> prove ((a -> b) -> a) -> a
	error: not an intuitionistic tautology

## Type checking
Type checking is a relatively trivial task, which corresponds to checking if the provided type corresponds to the one returned by the inference algorithm (up to unification).

	$ stlc-machine
	Welcome to STLC Machine!
	> check λx.λy.x : a -> b -> a
	Ok.
	> check λx.λy.x : d -> d -> d
	Ok.
	> check λx.x : a -> b
	Does not typecheck

## Normalization
The tool can be used to normalize (evaluate) arbitrary λ-terms. The evaluation is performed according to a normal order reduction strategy.

	$ stlc-machine
	> eval (λx.λy.x)(λx.x)(λx.λy.y)(λx.λy.λz.z)(λw.w)
	Result: λx0.λy0.y0
	Reduction steps: 4
	> eval (λx.λy.x)(λx.x)((λx.(x x))(λx.(x x)))
	Result: λx0.x0
	Reduction steps: 2
	> eval (λx.(x x))(λx.(x x))
	wait 'till you get tired...
	^C
