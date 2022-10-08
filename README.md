# A core calculus for temporal resources

A (work in progress) Agda formalisation of a (Fitch-type)
modally-typed, effectful **core calculus for safe and correct
programming with temporal resources**, i.e., resources that become
available only after some amount of time after being brought into
scope, e.g., when on a production line the assembly operation needs
to wait for (car) parts to dry after the paint operation.

The main aspects of this calculus are:

* Fitch-style, *temporally-graded modal types* `[ tau ] X` are used to
  capture temporal resources, expressing that an `X`-value will be
  available in at most `tau` time steps, after which it becomes
  possible to unbox it.
* A novel notion of *temporally-aware algebraic effects*, where
  operations' specifications include their execution times, and
  their continuations know that an operation's worth of additional
  time has passed before they start executing, making it possible to
  safely access further temporal resources in it.
* *Effect handlers*, also temporally-aware, that have to respect the
  temporal discipline of algebraic operations.
* A *graded monads-based effect system* (with some added temporal
  awareness) that modularly tracks the execution times of
  computations.

The formalisation consists of three main parts:

## Core calculus, type system, equations, basic meta-theory

The main modules presenting the core calculus are:

* `Syntax/Types.agda` defines types
* `Syntax/Contexts.agda` defines contexts and operations on them
* `Syntax/Language.agda` defines well-typed values and computations
* `Syntax/Renamings.agda` defines an inductive notion of renamings and
  its action on well-typed terms (i.e., proves admissibility of
  renaming)
* `Syntax/Substitutions.agda` defines/proves substitution for
  well-typed terms
* `Syntax/EquationalTheory.agda` defines a natural beta/eta-equational
  theory for well-typed terms

## Abstract category-theoretic denotational semantics 

The abstract model is summarised in `Semantics/Model.agda`. The main
modules presenting this model are:

* `Semantics/Model/Category.agda` axiomatises the basic abstract
  category-theoretic structures used in the interpretation (e.g.,
  products, exponentials, etc)
* `Semantics/Model/Modality/Future.agda` axiomatises the (future)
  modality used to model the modal temporal resource type `[ tau ] X`, 
  as a (covariant) strong monoidal functor
* `Semantics/Model/Modality/Past.agda` axiomatises the (past) 
  modality used to model the Fitch-style temporal modality on contexts, 
  as a (contravariant) strong monoidal functor
* `Semantics/Model/Modality/Adjunction.agda` axiomatises an adjunction
  between the two modalities used in the interpretation of computation
  terms (boxing, unboxing, but also sequential composition, etc)
* `Semantics/Model/Monad.agda` axiomatises strong graded monad structure
  used to model computation types and terms
  
This abstract model is then used to give the core calculus a denotational
semantics and prove it sound, in the following modules:

* `Semantics/Interpretation.agda` defines the interpretation of types, 
  contexts, and terms
* `Semantics/Renamings.agda` defines the interpretation of renamings
* `Semantics/Renamings/Properties/VC-rename.agda` proves a semantic
  renaming lemma
* `Semantics/Substitutions/Properties/VC-subst.agda` proves a semantic
  substitution lemma
* `Semantics/Soundness.agda` proves the soundness of the interpretation

## Concrete presheaf model

We provide a natural concrete example of the abstract setup using
time-indexed presheaves in `Semantics/Model/Example/TSets/`. The 
structure of this model follows the modules of the abstract setup.

## The work in progress aspect

Not all the desired results are currently written up in Agda, for
three main reasons: paper submission deadline; running into Agda's bug
where due to excessive eta-contraction `with` abstractions end up
producing ill-typed Agda terms
([#2732](https://github.com/agda/agda/issues/2732)); and the (naive,
straightforward attempt at the) concrete presheaf model producing
humongous inequational Agda terms in composite equations/diagrams.

What we currently have:

* In `Syntax/`, all the desired definitions and proofs are finished
* In `Semantics/`, the interpretation is defined, and the high-level
  arguments for renaming and substitution lemmas, and the soundness
  theorem are finished.
* In `Semantics/Model/Example/TSets/`, the presheaf category, with the
  modalities and graded monad on it, with all properties of modalities
  written up and most of the graded-monadic properties written up.

What we currently do not have:

* In `Semantics/`, some of the auxiliary lemmas used in the high-level
  proofs are currently partially finished (bugs) or postulated (time), 
  specifically:
  
  * `Semantics/Renamings/Properties/env-⟨⟩-ᶜ-ren-naturality.agda` runs
    into the problem with `with` abstractions producing ill-typed
    Agda-terms
  * `Semantics/Renamings/Properties/env-⟨⟩-ᶜ-split-env-naturality.agda`
    is postulated for time
  * `Semantics/Renamings/Properties/var-not-in-ctx-after-ᶜ-wk-ren.agda`
    runs into the `with` abstraction problem, but has the corresponding
    cases proved manually as separate auxiliary lemmas
    
* Further, in `Semantics/Model/Example/TSets/Monad/`, termination of
  some functions is postulated where Agda does not immediately see it.
  
  The reason for this is that the monad is defined simultaneously with
  its monotonicity proof, meaning that when defining operations such
  as monad multiplication, the types involved in these definitions
  have recursive calls of the form `μˢ (Tˢ-≤t p k)`, where Agda does
  not see that `Tˢ-≤t p k` is indeed smaller than the original
  argument to `μˢ` (with `k` one of its subterms) because `Tˢ-≤t` does
  not change the given tree height.
    
* In `Semantics/Model/Example/TSets/`, some of them modules typecheck
  extremely slowly due to the current definition of the presheaf model
  and the structure on it producing humongous inequational Agda terms
  in composite equations/diagrams, specifically:
  
  * `Semantics/Model/Example/TSets/Monad/Strength/Properties/CartesianStructure.agda`
    typechecks very slowly, with `--experimental-lossy-unification`
    option helping Agda to be a bit faster
  * `Semantics/Model/Example/TSets/Monad/Strength/Properties/Algebraicity.agda`
    postulates the algebraicity law for algebraic operations due to
    typechecking slowness (the corresponding proof for the unary delay
    operations is written up)
  * `Semantics/Model/Example/TSets/Monad/Handling/Properties/` is
    missing the write-up of the proof of the handling-of-operation law
    due to typechecking slowness (even for writing the law down with
    the current concrete model definition)
    
What and how could be improved:

* For the `with` abstraction problem, the official suggestion seems to
  be to rewrite the definition with pattern-matching in auxiliary
  functions as opposed to using with-abstractions. As a stop-gap
  measure, we could also work out the types of the individual cases
  and prove them as auxiliary lemmas (analogously to
  `Semantics/Renamings/Properties/var-not-in-ctx-after-ᶜ-wk-ren.agda`)
* For the slowness of typechecking, we likely need to make some
  aspects of the concrete model abstract, and manually simplify the
  generated inequational proof terms in composite equations/diagrams.
* Regarding the postulated termination of some of the functions in
  `Semantics/Model/Example/TSets/Monad/`, we could additionally index
  the monad's data structure with its tree-height, which should be
  enough to convince Agda of termination.
