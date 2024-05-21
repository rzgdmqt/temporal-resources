# A core language for temporal resources

A (work in progress) Agda formalisation of a (Fitch-type)
modally typed, effectful **core language for safe and correct
programming with temporal resources**, i.e., resources that become
available only after some amount of time after being brought into
scope, e.g., when on a production line the assembly operation needs
to wait for (car) parts to dry after the paint operation.

The **main features** of this core language are:

- Fitch-style, _temporally-graded modal types_ `[ tau ] X` are used to
  capture temporal resources, expressing that an `X`-value will be
  available in at most `tau` time steps, after which it becomes
  possible to unbox it.
- A novel notion of _temporally-aware algebraic effects_, where
  operations' specifications include their execution times, and
  their continuations know that an operation's worth of additional
  time has passed before they start executing, making it possible to
  safely access further temporal resources in it.
- _Effect handlers_, also temporally-aware, that have to respect the
  temporal discipline of algebraic operations.
- A _graded monads-based effect system_ (with some added temporal
  awareness) that modularly tracks the execution times of
  computations.

The formalisation is developed and tested with Agda version 2.6.2.2
and Agda Standard Library version 1.7.1.

The formalisation consists of **three main parts**:

### Core language, type system

The main modules presenting the core language are:

- `Syntax/Types.agda` defines types.

- `Syntax/Contexts.agda` defines contexts and operations on them.

- `Syntax/Language.agda` defines well-typed values and computations.

- `Syntax/Renamings.agda` defines an inductive notion of renamings and
  its action on well-typed terms (i.e., proves admissibility of
  renaming).
- `Syntax/Substitutions.agda` defines/proves substitution for
  well-typed terms.
- `Syntax/EquationalTheory.agda` defines a natural beta/eta-equational
  theory for well-typed terms.

### Operational semantics, progress theorem

- `OperationalSemantics/State.agda` defines state for stateful operational semantics, and proves some state properties.

- `OperationalSemantics/PreservationTheorem.agda` defines steps for stateful operational semantics, and proves preservation theorem.

- `OperationalSemantics/TheoremsAboutSteps.agda` proves some basic theorems about steps.

- `OperationalSemantics/ProgressTheorem.agda` proves progress theorem.

### EquationalTheory

- `EquationalTheory/CompContext.agda` defines binding contexts and programs with typed holes.
- `EquationalTheory/EquationalTheory.agda` defines a natural beta/eta-equational theory for well-typed terms.
- `EquationalTheory/Soundness.agda` proves that operational semantics as defined are sound with respect to equational theory.

## The work in progress aspect

Proof of soundness theorem is not yet finished, but we believe we can complet it in current setting.

## Difference from original work

This formalization has been made as part of a master thesis.
In order to provide operational semantics we had to change `box`
to be a computation. Because of that substitutions had to slightly change
and equations for equational theory aswell.
