# A core language for temporal resources

A (work in progress) Agda formalisation of a (Fitch-style) modally typed,
effectful **core language for safe and correct programming with temporal
resources**, i.e., resources that become available only after some amount of
time after being brought into scope, e.g., when on a production line the
assembly operation needs to wait for (car) parts to dry after the paint
operation.

The **main features** of this core language are:

- Fitch-style, _temporally-graded modal types_ `[ tau ] X` are used to capture
  temporal resources, expressing that an `X`-typed value will be available in at
  most `tau` time steps, after which it becomes possible to unbox it.

- A novel notion of _temporally-aware algebraic effects_, where operations'
  specifications include their execution times, and their continuations know
  that an operation's worth of additional time has passed before they start
  executing, making it possible to safely access further temporal resources in
  it.

- _Effect handlers_, also temporally-aware, that have to respect the temporal
  discipline of algebraic operations.

- A _graded monads-based effect system_ (with some added temporal awareness)
  that modularly tracks the execution times of computations.

The formalisation is developed and tested with Agda version 2.6.4.1 and Agda
Standard Library version 2.0.

The formalisation consists of **three main parts**:

### Core language, type system

The main modules presenting the core language are:

- `Syntax/Types.agda` defines types.

- `Syntax/Contexts.agda` defines contexts and operations on them.

- `Syntax/Language.agda` defines well-typed values and computations.

- `Syntax/Renamings.agda` defines renamings and their action on well-typed
  terms.

- `Syntax/Substitutions.agda` defines the action of substitution on well-typed
  terms.

- `Syntax/CompContext.agda` defines computation term and evaluation contexts.

### Operational semantics, progress theorem

- `OperationalSemantics/State.agda` defines state for the stateful time-aware
  operational semantics, and proves some auxiliary results about states.

- `OperationalSemantics/PreservationTheorem.agda` defines a reduction relation
  for well-typed computations; as the semantics is defined on well-typed
  computations, it simultaneously also proves preservation theorem.

- `OperationalSemantics/TheoremsAboutSteps.agda` proves some basic results
  about the reduction relation.

- `OperationalSemantics/ProgressTheorem.agda` proves progress theorem.

### Equational theory

- `EquationalTheory/EquationalTheory.agda` defines an equational theory for the
  language inspired by the standard equational presentations of local state.

## Work in progress

Agda formalisation of the soundness proof is not yet finished, and remains work
in progress.

## Difference from original work [1]

This formalisation has been made as part of a master thesis [2]. 

In order to provide an operational semantics for the language, we changed `box`
to be a computation. Because of that, substitutions had to be slightly changed
and instead of the previous (pattern-matching beta/eta-equations based)
equational theory we developed a new equational theory for the language in which
`box` and `unbox` are treated akin to memory allocation and lookup in standard
equational presentations of local state. Compared to the inductive definition in
the original work, this formalisation gives renamings an equivalent, but more
computational definition as certain well-behaving and temporally correct
functions from variables in one context to variables in another.

[1] Danel Ahman (2023): When Programs Have to Watch Paint Dry. FoSSaCS 2023.

[2] Gašper Žajdela (2023): Operacijska semantika za jezik s časovno omejenimi
    viri : magistrsko delo. Available at
    [https://repozitorij.uni-lj.si/IzpisGradiva.php?lang=eng&id=150138](https://repozitorij.uni-lj.si/IzpisGradiva.php?lang=eng&id=150138).
    Faculty of Mathematics and Physics, University of Ljubljana.
