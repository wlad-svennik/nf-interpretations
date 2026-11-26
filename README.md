# NF and NF + AxCount in Lean

This repository packages R. Gutin's `nf-interp` Lean development for review by the
Palomar Registry. The source is the `standalone/` project in the author-supplied
`nf-interp(1).zip` of 25 November 2026.

The development contains 149 original Lean modules on New Foundations, NFU with
Infinity, the Axiom of Counting, and related interpretations. The uploaded source
uses Lean 4.35.0. Its mathematical definitions and proofs are retained; the
packaging adds Lean module headers, public imports, a scoped meta section for
the `hdef` tactic implementation, and exposed public sections
where required by Palomar. The original-to-packaged file hashes are recorded in
[`provenance/source-files.json`](provenance/source-files.json).

## Statements submitted for review

[`Challenge.lean`](Challenge.lean) gives independently readable definitions and
statements using only Mathlib. [`Solution.lean`](Solution.lean) imports the
substantive development and supplies the corresponding proofs. These modules are
intentionally independent and must not be imported together.

The primary comparison targets are:

| Lean declaration | Mathematical statement |
|---|---|
| `NFUCut.nf_nfu_inf_mutually_interpretable` | Three fixed parameter-free formulas uniformly interpret an NF model in every NFU + Infinity model. Conversely, every NF model, with every object declared a set, satisfies NFU + Infinity. |
| `Palomar.exists_nf_model` | There is a set-sized model satisfying extensionality and the full stratified comprehension scheme of NF. This follows from the uploaded Jensen NFU model construction and the uploaded interpretation. |
| `Palomar.nfuic_interprets_nfc` | Two fixed first-order formulas uniformly define an NF + AxCount model inside every NFU + Infinity + AxCount model. An injection identifies the target with the definable domain; equality is actual equality. |
| `Palomar.nfc_interprets_nfuic` | Every NF + AxCount model is already an NFU + Infinity + AxCount model with the same membership relation. Infinity is obtained from the proved NF theorem. |

Here NF has extensionality and every stratified comprehension instance, including
parameters. The first result uses NFU with an explicit sethood predicate; the
counted results use Jensen's membership-only presentation of NFU. Both
presentations are spelled out in the Challenge. The Axiom of Counting says that
forming singleton images preserves each internal Frege natural cardinal.

Six additional comparison targets are the elementary NFU witness lemmas
`NFUCut.Model.exists_emp`, `exists_sing`, `exists_adj`, `exists_succ`, `exists_nat`,
and `exists_univ`. They prove the existence of the empty set, singletons,
one-element adjunction, cardinal successor, the least inductive set of natural
cardinals, and the universal set. Their statements specify the choice-defined
objects used in the original definition of Infinity. Their proofs are checked
alongside the primary results.

The exact declarations are enumerated in [`comparator.json`](comparator.json),
with their source correspondence in [`formalization.yaml`](formalization.yaml).

The Challenge's deliberate `sorry` placeholders describe the problems being
checked. They are not used by the Solution. Fixed mathematical definitions are
compared transitively from the theorem statements; they are not open definition
holes.

The wider development also contains interpretations involving FunctionNF,
CombNF, Mac Lane set theory, and Zermelo set theory with rank axioms. Inclusion
and successful compilation of those modules do not make every result in them a
separate Palomar comparison target. The comparator and metadata specify the
reviewed scope.

## Reproduction

The toolchain is pinned in `lean-toolchain`; all Git dependencies are pinned to
full commits in `lake-manifest.json`. The project uses Mathlib and the
Formalized Formal Logic Foundation library as external dependencies.

```sh
lake exe cache get
lake build
```

Palomar's complete mechanical workflow is additionally required before intake.
The workflow revision and the exact source commit, together with the resulting
report, identify a verification run. A local build alone is not a Palomar pass.

## Provenance and licensing

The source archive has SHA-256
`ba8c3ce7f93dba1b665e5b50e1c28e5d30e50d50cfb0df79172196b9135fd1c2`.
It includes the companion manuscript *New Foundations, NFU, Mac Lane set theory
and the Axiom of Counting: Interpretations checked in Lean: the proofs on paper*.
The manuscript is a mathematical source for this development; this repository
contains the Lean project rather than a relicensed copy of that manuscript.

R. Gutin's code and Lean proofs are available under the root MIT license.
External libraries retain their own licenses and credits. See
[`NOTICE.md`](NOTICE.md) for dependency and mathematical-source attribution.

ChatGPT assisted the submission packaging, source comparison, and statement
adapters. The metadata distinguishes this work from the uploaded development and
records the review and automation limits. Registry intake and permanent
registration are separate steps; the existence of this repository does not
assert either has occurred.
