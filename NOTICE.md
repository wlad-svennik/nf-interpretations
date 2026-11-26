# Attribution

The substantive Lean development was supplied by R. Gutin in
`nf-interp(1).zip`. This repository preserves the `standalone/` source tree,
with module-interface changes documented by per-file hashes in
`provenance/source-files.json`.

The project uses the following external libraries, fetched separately at the
commits in `lake-manifest.json`:

- **Mathlib**, developed by the Mathlib community. Its source and license remain
  at <https://github.com/leanprover-community/mathlib4>.
- **Foundation**, developed by Formalized Formal Logic, under Apache-2.0. Its
  source and license remain at
  <https://github.com/FormalizedFormalLogic/Foundation>.
- The libraries required by those dependencies retain their own notices and
  licenses in their respective repositories.

The `ConNF/NF/` files are present in the supplied standalone development. The
uploaded `con-nf.patch` records them as new files. They use the con-nf naming and
finite-axiomatization conventions described in their source comments. Existing
source comments and mathematical attributions have been preserved.

The separate paper *Choice and Consistency Strength in NF and NFU* is joint work
of **R. Gutin and E. Glazer**. This submission does not change its attribution or
grant any rights on behalf of E. Glazer. The mathematical statements checked here
are specified independently in `Challenge.lean` and `formalization.yaml`.

ChatGPT assisted with the Palomar packaging and new adapter code; it is not
listed as a human author or responsible maintainer.
