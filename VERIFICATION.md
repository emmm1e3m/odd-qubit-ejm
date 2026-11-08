# Verification record

Formalization update: November 8, 2026. A subsequent targeted bilingual manuscript revision clarified prior-work attribution, model scope, and the interference explanation, with the final author-requested wording edits included. Both versions compiled successfully (English 22 pages, Chinese 23 pages); all 156 cross-reference labels and 23 citation numbers were preserved, and the rendered pages were checked. The mathematical proofs and Lean sources were unchanged.

| Material | Verification |
|---|---|
| Production Lean sources | 735 UnifiedEJM modules and 29 foundation modules; local imports and the source/object correspondence of new proofs checked. Unchanged previously verified foundations retained. |
| Final proof entry | Recompiled successfully; final theorem types and axiom dependencies checked. |
| All local declarations | 105633 declarations, including 89376 theorems; zero dependencies outside propext, Classical.choice, and Quot.sound. Private and generated declarations included. |
| All-size GME | Every n≥5, every real parameter and actual measurement column: exact GME, positivity, and precisely the single-qubit minimizing cuts. |
| Endpoint comparisons | Unified endpoint pair purity and exclusion of stabilizer LU/permutation orbits; cosine endpoint pair purity and strict GME bound; inequivalence of the two zero-radius endpoints for every even n≥6. |
| Real generators | At-most-two-valued real generators, including constants: actual projector normalization, equal attainable radius sets, and the attained model optimum. |

The all-size Lean proof uses finite sizes n=5…8 and a stronger perturbation bound valid from n=9, combined with arbitrary-length background induction and exact prefix-cut coefficient proofs. The original Appendix E1 scripts independently cover n=5…9 and the paper's representative certificates. Their previous exact results are preserved; the full Python computation was not rerun, and its 456 cut checks were not all individually ported to Lean.

## Current evidence

- [Final theorem types and axiom audit](verification/209/final-axioms.txt), with [the audit source](verification/209/AllNFinalAudit.lean).
- [All-declaration audit](verification/209/all-axioms.txt).
- [Source correspondence](verification/209/final-source-check.json) and [verification summary](verification/209/final-verification.json).
- [Formal coverage](lean-unified/COVERAGE.md) and [machine-readable verification history](lean-unified/verification.json).
- [Original exact computations](paper/reproduce/verification_results.json) and [Appendix E1 results](paper/reproduce/all_n_gme/verification_results.json).

The [1.2.0 archive](archives/multiqubit-ejm-verification-1.2.0.zip) packages the proof sources, pinned dependencies, audit outputs, and 14 Appendix E1 reproduction files. Packaging checks covered 2062 local import edges and extraction of all 795 files.

## Earlier verification

The November 7 manuscript checks recorded: English 21 pages, Chinese 23 pages; 156 matching cross-reference labels and 23 bibliography entries; successful bilingual compilation and rendered-page checks. No manuscript recompilation was needed for this source-only formalization update.

The November 4 proof checks covered 186 UnifiedEJM modules, 77 finite-cut certificates, and 4944 declarations. See the [earlier source check](verification/163/delivery_check.json), [compilation results](verification/163/compile_results.json), [axiom audit](verification/163/all_axioms.txt), and [independent interface check](verification/164/final_delivery_check.txt). The November 1 audit files in `lean-unified/` retain their historical counts.

## Reproduction

See the [Lean instructions](lean-unified/README.md) and [exact-computation instructions](paper/reproduce/README.md). The pinned toolchain is Lean 4.35.0 with mathlib v4.35.0. The current proof update does not modify the earlier Zenodo archive.
