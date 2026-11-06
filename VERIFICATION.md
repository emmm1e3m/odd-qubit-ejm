# Verification record

Release: November 6, 2026. This package includes the current bilingual manuscript, reproduction data, production Lean sources, and existing verification records.

| Material | Included verification |
|---|---|
| Manuscripts | English 21 pages; Chinese 22 pages. Both compile successfully. All 156 cross-reference labels and 22 bibliography entries agree. No undefined references, missing characters, overfull boxes, or blocked floats. Relevant rendered pages were inspected. |
| Paper dependencies | LaTeX sections, four vector figures and their generators, references, and both reproduction entry points are included. |
| Production Lean sources | 186 UnifiedEJM modules and their 29 foundation modules; all local imports resolve within the package. |
| Existing November 4 source and proof checks | 108 added production modules and 77 finite-cut certificates checked; aggregate entry compiled. The final declaration audit reports 4944 declarations, including 4271 theorems, and zero nonstandard axiom dependencies. |
| Existing independent final interface check | 27 final interfaces checked through the production entry. |
| Exact all-n GME certificates | Rank-one length formulas, 7882 compressed representatives, 1405 closure states, 456 small-size complete-state cuts, and endpoint purity checks. The analytic arbitrary-n coverage is given in Appendix E. |

## Evidence

- [Production source manifest](verification/141/physics_sources.json) and [integration record](verification/141/finite_integration.json).
- [Final source check](verification/163/delivery_check.json), [compilation results](verification/163/compile_results.json), and [4944-declaration audit](verification/163/all_axioms.txt).
- [Independent final interface check](verification/164/FinalDeliveryCheck.lean) and [output](verification/164/final_delivery_check.txt).
- [Machine-readable history](lean-unified/verification.json) and [formal coverage](lean-unified/COVERAGE.md).
- [Original exact computations](paper/reproduce/verification_results.json) and [all-n GME certificate results](paper/reproduce/all_n_gme/verification_results.json).

The November 1 key audit and 3050-declaration audit remain in `lean-unified/axioms.txt` and `lean-unified/all_axioms.txt` as historical records. The November 4 integration and final checks are linked separately above. This upload packages those completed checks; it does not relabel them as a newly run Lean audit.

## Reproduction

From `lean-unified/`, use Lean 4.35.0 with the pinned mathlib v4.35.0 dependency:

```text
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean AllAxioms.lean
lake env lean ../verification/164/FinalDeliveryCheck.lean
```

For exact computations, see [the reproduction instructions](paper/reproduce/README.md) and [the self-contained all-n certificate package](paper/reproduce/all_n_gme/README.md).
