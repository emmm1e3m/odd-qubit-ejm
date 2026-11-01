# Verification record

Version: November 1, 2026. The appendix condensation changes presentation only. The packaged Lean sources are identical to the sources used for the isolated audit below; that audit was not rerun for the editorial revision. The seven exact recomputation groups were rerun successfully from this publication package.

| Check | Result |
|---|---|
| Current manuscripts | English 15 pages; Chinese 16 pages. Both recompiled after condensing Appendices B and D. Nine repeated display blocks were removed; the remaining 107 display blocks and the main results are unchanged. Rendered pages were inspected; 130 labels and 7 references agree. |
| Lean source package | 78 UnifiedEJM modules and 29 required foundation modules, plus the unified entry, recompiled from source in an isolated directory. Original project build directories were excluded from the import path. Lean 4.35.0 and pinned mathlib v4.35.0 dependency caches were retained. |
| Key declaration audit | 77 declarations passed. |
| Complete local declaration audit | 3050 declarations, including 2592 theorem declarations, private helpers and generated declarations. No nonstandard axiom dependencies. |
| Allowed foundational axioms | propext, Classical.choice, Quot.sound. No sorryAx or custom axioms. |
| Exact recomputation | All seven groups passed, using exact finite sums, Laurent polynomials, rational arithmetic and symbolic identities. |
| Semantic review | Six independent topic reviews checked physical definitions, hypotheses and manuscript correspondence. The repaired six-qubit geometry bridge was independently reviewed. |

This audit added the six-qubit theorem `SixFamily.geometric_local_crossing`, which derives the general geometric classification on an actual open neighborhood without an extra positivity assumption. It also brought the explicit CNOT sequence into the unified import closure and added `Physical.measurement_eq_original_gate_sequence`.

The [coverage table](lean-unified/COVERAGE.md) specifies the assumptions and interfaces. The exact maximum theorem uses normalized Boolean generators; two-rate phase normalization and complement identities are formalized separately. There is no separately stated radius-set equality theorem for arbitrary real-valued generators.

Evidence: [key audit](lean-unified/axioms.txt), [complete declaration audit](lean-unified/all_axioms.txt), [machine-readable summary](lean-unified/verification.json), [exact calculation results](paper/reproduce/verification_results.json).

Build and audit from `lean-unified/`:

```text
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean AllAxioms.lean
```

Finite-dimensional checks include 1,280 Gram entries and 224 actual partial traces. Arbitrary dimension and continuous parameter intervals are covered by the analytic arguments and Lean proofs.
