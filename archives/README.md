# Verification archive

[Download version 1.2.0](multiqubit-ejm-verification-1.2.0.zip), prepared on November 8, 2026, under the MIT License.

This version adds the completed Lean proofs of all-size genuine multipartite entanglement, endpoint comparisons, and the arbitrary two-valued real-generator extension. It includes 735 UnifiedEJM modules, 29 foundation modules, pinned configuration, the current coverage map, and the final theorem and declaration-audit outputs. Keep the extracted `lean/` and `lean-unified/` directories adjacent.

The Lean proof uses finite sizes n=5…8 and a stronger analytic tail from n=9, together with arbitrary-length background induction and exact prefix-cut coefficient proofs. The independent Appendix E1 Python package and its previous results remain included; its 456 finite cuts were not all individually ported to Lean, and the full Python computation was not rerun for this release.

Packaging checks verified all 2062 local import edges, pinned dependencies, certificate completeness, and extraction of all 795 files. The current [bilingual paper](../paper/README.md) is distributed separately and is unchanged by this formalization update. See the [verification record](../VERIFICATION.md).

## Earlier versions

- [Version 1.1.0](multiqubit-ejm-verification-1.1.0.zip), November 7, 2026: 186 UnifiedEJM modules, 29 foundation modules, and the self-contained Appendix E1 exact-arithmetic package.
- [Zenodo version 1.0.0](https://doi.org/10.5281/zenodo.23882488): the earlier archived proof package. The Zenodo record has not been updated in this release.
