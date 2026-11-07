# Verification archive

[Download version 1.1.0](multiqubit-ejm-verification-1.1.0.zip), prepared on November 7, 2026, under the MIT License.

The package contains the production Lean project and its local foundation, pinned dependency configuration, existing axiom-audit programs, and the complete Appendix E1 exact-arithmetic scripts and certificates. Its README gives the build and reproduction commands. Keep the extracted `lean/` and `lean-unified/` directories adjacent.

Compared with the [Zenodo 1.0.0 archive](https://doi.org/10.5281/zenodo.23882488), it adds 108 production Lean modules, 14 Appendix E1 reproduction files, and a separate LICENSE. The E1 materials cover 7,882 compressed representatives, the independent closure certificate, all 456 non-single-qubit cuts for `n = 5, ..., 9`, and endpoint purity checks; the arbitrary-size analytic reductions are in the paper.

These Lean sources and E1 files were already included in the [November 6 GitHub version](https://github.com/emmm1e3m/odd-qubit-ejm/commit/4677c9a39580b44b5ac2d258cf497c7bc49dfcd2). Version 1.1.0 supplies a self-contained downloadable package and updated instructions. No Lean proofs or certificate computations were newly added or rerun during packaging.

The archive contains 241 files. Packaging checks verified local import closure, relative dependencies, pinned configuration, certificate completeness, and successful extraction. The current [bilingual paper](../paper/README.md) is distributed separately.
