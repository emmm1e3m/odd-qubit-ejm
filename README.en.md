# A unified construction of continuously tunable multiqubit elegant joint measurements

[中文](README.md) | English

**Tingyu Zhang and Yan Cen (corresponding author)**<br>
Department of Physics, Fudan University, Shanghai, China<br>
Email: [23300190021@m.fudan.edu.cn](mailto:23300190021@m.fudan.edu.cn) · [cenyan@fudan.edu.cn](mailto:cenyan@fudan.edu.cn)<br>
**Version: November 7, 2026; bilingual author-review manuscript in PRA format**

- Paper PDFs: [English, 21 pages](paper/main.pdf) · [Chinese, 23 pages](paper/main-zh.pdf)
- LaTeX sources: [English](paper/main.tex) · [Chinese](paper/main-zh.tex)
- Reproduction: [exact computations](paper/reproduce/README.md) · [Lean project](lean-unified/README.md) · [formal coverage](lean-unified/COVERAGE.md)
- [Complete verification archive 1.2.0](archives/multiqubit-ejm-verification-1.2.0.zip) · [Version notes](archives/README.md)

We study continuous phase deformations through a specified elegant joint measurement (EJM). The complete measurement remains orthonormal, and each qubit's local Bloch vectors form a regular tetrahedron with a common radius. Write $r_E(n)=\sqrt3/2^{n-1}$ for the reference radius.

## Main results

1. **A unified radius-increasing family for every integer $n\ge5$.** One four-feature Boolean kernel gives complete measurements with fixed tetrahedral directions and radius

   $$r_n(t)=r_E(n)(1-\sin t).$$

   On $[-\pi/2,\pi/2]$, the radius is continuous and strictly decreasing, with exact image $[0,2r_E(n)]$. At $t=0$, the reference measurement is recovered column by column; at the right endpoint, every one-qubit reduced state is $I/2$.
2. **The exact optimum for Boolean straight phase paths.** In the fixed phase representation, maximize over all Boolean generators through the reference point that preserve regular geometry in a neighborhood of that point, and over all real parameters. The maximum is $r_E(n)$ for $n=2,3,4$ and $2r_E(n)$ for $n\ge5$, with both bounds attained. The result also applies to two-valued real generators after removing a global phase and reparametrizing.
3. **A two-parameter embedding for even qubit numbers.** For every even $n\ge8$, the earlier even-qubit family and the unified radius-increasing family are coordinate sections of one complete measurement family. On the domain $\Omega$ specified in the paper, $r_n(\alpha,\beta)=r_E(n)(\cos\alpha-\sin\beta)$ has exact image $[0,2r_E(n)]$. The two axes recover the corresponding measurements column by column, and the two directions are independent at the level of ordered measurement projectors.
4. **A four-qubit obstruction for straight paths and a radius increase along a curved path.** Every real straight phase path through the reference point in the fixed representation that preserves regular geometry locally has radius at most $r_E(4)$ for all parameters. An explicit curved path through the same point strictly increases the radius throughout $[0,\pi/4]$, reaching exactly $(1+1/\sqrt2)r_E(4)$.
5. **Genuine multipartite entanglement along the entire path and implementation.** For every $n\ge5$, every real parameter and every column, $C_{\rm GME}=\sqrt{1-r_n(t)^2}>0$, with precisely the single-qubit cuts minimizing the concurrence. The zero-radius endpoint is inequivalent to every stabilizer pure state under local unitaries and qubit permutations. The complete measurement unitary has exact Clifford-hierarchy levels $n+1,n,4$ at $t=0,-\pi/2,\pi/2$, respectively. For every even $n\ge6$, the unified and cosine zero-radius endpoints have identical one-qubit reductions but are inequivalent under local unitaries and qubit permutations: the cosine endpoint has $p_{12}=1/2+2^{3-n}$ and $C_{\rm GME}\le\sqrt{1-2^{4-n}}<1$.

The paper also proves local rigidity of the specified three-qubit point in the fixed Pauli-orbit representation. At six qubits, the direct superposition has **equal signed local components** exactly when $\sin\alpha\sin\beta=0$. Within the paper's four-group phase model, including an independent zero-string phase, the regular solutions near the reference point are exactly two crossing branches.

These optima concern the specified phase models. An earlier four-qubit parameter segment reaches the larger radius $3r_E(4)$. We prove that no measurement on that segment is equivalent to our specified reference point under a common local unitary, qubit permutations, and outcome relabeling; we do not claim global optimality over all EJMs.

## Formalization and reproduction

The November 8, 2026 update completes the Lean proofs of exact GME and minimizing cuts for every n≥5, every real parameter, and every measurement column, the endpoint inequivalence results, and the extension to arbitrary at-most-two-valued real generators. The final entry and all local declaration axioms were checked; see the [verification record](VERIFICATION.md). The manuscript text and PDFs are unchanged.

The [Lean 4.35.0 / mathlib v4.35.0 project](lean-unified/README.md) formalizes these constructions, model optima, low-dimensional results, and inequivalence from the actual circuit columns and reduced matrices. Coverage also includes the actual reduced spectrum $\lambda_\pm=(1\pm r)/2$, the von Neumann entropy identity $S=h_2((1+r)/2)$, and strict entropy monotonicity and endpoints along the unified path. See [COVERAGE.md](lean-unified/COVERAGE.md) for precise assumptions and declaration names. The adjacent `lean/` directory supplies the required common foundations.

The [exact reproduction scripts](paper/reproduce/README.md), using Python and SymPy, independently check the original phases and circuit, finite character sums, derivative certificates, curved-path identities, and polynomial inequivalence certificates, with saved results included. Finite-dimensional recomputation provides cross-checks; the Lean proofs establish the statements for arbitrary dimension.

The manuscript has separate Discussion and Conclusions sections. Both language versions share four figures and five tables in English. Acknowledgments follow the authors' supplied statement, and the Conclusions state that the main mathematical results have been formally proved in Lean. The current verification materials are available in the [1.2.0 archive](archives/multiqubit-ejm-verification-1.2.0.zip) under the MIT License; [Zenodo 1.0.0](https://doi.org/10.5281/zenodo.23882488) preserves the earlier version. See the [author-review notes](paper/README.md).
