# Exact certificates for the all-n GME law

This directory is self-contained. It accompanies Appendix E of the manuscript and verifies the finite exact coefficient certificates used to establish, for every integer n ≥ 5 and real t,

`C_GME = sqrt(1 - 3 * 2^(2-2n) * (1-sin(t))^2)`.

Every cut with at least two qubits on each side has purity strictly below 1/2; the one-qubit cuts are precisely the minimizing cuts. The analytic reductions in Appendix E establish coverage of arbitrary n. The computations below evaluate the resulting finite certificates with integer arithmetic; no parameter sampling or extrapolation is used.

## Run

Use Python 3.10 or later with NumPy installed, then run:

```text
python -B verify.py
```

The script resolves every input relative to its own location, so it can also be run from another working directory. It prints each completed group and writes `verification_results.json` here. No repository files, network access, symbolic-algebra package, or external data are required. Allow a few minutes; the representative enumeration is the longest step. Do not run Python with `-O`, which disables assertions.

## Coverage and files

| Verification | Exact coverage | Files |
| --- | --- | --- |
| Rank-one cuts | All prefix/suffix lengths, including both length parities and empty free groups | `prove_prefix.py`, `prove_p12.py`, `four_copy.py`; `data/prefix_symbolic.json`, `data/prefix_short_symbolic.json`, `data/p12_symbolic.json` |
| Low-rank backgrounds | All 7,882 parity-compressed representatives for cross rank 2, 3, 4; all 121 coefficient classes and multiplicities | `data/representatives.txt`, `data/representative_coefficients.json` |
| Independent background coverage | Exhaustive closure of 1,405 intermediate linear-relation states and 1,313 terminal signatures | `data/closure_states.json`, `data/closure_certificate.json` |
| Small complete states | All 456 non-single-qubit cuts for n = 5, …, 9, distinct up to complementation, reconstructed directly from the original H/CNOT gates | `data/finite_coefficients.json` |
| Bridge and endpoint checks | Exact affine amplitudes at n = 5, …, 10; p12 = 11/32 at n = 5 and 5/16 for every n ≥ 6 at t = π/2 | `verify.py` |

The coefficient order throughout is `1, cos(t), sin(t), cos(2t), sin(2t)`. Cuts in the small-size JSON use one-based qubit indices. A representative word gives the two sides by `0` and `1`; complementary words describe the same cut. `verify.py` independently regenerates the representatives from every color word up to the proved bounds `n' ≤ 3κ+7`, and computes their purities through a graph-basis relation formula. Thus the supplied list is checked for completeness as well as for its coefficients. The separate closure check reproduces the alternate finite coverage certificate; its witness lengths are not used as a cutoff.

The rank-one symbolic calculation groups each free length-L string into all-zero, all-one, mixed-even and mixed-odd classes. Their exact multiplicities are `1`, `1`, `2^(L-1)-1-[L even]`, and `2^(L-1)-[L odd]`. An empty group contributes only the empty string. Applying these counts independently to both replicas yields the stored polynomials in `X=2^(k-4)`, `Y=2^(n-k-4)` or `K=2^(n-6)`, with every parity branch checked. The positive gap bounds in Appendix E then hold on their full variable domains.

For a rank-one cut, let `k,l=n-k` be its prefix and suffix lengths. The following exact lower bounds on `1/2-p_A(t)` follow from the stored coefficient polynomials for every real t. A length variable is used only in the row where its exponent is nonnegative.

| Lengths | Positive lower bound on `1/2-p_A(t)` | Lower bound divided by `2^(-n)` |
| --- | --- | --- |
| k,l ≥ 4 | `(992XY+8)/(262144X²Y²)` | at least `31/32` |
| k = 3, l ≥ 4 | `(608Y-248)/(65536Y²)` | at least `45/64` |
| l = 3, even k ≥ 4 | `(608X-248)/(65536X²)` | at least `45/64` |
| l = 3, odd k ≥ 5 | `(320X+8)/(65536X²)` | at least `5/8` |
| min(k,l) = 2, n ≥ 6 | `(256K-120)/(16384K²)` | at least `17/32` |
| k = l = 3 | `27/2048` | `27/32` |
| n = 5 | `13/1024` | `13/32` |

In the first five rows, `X,Y,K ≥ 1`. The four oscillating coefficients are bounded by absolute values; in the second and third rows use `|64Y-128| ≤ 64Y+128` (or replace Y by X). In the last row the exact polynomial is `(379+112 cos(t)-24 sin(t)+3 cos(2t)-4 sin(2t))/1024`; use `sqrt(112²+24²) < 115` and `sqrt(3²+4²)=5` to obtain `p_A ≤ 499/1024`. Every final-column value exceeds `1/4`, establishing the common bound `p_A ≤ 1/2-2^(-n-2)` at every length.

The graph calculation used to independently verify compressed representatives has four binary graph words, the columns of W, with site rows `(4,1,8,…,8,2,4)` in low-bit integer notation. For the path graph state G, the background is a superposition `sum_d c_d Z^(Wd)|G>`. If `H=(h_x,h_b,h_c,h_s)` is a four-feature character and `ν=n mod 2`, its graph-word coordinates are

```text
d = (h_x XOR h_b XOR h_s,
     h_x XOR ((1-ν)h_b) XOR (ν h_c),
     h_x XOR h_s, h_b XOR h_c),
c_d(u) = (-i)^h_s * [(1+u)δ_(H,0)/2 + (1-u)W_F(H)/2].
```

Here `W_F(H)=sum_x (-1)^(F(x)+H·x)/16` is the normalized Walsh coefficient of the sign function `(-1)^F`, whose absolute sum is 3. The relative phase `(-i)^h_s` follows from the final-qubit Hadamard and is retained throughout. For a physical cut A|B, set `M_A(v_A)=(Γ_BA v_A,W_A^T v_A)`, let R be its binary rank, and set `E_A={(d,k):(W_B d,k) in im M_A}`. Pauli orthogonality gives

```text
S(d,k) = sum_l c_l conjugate(c_(l XOR d)) (-1)^((l XOR d)·k),
p_A(background) = 2^(-R) sum_((d,k) in E_A) |S(d,k)|².
```

Each point in the image of M_A has `2^(|A|-R)` preimages. The local constraints at B sites are `v_(j-1) XOR v_(j+1)=W_j·d`, with boundary values `v_0=v_(n+1)=0`; A sites have free v_j and contribute to k. The code retains the binary relation on `(d,k,v_(j-1),v_j)` and its uniform preimage count, imposes each constraint before projecting the old bit, and thereby evaluates exactly the displayed purity. Closing this relation under both choices of the next cut side gives the separate closure certificate. This describes the finite algorithm without using witness length as an assumption.

All complex quantities are stored as pairs of Python integers. NumPy is used only with `dtype=object` for integer matrix multiplication in the finite-cut check. Rational values use `Fraction`; square-root upper bounds use upward-rounded integer square roots. The five small-size maximal bounds are

```text
n=5: 1995/4096       n=6: 3997/8192       n=7: 32313/65536
n=8: 130105/262144   n=9: 522297/1048576
```

The background bounds for cross rank 2, 3, 4 are respectively `3/8`, `33/128`, `33/256`. For higher rank, the manuscript uses the analytic Walsh norm bound `10/2^κ`; the exact overlap with the complete state supplies the n ≥ 10 tail. These analytic inequalities and the local-isometry reduction are stated in Appendix E rather than replaced by a finite numerical scan.
