"""从原始 H/CNOT 电路复算论文中的有限精确证书；不导入研究工作目录。"""

from collections import defaultdict
from pathlib import Path
import argparse
import json
import math
import platform
import time

import sympy as sp


ROOTS = (1, 1j, -1, -1j)
CURVE_EXPONENTS = [
    (0, 0), (1, 1), (1, 1), (1, 0), (2, 1), (2, 1), (0, 1), (0, 1),
    (1, 0), (1, 1), (0, 0), (0, 1), (0, 1), (0, 1), (1, 0), (1, 0),
]
UNIFIED_TARGET = {(0,): 4, (1,): 2j, (-1,): -2j}
MOTHER_TARGET = {(1, 0): 2, (-1, 0): 2, (0, 1): 2j, (0, -1): -2j}
CURVE_T = {(1, 1): 2, (-1, -1): 2, (0, 1): 2j, (0, -1): -2j}
CURVE_H = {
    (1, 0): 2, (-1, 0): 2, (1, 1): -2j, (-1, 1): -2j,
    (1, -1): 2j, (-1, -1): 2j, (2, 0): -4j, (-2, 0): 4j,
}


def bits(z, n):
    return [(z >> (n - 1 - j)) & 1 for j in range(n)]


def sign(z, h):
    return -1 if (z & h).bit_count() % 2 else 1


def f0(z):
    return 0 if z == 0 else (z.bit_count() - 1) % 4


def kernel4(v):
    x, b, c, s = bits(v, 4)
    return 1 ^ x ^ b ^ s ^ (x * s) ^ (x * c) ^ (b * c) ^ (b * c * s)


def qfour(z, n):
    a = bits(z, n)
    x = a[0] ^ a[-2]
    b = sum(a[j - 1] for j in range(2, n - 1, 2)) % 2
    c = sum(a[j - 1] for j in range(3, n - 1, 2)) % 2
    s = a[0] ^ a[-1]
    return kernel4(8 * x + 4 * b + 2 * c + s)


def qa(z, n):
    return int(not any(bits(z, n)[j - 1] for j in range(2, n - 1, 2)))


def qfive(v):
    a, b, c, d, e = bits(v, 5)
    return kernel4(8 * (a ^ d) + 4 * b + 2 * c + (a ^ e))


def chain(z, n):
    # 右侧门先作用：n→n−1，随后 n−1→n−2，直到 2→1。
    for control in range(n, 1, -1):
        if z & (1 << (n - control)):
            z ^= 1 << (n - control + 1)
    return z


def clean(poly):
    result = {e: c for e, c in poly.items() if c != 0}
    # 本通道只对小高斯整数加减和乘以 ±1、±i；二进制表示严格精确。
    for c in result.values():
        assert float(c.real).is_integer() and float(c.imag).is_integer()
        assert abs(c.real) < 2 ** 20 and abs(c.imag) < 2 ** 20
    return result


def add(*polys):
    out = defaultdict(complex)
    for poly in polys:
        for e, c in poly.items():
            out[e] += c
    return clean(out)


def scale(poly, c):
    return clean({e: c * v for e, v in poly.items()})


def serial(poly):
    return [{"exponent": list(e), "coefficient": [int(c.real), int(c.imag)]}
            for e, c in sorted(poly.items())]


def phase_state(n, exponents, base=None):
    # 返回 sqrt(2N) 倍种子：先输入相位，再末位无归一化 H，最后 CNOT 链。
    out = [defaultdict(complex) for _ in range(1 << n)]
    for z in range(1 << n):
        c = ROOTS[f0(z)] if base is None else base[z]
        out[chain(z & ~1, n)][tuple(exponents[z])] += c
        out[chain(z | 1, n)][tuple(exponents[z])] += c * (-1) ** (z & 1)
    return [clean(v) for v in out]


def pauli(n, j, p, signed=True):
    mask = 1 << (n - 1 - j)
    out = []
    for z in range(1 << n):
        zsign = -1 if z & mask else 1
        coefficient = zsign if p == "Z" else (1 if p == "X" else 1j * zsign)
        if signed and j == n - 1 and p == "Y":
            coefficient *= -1
        out.append((z if p == "Z" else z ^ mask, coefficient))
    return out


def moment(n, state, j, p):
    out = defaultdict(complex)
    for z, (w, phase) in enumerate(pauli(n, j, p)):
        for e, c in state[z].items():
            for f, d in state[w].items():
                out[tuple(a - b for a, b in zip(e, f))] += d.conjugate() * phase * c
    return clean(out)


def all_moments(n, state, target):
    for j in range(n):
        for p in "XYZ":
            actual = moment(n, state, j, p)
            assert actual == target, (n, j + 1, p, actual, target)


def polynomial_inner(left, right):
    out = defaultdict(complex)
    for lv, rv in zip(left, right):
        for e, c in lv.items():
            for f, d in rv.items():
                out[tuple(b - a for a, b in zip(e, f))] += c.conjugate() * d
    return clean(out)


def reduced_entry(state, n, j, row, col):
    # 直接对其余物理位求和，不从 Bloch 公式定义约化矩阵。
    mask = 1 << (n - 1 - j)
    out = defaultdict(complex)
    for rest in range(1 << n):
        if rest & mask:
            continue
        for e, c in state[rest | (row * mask)].items():
            for f, d in state[rest | (col * mask)].items():
                out[tuple(a - b for a, b in zip(e, f))] += c * d.conjugate()
    return clean(out)


def check_full_measurement(n, exponents, components):
    N = 1 << n
    zero = (0,) * len(exponents[0])
    columns = [phase_state(n, exponents, [ROOTS[f0(z)] * sign(z, label) for z in range(N)])
               for label in range(N)]
    for k in range(N):
        for ell in range(N):
            assert polynomial_inner(columns[k], columns[ell]) == ({zero: 2 * N} if k == ell else {})
    for label, state in enumerate(columns):
        lab = bits(label, n)
        adjacent = [0] + lab[:-1] + [0]
        sigma = lab[-1]
        for j in range(n):
            parity = adjacent[j] ^ adjacent[j + 1]
            orientation = 1 if j < n - 1 else -1
            mx = scale(components[j][0], (-1) ** parity)
            my = scale(components[j][1], orientation * (-1) ** (parity + sigma))
            mz = scale(components[j][2], (-1) ** sigma)
            target = {
                (0, 0): add({zero: N}, scale(mz, 0.5)),
                (1, 1): add({zero: N}, scale(mz, -0.5)),
                (0, 1): add(scale(mx, 0.5), scale(my, -0.5j)),
                (1, 0): add(scale(mx, 0.5), scale(my, 0.5j)),
            }
            for indices, expected in target.items():
                assert reduced_entry(state, n, j, *indices) == expected, (n, label, j, indices)
    return {"n": n, "gram_entries": N * N, "one_qubit_reduced_matrices": n * N,
            "normalization_denominator": 2 * N, "method": "exact Laurent identities"}


def circuit_integer(n):
    N = 1 << n
    matrix = sp.zeros(N)
    for z in range(N):
        matrix[chain(z & ~1, n), z] = 1
        matrix[chain(z | 1, n), z] = (-1) ** (z & 1)
    assert matrix.T * matrix == 2 * sp.eye(N)
    return matrix


def pauli_matrix(n, j, p, signed=True):
    matrix = sp.zeros(1 << n)
    for z, (w, c) in enumerate(pauli(n, j, p, signed)):
        matrix[w, z] = int(c.real) + sp.I * int(c.imag)
    return matrix


def pullback(n, j, p):
    # 按门序反向共轭 Pauli，返回翻转、字符与相位。
    bit = lambda site: 1 << (n - 1 - site)
    a = bit(j) if p in "XY" else 0
    b = bit(j) if p in "YZ" else 0
    phase = (1 if p == "Y" else 0) + (2 if p == "Y" and j == n - 1 else 0)
    for control in range(1, n):
        target = control - 1
        if a & bit(control):
            a ^= bit(target)
        if b & bit(target):
            b ^= bit(control)
    if a & 1 and b & 1:
        phase += 2
    if (a ^ b) & 1:
        a ^= 1
        b ^= 1
    return a, a ^ b, ROOTS[(phase - a.bit_count()) % 4]


def verify_kernel_and_gates():
    for n in range(2, 12):
        for w in range(n + 1):
            assert sum((-1) ** k * math.comb(w, k) for k in range(2, w + 1)) % 4 == (0 if w == 0 else w - 1) % 4
    for v in range(16):
        x, b, c, s = bits(v, 4)
        branch = (1 ^ ((1 ^ c) * (x ^ b))) if s == 0 else (b ^ (x * c))
        assert kernel4(v) == branch
    certificates = []
    for shift, character in [(None, 9), (None, 11), (None, 15), (6, 6), (7, 13), (7, 11)]:
        total = sum((-1) ** ((kernel4(v) if shift is None else kernel4(v) ^ kernel4(v ^ shift))
                               + (v & character).bit_count()) for v in range(16))
        assert total == 0
        certificates.append({"derivative_shift": shift, "character": character, "integer_sum": total})
    assert sum(kernel4(v) for v in range(16)) == 10
    for n in range(5, 11):
        generator = [qfour(z, n) - int(z == 0) for z in range(1 << n)]
        assert set(generator) == {0, 1} and generator[0] == 0
        assert sum(generator) == 10 * 2 ** (n - 4) - 1
        all_moments(n, phase_state(n, [(d,) for d in generator]), UNIFIED_TARGET)
    return {"six_walsh_certificates": certificates, "kernel_weight": 10,
            "original_gate_signed_moments_n": list(range(5, 11)),
            "normalization": "Laurent expectation numerator divided by 2^(n+1)",
            "scope": "finite dimension checks; the all-n reduction is proved in Appendix A"}


def verify_boolean_low_dimensions():
    s, k = sp.symbols("s k")
    flip_masks = {}
    for n in (2, 3, 4):
        Cgate = circuit_integer(n)
        groups = {"I": set(), "II": set()}
        characters = {"I": set(), "II": set()}
        for j in range(n):
            for p in "XYZ":
                a, h, gamma = pullback(n, j, p)
                direct = Cgate.T * pauli_matrix(n, j, p) * Cgate / 2
                reconstructed = sp.zeros(1 << n)
                phase = gamma * ROOTS[a.bit_count() % 4]
                for z in range(1 << n):
                    coefficient = phase * sign(z, a ^ h)
                    reconstructed[z ^ a, z] = int(coefficient.real) + sp.I * int(coefficient.imag)
                assert direct == reconstructed
                cls = "I" if gamma == -1j else "II"
                assert gamma in (-1j, -1)
                assert (a & h).bit_count() % 2 == (1 if cls == "I" else 0)
                groups[cls].add(a)
                characters[cls].add(h)
        flip_masks[n] = {name: sorted(values) for name, values in groups.items()}
        if n == 2:
            assert groups == {"I": {1, 2, 3}, "II": set()}
            all_moments(2, phase_state(2, [(0,)] * 4), {(0,): 4})
            all_moments(2, phase_state(2, [(int(z != 0),) for z in range(4)]), {(1,): 2, (-1,): 2})
        if n == 3:
            assert groups == {"I": {1, 2, 3, 4, 5}, "II": {6, 7}}
            q = [1] + [s] * 5 + [k] * 2
            equations = [sp.expand(sum(q[z] * sign(z, h) for z in range(8)) - (1 - s - k)) for h in (1, 4)]
            assert equations == [k, 2 * s - k]
            assert sp.solve(equations, (s, k)) == {s: 0, k: 0}
        if n == 4:
            assert groups == {"I": {1, 2, 3, 8, 9}, "II": {6, 7, 12, 13}}
            A, B, C, D, E, F = sp.symbols("A B C D E F")
            q = [1, s, s, s, A, B, k, k, s, s, C, D, k, k, E, F]
            eq4 = [sp.expand(sum(q[z] * sign(z, h) for z in range(16)) - (1 - s - k)) for h in (1, 3, 7, 15)]
            assert sp.expand(sum(eq4)) == 4 * k
    return {"flip_masks_from_original_gates": flip_masks,
            "n3_character_equations": [str(v) for v in equations],
            "n4_boundary_equations": [str(v) for v in eq4], "n4_sum": "4*k",
            "scope": "analytic exclusion certificates, not enumeration of every Boolean support"}


def trig_polynomial(terms):
    out = defaultdict(complex)
    for kind, coefficient, exponent in terms:
        negative = tuple(-v for v in exponent)
        if kind == "c":
            out[exponent] += coefficient / 2
            out[negative] += coefficient / 2
        else:
            out[exponent] += coefficient / (2j)
            out[negative] -= coefficient / (2j)
    return clean(out)


def verify_mother_and_colors():
    conditional = []
    for flip, character in [(8, 8), (2, 2), (9, 15), (5, 7), (5, 3), (3, 1), (4, 4)]:
        counts = {e: [0, 0] for e in (-1, 0, 1)}
        for w in range(16):
            q0 = ((w >> 3) << 4) | (w & 7)
            shifted = w ^ flip
            q1 = ((shifted >> 3) << 4) | 8 | (shifted & 7)
            exponent = qfive(q0) - qfive(q1)
            counts[exponent][(w & character).bit_count() % 2] += 1
        signed = [counts[e][0] - counts[e][1] for e in (-1, 0, 1)]
        assert signed == ([2, 0, -2] if (flip, character) == (4, 4) else [0, 0, 0])
        conditional.append({"flip": flip, "character": character, "counts": counts})
    for n in (2, 4, 6, 8):
        all_moments(n, phase_state(n, [(qa(z, n) - int(z == 0),) for z in range(1 << n)]), {(1,): 2, (-1,): 2})
    for n in (8, 10):
        all_moments(n, phase_state(n, [(qa(z, n) - int(z == 0), qfour(z, n) - int(z == 0))
                                     for z in range(1 << n)]), MOTHER_TARGET)
    exception = {(1, 1): 4, (1, -1): -4, (-1, 1): -4, (-1, -1): 4}
    state = phase_state(6, [(qa(z, 6) - int(z == 0), qfour(z, 6) - int(z == 0)) for z in range(64)])
    for j in range(6):
        for p in "XYZ":
            target = add(MOTHER_TARGET, exception) if j in (2, 3) and p == "X" else MOTHER_TARGET
            assert moment(6, state, j, p) == target
    color = {(0, 0): (0, 0, 0), (1, 0): (1, 0, 0), (0, 1): (0, 1, 0), (1, 1): (0, 0, 1)}
    exponents = [color[(qa(z, 6), qfour(z, 6))] for z in range(64)]
    state = phase_state(6, exponents, [ROOTS[z.bit_count() % 4] for z in range(64)])
    backgrounds = {}
    for j in range(6):
        for p in "XYZ":
            terms = []
            if j in (2, 3) and p == "X":
                terms = [("c", -8, (1, 0, 0)), ("c", 8, (0, 0, 1)),
                         ("c", -8, (1, -1, 0)), ("c", 8, (0, 1, -1))]
            if j == 2 and p == "Y":
                terms = [("c", 16, (1, 0, 0)), ("c", -16, (0, 1, -1))]
            if (j, p) in ((3, "Z"), (4, "Z"), (5, "X")):
                terms = [("s", -16, (0, 1, 0)), ("s", -16, (1, 0, -1))]
            actual = moment(6, state, j, p)
            assert actual == trig_polynomial(terms)
            backgrounds[(j, p)] = actual
    full_exponents = [e + (0,) for e in exponents]
    full_exponents[0] = (0, 0, 0, 1)
    full_state = phase_state(6, full_exponents, [ROOTS[z.bit_count() % 4] for z in range(64)])
    # 直接构造 4F_I、4F_II，保持所有 Laurent 系数均为高斯整数。
    fi = trig_polynomial([("s", 4, (-1, 0, 0, 1)), ("s", -4, (-1, 0, 1, 0))])
    fii = trig_polynomial([("c", 4, (0, -1, 1, 0)), ("c", -4, (0, -1, 0, 1))])
    for j in range(6):
        for p in "XYZ":
            background = {e + (0,): c for e, c in backgrounds[(j, p)].items()}
            target = add(background, fi if pullback(6, j, p)[2] == -1j else fii)
            assert moment(6, full_state, j, p) == target
    alpha, beta, gamma, phi = sp.symbols("alpha beta gamma phi", real=True)
    FI = sp.sin(phi - alpha) - sp.sin(gamma - alpha)
    FII = sp.cos(gamma - beta) - sp.cos(phi - beta)
    assert sp.diff(FI - FII, phi).subs({alpha: 0, beta: 0, gamma: 0, phi: sp.pi / 2}) == -1
    for branch in ({beta: 0, gamma: alpha}, {alpha: 0, gamma: beta}):
        assert sp.trigsimp((FI - FII).subs(branch, simultaneous=True).subs(phi, sp.pi / 2)) == 0
    return {"conditional_16_point_sums": conditional, "old_even_axis_n": [2, 4, 6, 8],
            "mother_n": [8, 10], "n6_exception": "only X3,X4; normalized -sin(alpha)sin(beta)/8",
            "n6_color_backgrounds": {f"{p}{j+1}": serial(poly) for (j, p), poly in backgrounds.items()},
            "n6_four_parameter_full_expectations": 18, "zero_phase_derivative": -1,
            "background_normalization": "listed Laurent numerators divide by 128; Appendix C B divides by 64"}


def kernels(n):
    C = circuit_integer(n)
    diagonal = sp.diag(*[sp.I ** f0(z) for z in range(1 << n)])
    return [diagonal.conjugate().T * C.T * pauli_matrix(n, j, p) * C * diagonal
            for j in range(n) for p in "XYZ"]


def derivative(K, h, order):
    return sp.expand(sum(K[w, z] * (sp.I * (h[z] - h[w])) ** order
                         for w in range(K.rows) for z in range(K.cols) if K[w, z]))


def jacobian(Ks):
    h = [sp.S.Zero] + list(sp.symbols("h1:" + str(Ks[0].rows)))
    return sp.Matrix([[derivative(K - Ks[0], h, 1).coeff(v) for v in h[1:]] for K in Ks[1:]])


def verify_low_dimensional_lines():
    K3 = kernels(3)
    J3 = jacobian(K3) / 16
    assert J3[:7, :].det() == sp.Rational(1, 4096)
    K4 = kernels(4)
    J4 = jacobian(K4)
    a, b, g, k = sp.symbols("a b g k", real=True)
    h = sp.Matrix([0, a, a, a-g, -a+b-g/2+k, -a+b-g/2+k, g, g,
                   a-g, a, b-g, b, g, g, k, k])
    basis = h[1:, 0].jacobian((a, b, g, k))
    assert J4.rank() == 11 and basis.rank() == 4 and J4 * basis == sp.zeros(11, 4)
    assert sp.factor(derivative(K4[1] - K4[0], h, 2)) == -4*g*(2*a-g)
    assert sp.factor(derivative(K4[4] - K4[0], h, 2)) == 8*g*(a-2*b+2*g)
    assert sp.factor(derivative(K4[3] - K4[0], h, 2).subs({a:g/2, b:5*g/4})) == -g*(g+4*k)
    obstruction = sp.factor(derivative(K4[1] - K4[0], h, 3).subs({a:g/2, b:5*g/4, k:-g/4}))
    assert obstruction == -39*g**3/4
    assert sp.expand(derivative(K4[3] - K4[0], h, 2).subs(g, 0) + 16*(a-b)*(a-b-k)) == 0
    A = {1, 2, 3, 8, 9, 10, 11}
    B = {1, 2, 3, 8, 9, 14, 15}
    C = {4, 5, 14, 15}
    all_moments(4, phase_state(4, [(int(z in A), int(z in C)) for z in range(16)]), {(1, 0):2, (-1, 0):2})
    all_moments(4, phase_state(4, [(int(z in A), int(z in B)) for z in range(16)]), {(1, 1):2, (-1, -1):2})
    return {"n3_Jacobian": [[str(v) for v in row] for row in J3.tolist()],
            "n3_minor": str(J3[:7, :].det()), "n4_Jacobian_rank": 11,
            "n4_kernel_basis": [[str(v) for v in row] for row in basis.tolist()],
            "n4_third_derivative_numerator": str(obstruction),
            "derivative_normalization": "n3 denominator 16, n4 denominator 32",
            "two_sufficient_planes": ["span(1_A,1_C)", "span(1_A,1_B)"],
            "masks": {"A":sorted(A), "B":sorted(B), "C":sorted(C)}}


def verify_curve():
    state = phase_state(4, CURVE_EXPONENTS)
    for j in range(4):
        for p in "XYZ":
            assert moment(4, state, j, p) == (CURVE_H if (j, p) in ((0, "X"), (3, "Y")) else CURVE_T)
    x, z = sp.symbols("x z", real=True)
    root = sp.sqrt(2) - 1
    F = -x**3*z**2+x**3*z-3*x**2*z**2-3*x**2*z-4*x**2+3*x*z**2+x*z+4*x+z**2-3*z
    sinb, cosb = 2*x/(1+x*x), (1-x*x)/(1+x*x)
    sind, cosd = -2*z/(1+z*z), (1-z*z)/(1+z*z)
    A, B, C = cosb*(1+2*sinb), 2*cosb+sinb+1, 2*sinb*cosb
    H = cosb + 2*sind*cosb + 4*sinb*cosb
    T = cosb*cosd - sinb*sind - sind
    assert sp.factor(H-T-2*(A*z*z-B*z+C)/(1+z*z)) == 0
    assert sp.factor(A*z*z-B*z+C-(x+1)*F/(1+x*x)**2) == 0
    def bernstein(poly, degree):
        poly = sp.Poly(sp.expand(poly.subs({x:root*x, z:root*z})), x, z)
        return [[sp.simplify(sum(poly.coeff_monomial(x**i*z**j)*sp.binomial(r,i)/sp.binomial(degree[0],i)
                                *sp.binomial(t,j)/sp.binomial(degree[1],j)
                                for i in range(r+1) for j in range(t+1)))
                 for t in range(degree[1]+1)] for r in range(degree[0]+1)]
    bx, bz = bernstein(sp.diff(F,x),(2,2)), bernstein(sp.diff(F,z),(3,1))
    assert all(v.is_positive is True for row in bx for v in row)
    assert all(v.is_negative is True for row in bz for v in row)
    assert sp.factor(F.subs(z,x)) == -x*(1+x*x)*(x*x+2*x-1)
    assert sp.simplify(F.subs({x:root,z:root})) == 0
    assert T.subs({x:0,z:0}) == 1
    assert sp.simplify(T.subs({x:root,z:root})-(1+1/sp.sqrt(2))) == 0
    return {"all_signed_Laurent_identities":12, "phase_masks":CURVE_EXPONENTS,
            "H_numerator":serial(CURVE_H), "T_numerator":serial(CURVE_T),
            "half_angle_polynomial":str(F),
            "Bernstein_Fx": [[str(v) for v in row] for row in bx],
            "Bernstein_Fz": [[str(v) for v in row] for row in bz],
            "endpoint_radius_ratios":["1","1+1/sqrt(2)"],
            "scope":"exact identities and interval sign certificates; the root and monotonicity argument is in Appendix D"}


def verify_inequivalence():
    x = sp.Symbol("x", nonzero=True)
    conjugate = lambda value: sp.conjugate(value).subs(sp.conjugate(x), 1/x)
    phases = [0,0,0,3,0,0,1,0,0,0,0,2,0,1,3,3]
    speeds = [0,1,-1,-1,0,1,0,0,-1,2,0,1,3,3,1,0]
    C = circuit_integer(4)
    v = C * sp.Matrix([sp.I**f*x**k for f,k in zip(phases,speeds)])
    assert sp.expand(sum(conjugate(a)*a for a in v)) == 32
    component = (x**3+x**-3+2*x+2*x**-1)/16
    signs = ((1,-1,-1),(1,1,1),(1,-1,1),(1,1,1))
    for j in range(4):
        for p, expected_sign in zip("XYZ", signs[j]):
            value = (v.applyfunc(conjugate).T * pauli_matrix(4,j,p,signed=False) * v)[0]/32
            assert sp.expand(value-expected_sign*component) == 0
    def purity(vector, keep):
        rest = [j for j in range(4) if j not in keep]
        matrix = sp.zeros(4)
        for integer, value in enumerate(vector):
            bs = bits(integer,4)
            row = 2*bs[keep[0]]+bs[keep[1]]
            col = 2*bs[rest[0]]+bs[rest[1]]
            matrix[row,col] = value
        rho = matrix * matrix.applyfunc(conjugate).T / 32
        return sp.factor(sp.trace(rho*rho))
    base = C * sp.Matrix([sp.I**f0(z) for z in range(16)])
    base_purities = [purity(base,keep) for keep in ((0,1),(0,2),(0,3))]
    assert base_purities == [sp.Rational(63,128),sp.Rational(39,128),sp.Rational(39,128)]
    total = sp.factor(sum(purity(v,keep) for keep in ((0,1),(0,2),(0,3))))
    P = x**6+2*x**4-2*x**3+2*x*x+1
    Q = (x*x-x+1)*(x*x+x+1)*(6*x**12-9*x**10+77*x**8-20*x**6+77*x**4-9*x*x+6)
    assert sp.factor(16*x**3*(component-sp.Rational(1,8))-P) == 0
    assert sp.factor(512*x**8*(total-sp.Rational(141,128))-Q) == 0
    resultant = sp.resultant(P,Q,x)
    assert resultant == 21153523695616
    return {"source":"Pauwels--Gisin, arXiv:2607.16020v1, Appendix C",
            "integer_base_phase":phases,"integer_speed":speeds,
            "parameter":"x=exp(i*pi*(1-tau)/3), 0<=tau<=1",
            "base_two_cut_purities":[str(v) for v in base_purities],
            "line_purity_sum":str(total),"radius_polynomial":str(P),"purity_polynomial":str(Q),
            "resultant":str(resultant)}


def verify_grams_and_partial_traces():
    curve_components = [[CURVE_H if (j,p) in ((0,"X"),(3,"Y")) else CURVE_T for p in "XYZ"] for j in range(4)]
    curve = check_full_measurement(4, CURVE_EXPONENTS, curve_components)
    unified = check_full_measurement(5, [(qfour(z,5)-int(z==0),) for z in range(32)], [[UNIFIED_TARGET]*3 for _ in range(5)])
    return {"curve_n4":curve,"unified_n5":unified,
            "curve_scope":"partial traces verified for independent b,delta; equality H=T follows from the quadratic certificate"}


def main():
    if not __debug__:
        raise RuntimeError("Run without Python -O; verification requires assertions.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("verification_results.json"))
    args = parser.parse_args()
    result = {"python":platform.python_version(), "sympy":sp.__version__,
              "arithmetic":"exact finite Laurent/Gaussian-integer and SymPy symbolic identities; no numerical tolerance", "checks":{}}
    jobs = [
        ("unified_kernel",verify_kernel_and_gates),
        ("Boolean_low_dimensions",verify_boolean_low_dimensions),
        ("mother_and_n6_colors",verify_mother_and_colors),
        ("low_dimensional_lines",verify_low_dimensional_lines),
        ("curved_family",verify_curve),
        ("inequivalence_certificate",verify_inequivalence),
        ("full_Gram_and_partial_traces",verify_grams_and_partial_traces),
    ]
    for name, task in jobs:
        start = time.perf_counter()
        print(f"RUN {name}", flush=True)
        result["checks"][name] = task()
        print(f"PASS {name} ({time.perf_counter()-start:.2f} s)", flush=True)
    result["status"] = "PASS"
    args.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    print(f"PASS all 7 checks; results: {args.output.name}", flush=True)


if __name__ == "__main__":
    main()
