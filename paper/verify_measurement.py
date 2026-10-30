"""从原相位和逐门作用核对通用奇数族；仅使用标准库高斯整数。"""
from collections import Counter
from math import comb
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
IROOTS = ((1, 0), (0, 1), (-1, 0), (0, -1))
QSET = {0, 5, 6, 7, 11, 12, 13, 14, 18, 20, 21, 23, 24, 25, 26, 31}


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def mul(a, b):
    return (a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0])


def conj(a):
    return (a[0], -a[1])


def bits(z, n):
    return [(z >> (n-j-1)) & 1 for j in range(n)]


def encode(v):
    return sum(b << (len(v)-j-1) for j, b in enumerate(v))


def fold(z, n):
    v = bits(z, n)
    return encode([v[0], sum(v[1:n-3:2]) % 2,
                   sum(v[2:n-2:2]) % 2, v[-2], v[-1]])


def qpoly(z):
    a, b, c, d, e = bits(z, 5)
    return (1+a+b+c+d+e+d*e+b*e+b*d+a*e+a*b*e) % 2


def seed_numerator(n, background=False):
    """Hadamard省略1/sqrt(2)，返回分母sqrt(2^(n+1))下的p+u q。"""
    phase = []
    for z in range(1 << n):
        weight = z.bit_count()
        f0 = sum((-1)**r*comb(weight, r) for r in range(2, weight+1)) % 4
        assert f0 == (0 if z == 0 else (weight-1) % 4)
        d = qpoly(fold(z, n)) if background or z else 0
        coeff = [(0, 0), (0, 0)]
        coeff[d] = IROOTS[(weight if background else f0) % 4]
        phase.append(coeff)
    hadamard = []
    for y in range(1 << n):
        sign = (-1 if y & 1 else 1, 0)
        hadamard.append([add(phase[y & ~1][d], mul(sign, phase[y | 1][d])) for d in (0, 1)])
    output = [None] * (1 << n)
    for y, coeff in enumerate(hadamard):
        x = y
        # 右侧的 n -> n-1 先作用，逐门直接置换。
        for control in range(n, 1, -1):
            if x & (1 << (n-control)):
                x ^= 1 << (n-control+1)
        output[x] = coeff
    return output


def expectation(state, n, j, axis):
    out = {-1: (0, 0), 0: (0, 0), 1: (0, 0)}
    bit = 1 << (n-j)
    for z, right in enumerate(state):
        sign = -1 if z & bit else 1
        target = z if axis == 'Z' or axis == 'I' else z ^ bit
        scale = (sign, 0) if axis == 'Z' else (0, sign) if axis == 'Y' else (1, 0)
        for left_degree in (0, 1):
            for right_degree in (0, 1):
                value = mul(conj(state[target][left_degree]), mul(scale, right[right_degree]))
                degree = right_degree-left_degree
                out[degree] = add(out[degree], value)
    return out


def main():
    assert {z for z in range(32) if qpoly(z)} == QSET
    records = []
    for n in (5, 7, 9, 11):
        state = seed_numerator(n)
        background = seed_numerator(n, True)
        denominator = 1 << (n+1)
        assert expectation(state, n, 1, 'I') == {-1:(0, 0), 0:(denominator, 0), 1:(0, 0)}
        for j in range(1, n+1):
            for axis in 'XYZ':
                eta = -1 if j == n and axis == 'Y' else 1
                actual = expectation(state, n, j, axis)
                expected = {-1:(0, -2*eta), 0:(4*eta, 0), 1:(0, 2*eta)}
                assert actual == expected, (n, j, axis, actual)
                assert all(v == (0, 0) for v in expectation(background, n, j, axis).values())
        support = sum(qpoly(fold(z, n)) for z in range(1, 1 << n))
        assert support == (1 << (n-1))-1
        for j in range(1, n+1):
            counts = Counter()
            for e in range(1 << (n-1)):
                ev = [0] + bits(e, n-1) + [0]
                qj = ev[j-1] ^ ev[j]
                for s in (0, 1):
                    counts[2*qj+s] += 1
            assert list(counts.values()) == [1 << (n-2)]*4
        records.append(dict(n=n, norm_denominator=denominator, support=support,
                            all_local_laurent_coefficients='eta*(4+2*i*u-2*i/u)',
                            background='all zero', vertex_multiplicity=1 << (n-2)))
    result = dict(status='PASS', direct_gate_checks=records)
    (HERE / 'exact_results.json').write_text(json.dumps(result, indent=2), encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
