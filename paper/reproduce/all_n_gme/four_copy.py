"""四副本局部系数；高斯整数表示为两个任意精度整数。"""
from functools import lru_cache


def kernel(x, b, c, s):
    return (1 ^ ((1 ^ c) & (x ^ b))) if s == 0 else b ^ (x & c)


def replica(pair, side):
    y, v = pair >> 1, pair & 1
    return (y, v, v if side else y, y if side else v)


def mask(bits):
    return sum(b << j for j, b in enumerate(bits))


def h_coeff(endpoints, parity, constant, n_parity):
    a, b, c, d = endpoints
    x = a ^ b ^ c ^ d
    B = b ^ parity ^ (c if n_parity == 0 else 0)
    C = parity ^ (c if n_parity else 0)
    f0 = kernel(x, B, C, a ^ b)
    f1 = kernel(x, B, C, a ^ b ^ 1)
    result = [[0, 0], [0, 0]]
    result[f0][0] += 1
    result[f1][1] += -1 if d else 1
    if constant:
        result[0][1] += 1
        result[1][0] -= 1
    return result


@lru_cache(None)
def product_coeff(endpoints, parity, bad, n_parity):
    # 后两个副本取共轭；u的次数因此带负号。
    polynomial = {0: (1, 0)}
    for r in range(4):
        h = h_coeff(endpoints[r], (parity >> r) & 1,
                    not ((bad >> r) & 1), n_parity)
        result = {}
        for k, (ar, ai) in polynomial.items():
            for degree, (br, bi) in enumerate(h):
                if r >= 2:
                    bi = -bi
                power = k + (degree if r < 2 else -degree)
                re, im = result.get(power, (0, 0))
                result[power] = (re + ar * br - ai * bi,
                                 im + ar * bi + ai * br)
        polynomial = result
    return tuple(polynomial.get(k, (0, 0)) for k in range(-2, 3))
