"""全n GME的自足精确证书：整数振幅、奇偶压缩与符号长度计数。"""

from collections import deque
from fractions import Fraction
from itertools import combinations
from math import isqrt
from pathlib import Path
from functools import lru_cache
import json
import time

HERE = Path(__file__).resolve().parent
DATA = HERE / 'data'


def add(a, b):
    return (a[0] + b[0], a[1] + b[1])


def mul(a, b):
    return (a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def conj(a):
    return (a[0], -a[1])


def scale(a, s):
    return (s * a[0], s * a[1])


def span(vectors):
    answer = {0}
    for v in vectors:
        answer |= {x ^ v for x in tuple(answer)}
    return frozenset(answer)


def parity(x):
    return x.bit_count() & 1


def log2_exact(n):
    assert n > 0 and n & (n - 1) == 0
    return n.bit_length() - 1


@lru_cache(None)
def step(space, side, nextside, column, nextcolumn):
    # 显式枚举所有输入元素和新位；投影前后基数比就是统一纤维数。
    inputs = {x | (v << 10) for x in space for v in range(1 + nextside)}
    if not side:
        inputs = {x for x in inputs if ((x >> 8) ^ (x >> 10) ^ parity(x & column)) & 1 == 0}
    output = set()
    for x in inputs:
        v = (x >> 10) & 1
        output.add((x & 255) ^ ((nextcolumn << 4) if v else 0) | (((x >> 9) & 1) << 8) | (v << 9))
    lost = log2_exact(len(inputs) // len(output))
    assert len(inputs) == len(output) * 2 ** lost
    return frozenset(output), nextside - lost


def terminal(space, side):
    inputs = space if side else {x for x in space if ((x >> 8) ^ parity(x & 4)) & 1 == 0}
    output = frozenset(x & 255 for x in inputs)
    lost = log2_exact(len(inputs) // len(output))
    assert len(inputs) == len(output) * 2 ** lost
    return output, -lost


def edge(rank, odd, side, nextside):
    return (rank, 0) if side == nextside else (rank + 1 - odd, 1 - odd)


def closure():
    queue = deque()
    seen = {}
    finals = set()
    for a in (0, 1):
        initial = span([1, 2, 4, 8] + [576] * a)
        for b in (0, 1):
            sb, eb = step(initial, a, b, 4, 1)
            rb, ob = edge(0, 0, a, b)
            for c in (0, 1):
                sc, ec = step(sb, b, c, 1, 8)
                rc, oc = edge(rb, ob, b, c)
                state = (sc, a + eb + ec, rc, oc, c, 1)
                if state not in seen:
                    seen[state] = ''.join('A' if x else 'B' for x in (a,b,c))
                    queue.append(state)
    while queue:
        state = queue.popleft()
        space, exponent, rank, odd, side, lengthparity = state
        for a in (0, 1):
            r1, o1 = edge(rank, odd, side, a)
            if r1 > 4:
                continue
            s1, e1 = step(space, side, a, 8, 2)
            for b in (0, 1):
                r2, _ = edge(r1, o1, a, b)
                if r2 <= 4:
                    s2, e2 = step(s1, a, b, 2, 4)
                    sf, ef = terminal(s2, b)
                    finals.add((sf, exponent + e1 + e2 + ef, r2, lengthparity))
        for a in (0, 1):
            r1, o1 = edge(rank, odd, side, a)
            if r1 <= 4:
                s1, e1 = step(space, side, a, 8, 8)
                nextstate = (s1, exponent + e1, r1, o1, a, 1 - lengthparity)
                if nextstate not in seen:
                    seen[nextstate] = seen[state] + ('A' if a else 'B')
                    queue.append(nextstate)
    return seen, finals


def kernel(v):
    x,b,c,s = [(v >> j) & 1 for j in (3,2,1,0)]
    return (1 ^ ((1 ^ c) & (x ^ b))) if s == 0 else b ^ (x & c)


def coefficients(nparity):
    result = {}
    for h in range(16):
        hx,hb,hc,hs = [(h >> j) & 1 for j in (3,2,1,0)]
        word = (hx ^ hb ^ hs) + 2 * (hx ^ (hc if nparity else hb)) + 4 * (hx ^ hs) + 8 * (hb ^ hc)
        walsh = sum(1 - 2 * (kernel(v) ^ parity(h & v)) for v in range(16))
        phase = (0, -1) if hs else (1, 0)
        result[word] = (scale(phase, 16 * (h == 0) + walsh), scale(phase, 16 * (h == 0) - walsh))
    assert len(result) == 16
    return result


def squared_tables(nparity):
    coefficient = coefficients(nparity)
    table = []
    max_s = max_p = 0
    for dk in range(256):
        d, k = dk & 15, dk >> 4
        s = [(0, 0)] * 3
        for l in range(16):
            left, right = coefficient[l], coefficient[l ^ d]
            sign = 1 - 2 * parity((l ^ d) & k)
            for i in range(2):
                for j in range(2):
                    s[i-j+1] = add(s[i-j+1], scale(mul(left[i], conj(right[j])), sign))
        p = [(0,0)] * 5
        for i in range(3):
            for j in range(3):
                p[i-j+2] = add(p[i-j+2], mul(s[i], conj(s[j])))
        assert p[0] == conj(p[4]) and p[1] == conj(p[3]) and p[2][1] == 0
        max_s = max(max_s, *(abs(x) for term in s for x in term))
        max_p = max(max_p, *(abs(x) for term in p for x in term))
        table.append(p)
    return table, max_s, max_p


def fourier(space, exponent, table):
    p = [tuple(sum(table[x][i][part] for x in space) for part in (0,1)) for i in range(5)]
    assert p[0] == conj(p[4]) and p[1] == conj(p[3]) and p[2][1] == 0
    numerator = (p[2][0], 2*p[3][0], -2*p[3][1], 2*p[4][0], -2*p[4][1])
    return numerator, 2 ** (20 + exponent)


def bound(numer, denom):
    def cs(x):
        q = isqrt(x)
        return q + (q*q != x)
    a,b,c,d,e = numer
    return Fraction(a + cs(b*b+c*c) + cs(d*d+e*e), denom)


def check_closure():
    states, finals = closure()
    producer = DATA
    expected_states = json.loads((producer / 'closure_states.json').read_text(encoding='utf-8'))
    expected_finals = json.loads((producer / 'closure_certificate.json').read_text(encoding='utf-8'))['entries']
    assert set(states) == {(span(r['basis']),r['exponent'],r['crossrank'],r['edge_odd'],int(r['current_a']),r['parity']) for r in expected_states}
    assert finals == {(span(r['basis']),r['exponent'],r['crossrank'],r['parity']) for r in expected_finals}
    tables = [squared_tables(p) for p in (0,1)]
    maxima = {}
    for row in expected_finals:
        numer, denom = fourier(span(row['basis']), row['exponent'], tables[row['parity']][0])
        assert tuple(row['numerator']) == numer and row['denominator'] == denom
        upper = bound(numer, denom)
        assert str(upper) == row['upper_bound']
        rank = row['crossrank']
        maxima[rank] = max(maxima.get(rank, Fraction(0)), upper)
        if rank >= 2:
            assert upper <= Fraction(3,8)
    return dict(states=len(states), signatures=len(finals), maxima={k:str(v) for k,v in maxima.items()}, max_s=[t[1] for t in tables], max_p=[t[2] for t in tables], exponent_range=[min(s[1] for s in states),max(s[1] for s in states)], independent_method='explicit GF2 element sets and unbounded Python integer Gaussian arithmetic')


def raw_amplitudes(n, defect=True):
    # 不调用生产相位或门序函数，以原始H和逐门CNOT定义构造整数振幅。
    raw = [[(0,0)] * (1 << n) for _ in range(2)]
    roots = [(1,0),(0,1),(-1,0),(0,-1)]
    for index in range(1 << n):
        z = [(index >> (n-1-j)) & 1 for j in range(n)]
        feature = 8*(z[0]^z[-2]) + 4*(sum(z[1:n-2:2])%2) + 2*(sum(z[2:n-2:2])%2) + (z[0]^z[-1])
        d = kernel(feature) - int(defect and index == 0)
        phase = roots[(0 if index == 0 else sum(z)-1)%4] if defect else roots[sum(z)%4]
        for last in (0,1):
            output = z[:-1]+[last]
            for control in range(n-1,0,-1):
                output[control-1] ^= output[control]
            y = sum(bit << (n-1-j) for j,bit in enumerate(output))
            raw[d][y] = add(raw[d][y], scale(phase,(-1)**(z[-1]*last)))
    return raw


def coefficient_purity(raw, n, keep):
    # dtype=object中的每个元素都是任意精度Python整数；矩阵积也没有浮点步骤。
    import numpy as np
    rest = tuple(j for j in range(n) if j not in keep)
    matrices = []
    for polynomial_term in raw:
        matrices.append(tuple(np.array([v[p] for v in polynomial_term], dtype=object).reshape([2]*n).transpose(keep+rest).reshape(1<<len(keep),-1) for p in (0,1)))
    def mm(left, right):
        ar,ai = left; br,bi = right
        return ar@br.T+ai@bi.T, ai@br.T-ar@bi.T
    aa = mm(matrices[0],matrices[0]); bb = mm(matrices[1],matrices[1]); ab=mm(matrices[0],matrices[1]); ba=mm(matrices[1],matrices[0])
    reduced = {-1:ab, 0:(aa[0]+bb[0],aa[1]+bb[1]), 1:ba}
    polynomial=[]
    for frequency in range(-2,3):
        real=imag=0
        for i,(ar,ai) in reduced.items():
            for j,(br,bi) in reduced.items():
                if i+j==frequency:
                    real+=int(np.sum(ar*br.T-ai*bi.T)); imag+=int(np.sum(ar*bi.T+ai*br.T))
        polynomial.append((real,imag))
    assert polynomial[0]==conj(polynomial[4]) and polynomial[1]==conj(polynomial[3]) and polynomial[2][1]==0
    return (polynomial[2][0],2*polynomial[3][0],-2*polynomial[3][1],2*polynomial[4][0],-2*polynomial[4][1]), 2**(2*n+2)


def check_finite():
    saved=json.loads((DATA/'finite_coefficients.json').read_text(encoding='utf-8'))['sizes']
    result={}
    for n in range(5,10):
        raw=raw_amplitudes(n)
        expected={tuple(j-1 for j in row['qubits']):row for row in saved[str(n)]['cuts']}
        cuts=[keep for size in range(2,n//2+1) for keep in combinations(range(n),size) if size*2 != n or 0 in keep]
        assert set(cuts)==set(expected)
        maximum=Fraction(0)
        for keep in cuts:
            numerator,denominator=coefficient_purity(raw,n,keep)
            row=expected[keep]
            assert tuple(row['trig_numerator'])==numerator and row['denominator']==denominator,(n,keep)
            maximum=max(maximum,bound(numerator,denominator))
        assert maximum < Fraction(1,2)
        result[n]=dict(cuts=len(cuts),upper_bound=str(maximum),all_exact_coefficients_match=True)
        print('finite',n,result[n],flush=True)
    return result


def check_graph_bridge():
    # 全振幅、仿射u两个系数逐项精确比较，整体e^{iπ/4}由(1+i)/sqrt2处理。
    checked=0
    for n in range(5,11):
        raw=raw_amplitudes(n,defect=False)
        coefficient=coefficients(n%2)
        ws=[4,1]+[8]*(n-4)+[2,4]
        for y in range(1<<n):
            bits=[(y>>(n-1-j))&1 for j in range(n)]
            sign=(-1)**(sum(bits[j]*bits[j+1] for j in range(n-1))+sum(bits[1:-1]))
            local=(0,sign) if bits[0] else (sign,0)
            common=mul((1,1),local)
            character=0
            for b,w in zip(bits,ws):
                if b: character ^= w
            for degree in range(2):
                value=(0,0)
                for d in range(16):
                    value=add(value,scale(coefficient[d][degree],1-2*parity(d&character)))
                assert mul(common,value)==scale(raw[degree][y],32),(n,y,degree)
                checked+=1
    return dict(n_range=[5,10],exact_affine_coefficient_checks=checked)


def check_compression():
    from collections import Counter
    folder=DATA
    listed=set((folder/'representatives.txt').read_text(encoding='utf-8').splitlines())
    representatives=set()
    # 独立枚举理论长度界内的全部颜色串；从跨边连通分量计算秩。
    for n in range(5,20):
        for mask in range(1,1<<(n-1)):
            if min(mask.bit_count(),n-mask.bit_count())<2:
                continue
            side=[0]+[(mask>>j)&1 for j in range(n-1)]
            crossings=[j for j in range(n-1) if side[j]!=side[j+1]]
            rank=0; previous=-2; run=0
            for j in crossings:
                if j!=previous+1:
                    rank+=(run+1)//2;run=0
                run+=1;previous=j
            rank+=(run+1)//2
            if not 2<=rank<=4 or n>3*rank+7:
                continue
            protected={0,1,n-2,n-1}|set(crossings)|{j+1 for j in crossings}
            groups=[[j for j in range(2,n-2) if j not in protected and side[j]==color] for color in (0,1)]
            retained={g[0] for g in groups if g}
            if (n-len(protected)-len(retained))%2:
                retained.add(next(g[1] for g in groups if len(g)>1))
            word=''.join(str(side[j]) for j in sorted(protected|retained))
            assert len(word)%2==n%2 and 5<=len(word)<=3*rank+7
            representatives.add(word)
    assert representatives==listed
    tables=[squared_tables(p)[0] for p in (0,1)]
    classes=Counter()
    rankcounts=Counter()
    maxima={}
    for word in listed:
        n=len(word); colors=list(map(int,word)); ws=[4,1]+[8]*(n-4)+[2,4]
        space=span([1,2,4,8]+[576]*colors[0]); exponent=colors[0]; rank=odd=0
        for j in range(n-1):
            space, delta=step(space,colors[j],colors[j+1],ws[j],ws[j+1])
            exponent+=delta
            rank,odd=edge(rank,odd,colors[j],colors[j+1])
        space,delta=terminal(space,colors[-1]); exponent+=delta
        numer,denom=fourier(space,exponent,tables[n%2])
        coeff=tuple(Fraction(v,denom) for v in numer)
        assert coeff[0]+sum(map(abs,coeff[1:]))<=Fraction(3,8)
        upper=coeff[0]+sum(map(abs,coeff[1:]))
        maxima[rank]=max(maxima.get(rank,Fraction(0)),upper)
        classes[coeff]+=1;rankcounts[rank]+=1
    saved=json.loads((folder/'representative_coefficients.json').read_text(encoding='utf-8'))
    expected=Counter({tuple(map(Fraction,c['coefficients'])):c['count'] for c in saved['classes']})
    assert classes==expected
    assert maxima=={2:Fraction(3,8),3:Fraction(33,128),4:Fraction(33,256)}
    return dict(representatives=len(listed),fourier_classes=len(classes),rank_counts=dict(rankcounts),maxima={k:str(v) for k,v in maxima.items()},all_class_coefficients_and_multiplicities_match=True)


def check_rank_one():
    from itertools import product
    import prove_prefix
    import prove_p12
    long_saved=json.loads((DATA/'prefix_symbolic.json').read_text(encoding='utf-8'))['cases']
    for la,lb in product((0,1),repeat=2):
        assert prove_prefix.symbolic(la,lb)==long_saved[f'LAmod2={la},LBmod2={lb}']
    short_saved=json.loads((DATA/'prefix_short_symbolic.json').read_text(encoding='utf-8'))
    for case in ((-1,0),(-1,1),(0,-1),(1,-1),(-1,-1)):
        assert prove_prefix.symbolic(*case)==short_saved[str(case)]
    two_saved=json.loads((DATA/'p12_symbolic.json').read_text(encoding='utf-8'))['cases']
    for suffix,nparity in product((False,True),(0,1)):
        assert prove_p12.symbolic(nparity,suffix)==two_saved[f'suffix={suffix},nmod2={nparity}']
    # 端点值由全部n>=6的符号系数逐次幂相消得到。
    two=prove_p12.symbolic(0,False)
    assert [a+b-c for a,b,c in zip(two[0],two[2],two[3])]==[0,0,5120]
    numerator,denominator=coefficient_purity(raw_amplitudes(5),5,(0,1))
    assert Fraction(numerator[0]+numerator[2]-numerator[3],denominator)==Fraction(11,32)
    # n=10的迹距离界平方严格小于(1/8)^2；随后随n单调减小。
    assert 16*Fraction(1,1024)*Fraction(1023,1024)<Fraction(1,64)
    return dict(long_parity_cases=4,empty_group_cases=5,two_bit_cases=4,
                endpoint_p12={'n=5':'11/32','n>=6':'5/16'},tail_n10=True)


if __name__=='__main__':
    start=time.time()
    result={}
    for name,check in [('rank_one',check_rank_one),('closure',check_closure),
                       ('graph_bridge',check_graph_bridge),('finite',check_finite),
                       ('compression',check_compression)]:
        result[name]=check()
        print(name,result[name],flush=True)
    result['seconds']=time.time()-start
    (HERE/'verification_results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('All exact checks passed.',flush=True)


