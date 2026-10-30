"""任意奇数比特统一构造的有限 Walsh 证书（仅使用 Python 标准库）。"""
import json
from pathlib import Path

Q_SUPPORT = {0,5,6,7,11,12,13,14,18,20,21,23,24,25,26,31}
Q = tuple(int(x in Q_SUPPORT) for x in range(32))


def mask(n, positions):
    return sum(1 << (n-j) for j in positions)


def rows(n):
    return [mask(n,[1]), mask(n,range(2,n-2,2)),
            mask(n,range(3,n-1,2)),mask(n,[n-1]),mask(n,[n])]


def fold(n,z):
    out=0
    for row in rows(n):
        out=2*out+((z&row).bit_count()%2)
    return out


def row_character(n,h):
    for eta in range(32):
        image=0
        for j,row in enumerate(rows(n)):
            if eta & (1<<(4-j)):
                image ^= row
        if image==h:
            return eta
    return None


def pullback(n,j,axis):
    """返回翻转p、字符b、i的指数k；最后一个Y已取负号。"""
    if axis=='X':
        return (mask(n,[j-1,j] if 1<j<n else [1] if j==1 else [n-1]),
                0 if j<n else mask(n,[n]),0)
    if axis=='Z':
        return mask(n,[n]),mask(n,range(j,n)),0
    if j<n:
        return mask(n,[j-1,j,n] if j>1 else [1,n]),mask(n,range(j,n)),1
    return mask(n,[n-1,n]),mask(n,[n]),1


def certificate(a,eta):
    totals={-1:0,0:0,1:0}
    counts={-1:0,0:0,1:0}
    for x in range(32):
        d=Q[x]-Q[x^a]
        totals[d]+=(-1)**((eta&x).bit_count()%2)
        counts[d]+=1
    return [totals[d] for d in [-1,0,1]], [counts[d] for d in [-1,0,1]]


def main():
    records=[]
    for j in range(1,6):
        for axis in 'XYZ':
            p,b,k=pullback(5,j,axis)
            eta=row_character(5,p^b)
            totals,counts=certificate(p,eta)
            assert totals==[0,0,0]
            records.append(dict(label=f'{axis}{j}',a=p,eta=eta,
                gamma_exponent=(k-p.bit_count())%4,
                signed_counts=totals,counts=counts))
    totals,counts=certificate(13,7)
    assert totals==[0,0,0]
    records.append(dict(label='K (n=7, Y4)',a=13,eta=7,gamma_exponent=2,
                        signed_counts=totals,counts=counts))

    survivors={}
    for n in [5,7,9,11]:
        live=[]
        for j in range(1,n+1):
            for axis in 'XYZ':
                p,b,k=pullback(n,j,axis)
                a=fold(n,p)
                gamma=(k-p.bit_count())%4
                assert (gamma,Q[a]) in [(3,0),(2,1)]
                eta=row_character(n,p^b)
                if eta is not None:
                    assert certificate(a,eta)[0]==[0,0,0]
                    live.append(dict(label=f'{axis}{j}',a=a,eta=eta))
        survivors[n]=live
    output=dict(Q_support=sorted(Q_SUPPORT),finite_certificate=records,
                representative_survivors=survivors,
                status='All 16 exact Walsh certificates vanish.')
    path=Path(__file__).with_name('certificate.json')
    path.write_text(json.dumps(output,indent=2),encoding='utf-8')
    print(output['status'])
    for record in records:
        print(record['label'], record['a'], record['eta'],
              record['signed_counts'],record['counts'])
    for n,live in survivors.items():
        print('n=',n,'surviving characters:',','.join(x['label'] for x in live))

if __name__=='__main__':
    main()
