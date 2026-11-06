"""所有长前缀割的双变量符号纯度；自由长度通过精确类别计数进入。"""
from four_copy import replica,mask,product_coeff
from collections import defaultdict
from itertools import product
from functools import lru_cache


def cats(lp):
    return [(0,0,(1,0)),(1,lp,(1,0)),(2,0,(-1-int(lp==0),1)),(2,1,(-int(lp==1),1))]


def mul(a,b):
    out=[0,0,0]
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out


@lru_cache(None)
def group(fm,side,lp):
    if lp == -1: return [(0,0,(1,0,0))]
    result=defaultdict(lambda:[0,0,0])
    for cy,py,wy in cats(lp):
        for cv,pv,wv in cats(lp):
            pm=mask(replica((py<<1)|pv,side))
            bd=0
            for r,cat in enumerate((cy,cv,cv if side else cy,cy if side else cv)):
                if cat==2 or cat!=((fm>>r)&1):bd|=1<<r
            for power,v in enumerate(mul(wy,wv)):result[pm,bd][power]+=v
    return [(pm,bd,tuple(poly)) for (pm,bd),poly in result.items() if any(poly)]


@lru_cache(None)
def groups(fm,basebad,la,lb):
    result=defaultdict(lambda:[0]*9)
    for pa,ba,wa in group(fm,1,la):
        for pb,bb,wb in group(fm,0,lb):
            dest=result[pa^pb,ba|bb|basebad]
            for i,a in enumerate(wa):
                for j,b in enumerate(wb):dest[3*i+j]+=a*b
    return [(pm,bd,tuple(p)) for (pm,bd),p in result.items() if any(p)]


def symbolic(la,lb):
    total=[[[0,0] for _ in range(9)] for _ in range(5)]
    for first,second,left,right,penult,last in product(range(4),repeat=6):
        reps=[replica(x,s) for x,s in zip((first,second,left,right,penult,last),(1,1,1,0,0,0))]
        rf,rs,ra,rb,rp,rl=reps
        fm=mask(rf);bd=0
        for r in reps[1:]:bd|=mask(r)^fm
        baseparity=mask(ra)^mask(rb)
        ends=tuple((rf[r],rs[r],rp[r],rl[r]) for r in range(4))
        sign=-1 if left in (1,2) and right in (1,2) else 1
        for pm,bad,weight in groups(fm,bd,la,lb):
            co=product_coeff(ends,baseparity^pm,bad,max(la,0)^max(lb,0))
            for k,(re,im) in enumerate(co):
                for power,v in enumerate(weight):
                    total[k][power][0]+=sign*v*re
                    total[k][power][1]+=sign*v*im
    assert all(im==0 for re,im in total[2])
    return [[re for re,im in total[2]],[2*re for re,im in total[3]],[-2*im for re,im in total[3]],[2*re for re,im in total[4]],[-2*im for re,im in total[4]]]
