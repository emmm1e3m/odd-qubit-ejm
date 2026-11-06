"""用任意长度同侧段的精确计数，符号证明全部n>=6的p12公式。"""
from four_copy import replica,mask,product_coeff


def multiply(a,b):
    out=[0,0,0]
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out


def symbolic(parity_n, suffix=False):
    # 在首个中间比特y3之外尚有L=n-5位；K=2^(L-1)=2^(n-6)。
    lp=1-parity_n
    cats=[(0,0,(1,0)),(1,lp,(1,0)),(2,0,(-1-int(lp==0),1)),(2,1,(-int(lp==1),1))]
    total=[[[0,0] for _ in range(3)] for _ in range(5)]
    for first in range(4):
        rf=replica(first,1);fm=mask(rf)
        for second in range(4):
            rs=replica(second,1);b0=mask(rs)^fm
            for third in range(4):
                rt=replica(third,int(suffix));tm=mask(rt);b1=b0|(tm^fm)
                sign=1 if suffix else (-1 if second in (1,2) and third in (1,2) else 1)
                for cy,py,wy in cats:
                    for cv,pv,wv in cats:
                        weight=multiply(wy,wv)
                        midp=tm^mask(replica((py<<1)|pv,int(suffix)))
                        bd=b1
                        for r,cat in enumerate((cy,cv,cv if suffix else cy,cy if suffix else cv)):
                            if cat==2 or cat!=rf[r]:bd|=1<<r
                        for penult in range(4):
                            rp=replica(penult,0)
                            for last in range(4):
                                rl=replica(last,0)
                                final_bad=bd|(mask(rp)^fm)|(mask(rl)^fm)
                                ends=tuple((rf[r],rs[r],rp[r],rl[r]) for r in range(4))
                                co=product_coeff(ends,midp,final_bad,parity_n)
                                for k,(re,im) in enumerate(co):
                                    for power,v in enumerate(weight):
                                        sg=sign*(-1 if suffix and third in (1,2) and penult in (1,2) else 1)
                                        total[k][power][0]+=sg*v*re
                                        total[k][power][1]+=sg*v*im
    assert all(im==0 for re,im in total[2])
    trig=[ [re for re,im in total[2]], [2*re for re,im in total[3]],[-2*im for re,im in total[3]], [2*re for re,im in total[4]],[-2*im for re,im in total[4]] ]
    expected=[[60,-64,5632],[0,-128,2048],[-64,0,0],[-4,-64,512],[0,0,0]]
    assert trig==expected,(parity_n,trig)
    return trig
