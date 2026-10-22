# Usage: python3 platonic_gen.py && python3 platonic_emit_lean.py ../EulersGem/PlatonicSolids
# Exact data generator for the five Platonic solids over Z[phi] (phi^2 = phi + 1).
from fractions import Fraction as Fr
from itertools import combinations, product
import json, sys

class Q:  # a + b*phi, a,b rational
    __slots__=('a','b')
    def __init__(s,a=0,b=0): s.a=Fr(a); s.b=Fr(b)
    def __add__(s,o): o=q(o); return Q(s.a+o.a,s.b+o.b)
    __radd__=__add__
    def __neg__(s): return Q(-s.a,-s.b)
    def __sub__(s,o): return s+(-q(o))
    def __rsub__(s,o): return q(o)-s
    def __mul__(s,o): o=q(o); return Q(s.a*o.a+s.b*o.b, s.a*o.b+s.b*o.a+s.b*o.b)
    __rmul__=__mul__
    def inv(s):
        # (a+b phi)^-1 ; conj: phi -> 1-phi ; norm = (a+b phi)(a+b-b phi) = a^2+ab-b^2
        n = s.a*s.a + s.a*s.b - s.b*s.b
        return Q((s.a+s.b)/n, -s.b/n)
    def __truediv__(s,o): return s*q(o).inv()
    def __eq__(s,o): o=q(o); return s.a==o.a and s.b==o.b
    def __hash__(s): return hash((s.a,s.b))
    def f(s): return float(s.a)+float(s.b)*1.618033988749895
    def sgn(s):
        p=2*s.a+s.b; qq=s.b
        if p==0 and qq==0: return 0
        if p>=0 and qq>=0: return 1
        if p<=0 and qq<=0: return -1
        if p>0: return 1 if p*p>5*qq*qq else -1
        return 1 if 5*qq*qq>p*p else -1
    def __repr__(s): return f"({s.a}+{s.b}φ)"
def q(x): return x if isinstance(x,Q) else Q(x,0)
PHI=Q(0,1); IPHI=Q(-1,1)
def vadd(u,v): return tuple(a+b for a,b in zip(u,v))
def vsub(u,v): return tuple(a-b for a,b in zip(u,v))
def vsc(c,u): return tuple(c*a for a in u)
def dot(u,v): return u[0]*v[0]+u[1]*v[1]+u[2]*v[2]
def cross(u,v): return (u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0])
def iszero(u): return all(a==0 for a in u)

def cyc(p): x,y,z=p; return [(x,y,z),(z,x,y),(y,z,x)]
def solids():
    S={}
    S['tetrahedron']=[tuple(map(q,t)) for t in [(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)]]
    S['cube']=[tuple(map(q,t)) for t in product([1,-1],repeat=3)]
    S['octahedron']=[tuple(map(q,t)) for t in [(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)]]
    ico=[]
    for s1,s2 in product([1,-1],repeat=2):
        for p in cyc((q(0),q(s1),s2*PHI)): ico.append(p)
    S['icosahedron']=ico
    dod=[tuple(map(q,t)) for t in product([1,-1],repeat=3)]
    for s1,s2 in product([1,-1],repeat=2):
        for p in cyc((q(0),s1*IPHI,s2*PHI)): dod.append(p)
    S['dodecahedron']=dod
    return S

def analyse(name,V):
    n=len(V)
    assert len(set(V))==n
    facets=set()
    for i,j,k in combinations(range(n),3):
        nn=cross(vsub(V[j],V[i]),vsub(V[k],V[i])); assert not iszero(nn)
        sg=[dot(nn,vsub(V[u],V[i])).sgn() for u in range(n)]
        if 1 in sg and -1 in sg: continue
        facets.add(tuple(u for u in range(n) if sg[u]==0))
    facets=sorted(facets)
    edges=sorted({tuple(sorted(set(f)&set(g))) for f,g in combinations(facets,2) if len(set(f)&set(g))==2})
    # order facet vertices: keep sorted index lists
    return facets,edges

def pair_cert(V,i,j):
    n=len(V); m2=vadd(V[i],V[j])  # target 2*midpoint
    others=[u for u in range(n) if u not in (i,j)]
    # try 2-point: V[u]+V[w]=m2
    for u,w in combinations(others,2):
        if vadd(V[u],V[w])==m2: return [(u,Q(1)),(w,Q(1))],1
    # general: find lambda over up to 4 points with sum lam*V = m2/2, sum lam = 1, lam>=0
    target=vsc(Q(Fr(1,2)),m2)
    best=sorted(others,key=lambda u: -dot(V[u],target).f())
    cand=best
    for k in (3,4):
      for S in combinations(cand,k):
        # solve: sum lam_s (V_s) = target, sum lam_s = 1 ; k unknowns, 4 equations
        rows=[[V[s][c] for s in S]+[target[c]] for c in range(3)]+[[Q(1)]*k+[Q(1)]]
        sol=solve(rows,k)
        if sol is None: continue
        if all(x.sgn()>=0 for x in sol):
            # convert: D*(V_i+V_j) = sum nu V ; nu = 2*D*lam ; choose D=common denominator
            den=1
            for x in sol:
                for r in (x.a,x.b): den=den*r.denominator//__import__('math').gcd(den,r.denominator)
            nu=[(s,x*(2*den)) for s,x in zip(S,sol) if not x==0]
            for s,x in nu: assert x.a.denominator==1 and x.b.denominator==1
            return nu,den
    return None

def solve(rows,k):
    # Gaussian elimination over Q(phi); rows: m equations, k unknowns + rhs; return unique solution or None
    M=[r[:] for r in rows]; m=len(M); piv=[]; r=0
    for c in range(k):
        p=next((x for x in range(r,m) if not M[x][c]==0),None)
        if p is None: return None
        M[r],M[p]=M[p],M[r]
        inv=M[r][c].inv(); M[r]=[x*inv for x in M[r]]
        for x in range(m):
            if x!=r and not M[x][c]==0:
                f=M[x][c]; M[x]=[a-f*b for a,b in zip(M[x],M[r])]
        piv.append(c); r+=1
    for x in range(r,m):
        if not M[x][k]==0: return None
    return [M[i][k] for i in range(k)]

def refl(nrm,x):
    # x - 2<n,x>/<n,n> n
    return vsub(x, vsc(Q(2)*dot(nrm,x)/dot(nrm,nrm), nrm))

def generators(V,facets,edges):
    n=len(V)
    e0=next(e for e in edges if 0 in e); a=e0[1] if e0[0]==0 else e0[0]
    f0=next(f for f in facets if set(e0)<=set(f))
    # neighbour b of 0 in f0 other than a
    b=next(e[0]+e[1]-0 for e in edges if 0 in e and set(e)<=set(f0) and set(e)!=set(e0))
    gens=[vsub(V[0],V[a]), vsub(V[a],V[b]), cross(V[0],V[a])]
    perms=[]
    for g in gens:
        pi=[]
        for u in range(n):
            y=refl(g,V[u]); w=V.index(y); pi.append(w)
        perms.append(pi)
    base=(0,tuple(sorted(e0)),tuple(sorted(f0)))
    return gens,perms,base

def act(pi,fl):
    i,e,f=fl; return (pi[i],tuple(sorted(pi[x] for x in e)),tuple(sorted(pi[x] for x in f)))

def bfs(perms,base):
    words={base:[]}; frontier=[base]
    while frontier:
        nf=[]
        for fl in frontier:
            for t,pi in enumerate(perms):
                g=act(pi,fl)
                if g not in words: words[g]=[t]+words[fl]  # apply t after word -> word list applied right-to-left? see lean
                nf.append(g) if g not in [x for x in nf] and len(words[g])==len(words[fl])+1 else None
        frontier=[x for x in nf]
        frontier=list(dict.fromkeys(frontier))
    return words

if __name__=='__main__':
    out={}
    for name,V in solids().items():
        F,E=analyse(name,V)
        gens,perms,base=generators(V,F,E)
        W=bfs(perms,base)
        flags=[(i,e,f) for e in E for f in F if set(e)<=set(f) for i in e]
        assert all(fl in W for fl in flags) and len(W)==len(flags)
        certs={}
        for i,j in combinations(range(len(V)),2):
            if (i,j) in E: continue
            c=pair_cert(V,i,j); assert c is not None,(name,i,j); certs[(i,j)]=c
        print(name,len(V),len(E),len(F),'flags',len(flags),'maxword',max(len(w) for w in W.values()),'certs',len(certs), 'maxcertlen',max(len(c[0]) for c in certs.values()) if certs else 0)
        out[name]=dict(V=V,F=F,E=E,gens=gens,perms=perms,base=base,words=W,certs=certs)
    import pickle, os
    pickle.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'platonic_data.pkl'), 'wb'))
