#!/usr/bin/env python3
"""Validates: finite exact frontier-register semantics and state accounting.

Independent of check_backdoors.py; no corpus imports or third-party dependencies.
Checks direct-vs-frontier acceptance, state widths, and <=8 incoming transitions.
Does not prove asymptotic hardness, first-transition counting, or historical novelty.
Fixed seed 991734. Run from the repository root:
  python3 research/circuit-lower-bound-frontiers/larger-gates/data/check_frontier_independent.py
"""
from itertools import product
from collections import defaultdict
from math import prod
import random
rng=random.Random(991734)

def bits(n): return product((0,1),repeat=n)
def pred(g,t):
    kind,slots,p=g
    if kind=='thr': return int(t>=p)
    if kind=='mod': return int(t%p[0] in p[1])
    return p[t]
def direct(n,gs,x,out):
    v=list(x)
    for g in gs:
        kind,slots,p=g
        v.append((p>>(2*v[slots[0]]+v[slots[1]]))&1 if kind=='bin'
                 else pred(g,sum(w*v[u] for u,w in slots)))
    return v[out]

def run(n,gs,out):
    specs=[(n+i,g) for i,g in enumerate(gs) if g[0]!='bin']
    sid={u:j for j,(u,g) in enumerate(specs)}
    ordinary=list(range(n))+[n+i for i,g in enumerate(gs) if g[0]=='bin']
    # Edges retain slot identities; each gate gets its original ordered inputs.
    uses=defaultdict(list)
    for i,g in enumerate(gs):
        if g[0]=='bin':
            for k,u in enumerate(g[1]):
                if u not in sid: uses[u].append((n+i,k))
    vertices=list(ordinary); edges=[]; slotedge={}; outgoing={}; copies=set()
    def edge(u,v): edges.append((u,v)); return len(edges)-1
    for u,targets in uses.items():
        if len(targets)==1:
            v,k=targets[0]; slotedge[v,k]=edge(u,v); outgoing[u]=len(edges)-1
        else:
            cs=list(range(n+len(gs)+len(copies),n+len(gs)+len(copies)+len(targets)-1))
            vertices+=cs; copies.update(cs)
            outgoing[u]=edge(u,cs[0])
            for c,d in zip(cs,cs[1:]): edge(c,d)
            for k,(v,slot) in enumerate(targets): slotedge[v,slot]=edge(cs[min(k,len(cs)-1)],v)
    incident={u:[e for e,(a,b) in enumerate(edges) if u in (a,b)] for u in vertices}
    assert max(map(len,incident.values()),default=0)<=3
    q=len(specs); R=[g[2][0] if g[0]=='mod' else 1+sum(abs(w) for _,w in g[1]) for _,g in specs]
    def normal(j,v): return v%specs[j][1][2][0] if specs[j][1][0]=='mod' else v
    coeff={u:[sum(w for v,w in g[1] if u==v) for _,g in specs] for u in ordinary}
    def initial(a): return tuple(normal(j,sum(w*a[sid[u]] for u,w in g[1] if u in sid)) for j,(_,g) in enumerate(specs))
    states={ ((),a,initial(a)):{()} for a in bits(q) if out not in sid or a[sid[out]]==1 }
    order=vertices[:]; rng.shuffle(order); processed=set(); cut=[]; queried=[]; maxfanin=0
    for u in order:
        newprocessed=processed|{u}
        newcut=[e for e,(v,w) in enumerate(edges) if (v in newprocessed)!=(w in newprocessed)]
        fresh=[e for e in incident[u] if e not in cut]
        nxt=defaultdict(set); incoming=defaultdict(set)
        for state,prefixes in states.items():
            frontier,a,reg=state
            fixed=dict(zip(cut,frontier))
            for b in ([0,1] if u<n else [None]):
                for vals in bits(len(fresh)):
                    ev=fixed|dict(zip(fresh,vals))
                    if u in copies:
                        if len({ev[e] for e in incident[u]})>1: continue
                        signal=None
                    elif u<n: signal=b
                    else:
                        g=gs[u-n]
                        local=[a[sid[v]] if v in sid else ev[slotedge[u,k]] for k,v in enumerate(g[1])]
                        signal=(g[2]>>(2*local[0]+local[1]))&1
                    if signal is not None:
                        if u in outgoing and ev[outgoing[u]]!=signal: continue
                        if out==u and signal!=1: continue
                        nr=tuple(normal(j,v+coeff[u][j]*signal) for j,v in enumerate(reg))
                    else: nr=reg
                    ns=(tuple(ev[e] for e in newcut),a,nr)
                    incoming[ns].add((state,b))
                    nxt[ns].update(p+(b,) if b is not None else p for p in prefixes)
        assert max(map(len,incoming.values()),default=0)<=8
        maxfanin=max(maxfanin,max(map(len,incoming.values()),default=0))
        assert len(nxt)<=2**(len(newcut)+q)*prod(R)
        # Fixed a has at most R_j distinct partial sum values, even signed weights.
        for a in bits(q):
            for j in range(q): assert len({st[2][j] for st in nxt if st[1]==a})<=R[j]
        states=nxt; processed=newprocessed; cut=newcut
        if u<n: queried.append(u)
    accepted=set()
    for (_,a,reg),prefixes in states.items():
        if all(pred(g,reg[j])==a[j] for j,(_,g) in enumerate(specs)):
            for p in prefixes:
                x=[0]*n
                for u,b in zip(queried,p): x[u]=b
                accepted.add(tuple(x))
    expected={x for x in bits(n) if direct(n,gs,x,out)}
    assert accepted==expected,(n,gs,out,order,accepted,expected)
    return len(vertices),maxfanin

cases=[]
# zero-input binary component, special-to-special wires, and dead observed sinks
cases.append((2,[('mod',[(0,1),(1,1)],(2,(1,))),('bin',[2,2],9),('thr',[(3,-3),(2,5)],1)],3))
for _ in range(180):
    n=rng.randrange(1,4); gs=[]; q=0
    for j in range(rng.randrange(1,7)):
        typ=rng.choice(['bin','bin','thr','mod','sym']) if q<3 else 'bin'
        if typ=='bin': gs.append((typ,[rng.randrange(n+j) for _ in range(2)],rng.randrange(16)))
        else:
            q+=1
            slots=[(rng.randrange(n+j),1 if typ=='sym' else rng.randrange(-3,4)) for _ in range(rng.randrange(0,5))]
            param=rng.randrange(-4,5) if typ=='thr' else (rng.randrange(2,5),(1,)) if typ=='mod' else [rng.randrange(2) for _ in range(len(slots)+1)]
            gs.append((typ,slots,param))
    cases.append((n,gs,rng.randrange(n+len(gs))))
results=[run(*c) for c in cases]
print('Validates: finite exact frontier-register semantics and state accounting.')
print('seed=991734; circuits=',len(cases),'vertices processed=',sum(x[0] for x in results),'max observed incoming labeled transitions=',max(x[1] for x in results))
print('PASS: exhaustive original-vs-frontier acceptance; signed/mod register widths; <=8 predecessor transitions; arbitrary output wires, vertex orders, zero-arity special gates, and zero-input components')

print('Limits: finite compiler checks only; no asymptotic hardness or novelty certification.')
