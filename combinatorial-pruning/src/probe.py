"""Bounded falsification probes, not a finite proof of the target.
Standard library only. Supports are constructed from the original relation.
"""
from __future__ import annotations
from itertools import product
from random import Random
import json
from pathlib import Path

Pair = tuple[int, int]

def supports(n: int, arrows: set[Pair], R: set[Pair], C: set[Pair]):
    conflicts = {(r, c) for r in R for c in C
                 if (r[0], c[0]) in arrows and (c[1], r[1]) in arrows}
    Z = {(c[0], r[1]) for r, c in conflicts}
    H = {(r[0], c[1]) for r, c in conflicts}
    L = {r: {z for z in Z if r[1] == z[1] and (r[0], z[0]) in arrows} for r in R}
    N = {z: {c for c in C if z[0] == c[0] and (c[1], z[1]) in arrows} for z in Z}
    B = {r: {h for h in H if r[0] == h[0] and (h[1], r[1]) in arrows} for r in R}
    A = {h: {c for c in C if h[1] == c[1] and (h[0], c[0]) in arrows} for h in H}
    return conflicts, Z, H, L, N, B, A

def matching(adj: dict):
    """Elementary depth-first augmenting paths; returns left-to-right map."""
    right = {}
    def visit(u, seen):
        for v in sorted(adj[u]):
            if v in seen:
                continue
            seen.add(v)
            if v not in right or visit(right[v], seen):
                right[v] = u
                return True
        return False
    for u in sorted(adj):
        visit(u, set())
    return {u: v for v, u in right.items()}

def exposable(adj):
    size = len(matching(adj))
    return {u for u in adj if len(matching({x: vs for x, vs in adj.items() if x != u})) == size}

def powerset(S):
    seq = sorted(S)
    for bits in range(1 << len(seq)):
        yield {v for i, v in enumerate(seq) if bits >> i & 1}

def neighbor(adj, S):
    return set().union(*(adj[u] for u in S)) if S else set()

def probe_case(n, arrows, R, C):
    F,Z,H,L,N,B,A=supports(n, arrows, R,C)
    alpha=matching(L)
    beta=matching(N)
    U=exposable(B)
    V=exposable(N)
    W=neighbor(L,U)
    if not W <= V:
        raise AssertionError('Exposure transfer fails')
    # Candidate: keep alpha fixed, route every beta C endpoint into H or unused Z.
    # This is intentionally stronger than the target; seek an exact counterexample.
    used=set(alpha.values())
    Cs=set(beta.values())
    adj={c: {('H', *h) for h in H if c in A[h]} |
              {('Z', *z) for z in Z-used if c in N[z]} for c in Cs}
    route=matching(adj)
    if len(route)<len(Cs):
        return {'n':n,'arrows':sorted(arrows),'R':sorted(R),'C':sorted(C),
                'candidate':'fixed_alpha_projection','alpha':sorted(alpha.items()),
                'beta':sorted(beta.items()),'route_size':len(route)}
    return None

def main():
    rng=Random(173)
    count=0
    for n in range(1,5):
        pairs=list(product(range(n),repeat=2))
        for trial in range(1000):
            arrows={e for e in pairs if rng.random()<0.45}
            R={e for e in pairs if rng.random()<0.45}
            C={e for e in pairs if rng.random()<0.45}
            count+=1
            fail=probe_case(n,arrows,R,C)
            if fail:
                print('FAIL',json.dumps(fail,sort_keys=True))
                print('cases_before_stop',count)
                return
    print('No candidate failure in',count,'seeded inputs; not a proof.')

if __name__=='__main__':
    main()
