"""Constructive ordered-matching cover conversion. Python standard library only.

All mathematical input coordinates are exact integers in range(n). Distinct
vertex tags preserve the original copies. No network or subprocess access.
This implementation is newly written for this handoff, not copied from v1.0.
"""
from __future__ import annotations
import argparse
from collections import deque
import json
from pathlib import Path

TAG_LENGTH = {'R': 3, 'C': 3, 'H': 3, 'ZL': 3, 'ZR': 3, 'P': 2, 'I': 2}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def coordinates(sequence, n, width):
    require(type(sequence) is list, 'coordinate collection must be a JSON list')
    out = []
    for item in sequence:
        require(type(item) is list and len(item) == width, 'bad coordinate width')
        require(all(type(x) is int and 0 <= x < n for x in item), 'non-integer/out-of-range coordinate')
        out.append(tuple(item))
    require(len(out) == len(set(out)), 'duplicate coordinates')
    return set(out)


def vertex(item, n):
    require(type(item) is list and len(item) >= 1 and type(item[0]) is str, 'malformed vertex')
    require(item[0] in TAG_LENGTH and len(item) == TAG_LENGTH[item[0]], 'wrong vertex tag/width')
    require(all(type(x) is int and 0 <= x < n for x in item[1:]), 'non-integer/out-of-range vertex coordinate')
    return tuple(item)


def vertices(sequence, n, allowed):
    require(type(sequence) is list, 'vertex collection must be a JSON list')
    out = [vertex(v, n) for v in sequence]
    require(len(out) == len(set(out)), 'duplicate vertex')
    require(set(out) <= allowed, 'vertex outside graph')
    return set(out)


def graph(left, right, edges):
    require(not set(left) & set(right), 'graph sides are not tagged distinctly')
    return (set(left), set(right), set(edges))


def supports(instance):
    require(type(instance) is dict and set(instance) == {'n', 'arrows', 'R', 'C'}, 'bad instance fields')
    n = instance['n']
    require(type(n) is int and n >= 0, 'n must be a nonnegative exact integer')
    arrows, R, C = [coordinates(instance[k], n, 2) for k in ('arrows', 'R', 'C')]
    conflicts = {(r, c) for r in R for c in C
                 if (r[0], c[0]) in arrows and (c[1], r[1]) in arrows}
    Z = {(c[0], r[1]) for r, c in conflicts}
    H = {(r[0], c[1]) for r, c in conflicts}
    RR = {('R', *v) for v in R}; CC = {('C', *v) for v in C}
    HH = {('H', *v) for v in H}
    ZL = {('ZL', *v) for v in Z}; ZR = {('ZR', *v) for v in Z}
    LE = {(r, z) for r in RR for z in ZR if r[2] == z[2] and (r[1], z[1]) in arrows}
    NE = {(z, c) for z in ZL for c in CC if z[1] == c[1] and (c[2], z[2]) in arrows}
    BE = {(r, h) for r in RR for h in HH if r[1] == h[1] and (h[2], r[2]) in arrows}
    AE = {(h, c) for h in HH for c in CC if h[2] == c[2] and (h[1], c[1]) in arrows}
    CE = {(('R', *r), ('C', *c)) for r, c in conflicts}
    G = {'L': graph(RR, ZR, LE), 'N': graph(ZL, CC, NE),
         'B': graph(RR, HH, BE), 'A': graph(HH, CC, AE),
         'Gamma': graph(RR | ZL, CC | ZR, LE | NE | CE)}
    return n, arrows, R, C, Z, H, G


def left_restrict(G, subset):
    L, R, E = G
    return graph(L & set(subset), R, {(u, v) for u, v in E if u in subset})


def inverse(G):
    L, R, E = G
    return graph(R, L, {(v, u) for u, v in E})


def parse_matching(G, sequence, n):
    require(type(sequence) is list, 'matching must be a JSON list')
    M = {}
    used = set()
    for e in sequence:
        require(type(e) is list and len(e) == 2, 'bad matching edge shape')
        u, v = vertex(e[0], n), vertex(e[1], n)
        require(u in G[0] and v in G[1] and (u, v) in G[2], 'illegal matching edge')
        require(u not in M and v not in used, 'repeated matching endpoint')
        M[u] = v; used.add(v)
    return M


def augment_path(G, M):
    L, R, E = G
    require(set(M) <= L and set(M.values()) <= R and len(set(M.values())) == len(M), 'invalid seed matching')
    require(all((u, v) in E for u, v in M.items()), 'seed edge absent')
    rev = {v: u for u, v in M.items()}
    adj = {u: [] for u in L}
    for u, v in sorted(E):
        adj[u].append(v)
    roots = sorted(L - set(M))
    pred = {u: None for u in roots}
    todo = deque(roots)
    while todo:
        u = todo.popleft()
        for v in adj[u]:
            if M.get(u) == v or v in pred:
                continue
            pred[v] = u
            if v not in rev:
                path = []
                cur = v
                while cur is not None:
                    path.append(cur); cur = pred[cur]
                return list(reversed(path))
            w = rev[v]
            if w not in pred:
                pred[w] = v; todo.append(w)
    return None


def flip(M, path):
    out = dict(M)
    for u in path[2::2]:
        del out[u]
    out.update(zip(path[0::2], path[1::2]))
    return out


def encode_matching(M):
    return [[list(u), list(v)] for u, v in sorted(M.items())]


def minimum_cover(G, M):
    L, R, E = G
    rev = {v: u for u, v in M.items()}
    adj = {u: [] for u in L}
    for u, v in sorted(E):
        adj[u].append(v)
    reached_L = L - set(M); reached_R = set()
    todo = deque(sorted(reached_L))
    while todo:
        u = todo.popleft()
        for v in adj[u]:
            if M.get(u) == v or v in reached_R:
                continue
            reached_R.add(v)
            require(v in rev, 'matching is not maximum')
            w = rev[v]
            if w not in reached_L:
                reached_L.add(w); todo.append(w)
    K = (L - reached_L) | reached_R
    require(len(K) == len(M), 'cover size mismatch')
    require(all(u in K or v in K for u, v in E), 'not a cover')
    return K


def solve(G, seed=None):
    M = {} if seed is None else dict(seed)
    paths = []
    while True:
        path = augment_path(G, M)
        if path is None:
            break
        M = flip(M, path); paths.append(path)
    K = minimum_cover(G, M)
    return {'matching': encode_matching(M), 'cover': [list(v) for v in sorted(K)]}, M, paths


def arrow_graph(P, I, arrows):
    return graph({('P', p) for p in P}, {('I', i) for i in I},
                 {(('P', p), ('I', i)) for p in P for i in I if (p, i) in arrows})


def selector(P, I, arrows, order):
    prefix = set(); M = {}; chosen = []
    cert, M, _ = solve(arrow_graph(P, prefix, arrows), M)
    certs = [cert]
    for i in order:
        if i not in I:
            continue
        prefix.add(i)
        old_size = len(M)
        cert, M, _ = solve(arrow_graph(P, prefix, arrows), M)
        require(len(M) in (old_size, old_size + 1), 'selector increment not 0 or 1')
        if len(M) > old_size:
            chosen.append(i)
        certs.append(cert)
    return set(chosen), {'selected': chosen, 'prefix_certificates': certs}


def convert(instance, request):
    n, arrows, R, C, Z, H, G = supports(instance)
    require(type(request) is dict and set(request) == {'W', 'alpha', 'KB', 'order'}, 'bad request fields')
    Wpairs = coordinates(request['W'], n, 2)
    require(Wpairs <= R, 'W is not a subset of R')
    W = {('R', *v) for v in Wpairs}
    alpha = parse_matching(left_restrict(G['L'], W), request['alpha'], n)
    require(set(alpha) == W, 'alpha does not saturate W')
    KB = vertices(request['KB'], n, W | G['B'][1])
    require(all(u in KB or h in KB for u, h in G['B'][2] if u in W), 'KB not a cover of B[W,H]')
    order = request['order']
    require(type(order) is list and all(type(i) is int for i in order)
            and len(order) == n and set(order) == set(range(n)), 'order is not an exact permutation of X')
    if len(KB) >= len(W):
        return {'branch': 'all-Z', 'KN': [list(v) for v in sorted(G['N'][0])],
                'selectors_Z': [], 'selectors_C': []}
    remaining = W - KB
    V = KB & G['B'][1]
    Q = set(); selected_C = set(); SZ = []; SC = []
    for j in range(n):
        P = {p for _, p, jj in remaining if jj == j}
        I = {i for i, jj in Z if jj == j}
        S, proof = selector(P, I, arrows, order)
        require(len(S) == len(P), 'input saturation was lost')
        Q |= {('ZL', i, j) for i in S}
        SZ.append({'coordinate': j, **proof})
    for s in range(n):
        P = {p for _, p, ss in V if ss == s}
        I = {i for i, ss in C if ss == s}
        S, proof = selector(P, I, arrows, order)
        selected_C |= {('C', i, s) for i in S}
        SC.append({'coordinate': s, **proof})
    KN = (G['N'][0] - Q) | selected_C
    require(all(z in KN or c in KN for z, c in G['N'][2]), 'conversion produced an uncovered edge')
    require(len(KN) <= len(Z) - len(W) + len(KB), 'conversion exceeds budget')
    return {'branch': 'ordered-selector', 'KN': [list(v) for v in sorted(KN)],
            'selectors_Z': SZ, 'selectors_C': SC}


def normalized_accounting(G, supplied=None):
    gamma_cert, M, _ = solve(G['Gamma'], supplied)
    # Each auxiliary augmentation removes one core edge. Cardinality is fixed.
    for side in ('L', 'N'):
        aux_graph = G['L'] if side == 'L' else inverse(G['N'])
        while True:
            aux = ({u: v for u, v in M.items() if v[0] == 'ZR'} if side == 'L'
                   else {v: u for u, v in M.items() if u[0] == 'ZL'})
            path = augment_path(aux_graph, aux)
            if path is None:
                break
            if side == 'L':
                r = path[0]
                require(r in M and M[r][0] == 'C', 'normalization has no core edge')
                del M[r]
                for u in aux:
                    del M[u]
                M.update(flip(aux, path))
            else:
                c = path[0]
                rev = {v: u for u, v in M.items()}
                require(c in rev and rev[c][0] == 'R', 'normalization has no core edge')
                del M[rev[c]]
                for u in aux.values():
                    del M[u]
                M.update({v: u for u, v in flip(aux, path).items()})
    gamma_cert['matching'] = encode_matching(M)
    alpha = {u: v for u, v in M.items() if v[0] == 'ZR'}
    eta = {u: v for u, v in M.items() if u[0] == 'ZL'}
    core = {u for u, v in M.items() if u[0] == 'R' and v[0] == 'C'}
    certs = {'Gamma': gamma_cert}
    certs['L'], _, _ = solve(G['L'], alpha)
    certs['N'], _, _ = solve(G['N'], eta)
    for name in ('B', 'A'):
        certs[name], _, _ = solve(G[name])
    certs['B_RT'], _, _ = solve(left_restrict(G['B'], G['B'][0] - core))
    certs['B_alpha'], seed, _ = solve(left_restrict(G['B'], set(alpha)))
    extension_cert, extension, paths = solve(G['B'], seed)
    require(core <= set(extension) and set(seed) <= set(extension), 'core extension lost required saturation')
    keep = core | set(seed)
    return {'certificates': certs, 'extension_paths': [[list(v) for v in path] for path in paths],
            'extension': encode_matching(extension),
            'extracted': encode_matching({u: extension[u] for u in keep})}


def load_strict(path):
    def hook(rows):
        result = {}
        for key, value in rows:
            require(key not in result, 'duplicate JSON object key')
            result[key] = value
        return result
    def constant(value):
        raise ValueError('nonfinite JSON number: ' + value)
    return json.loads(Path(path).read_text(), object_pairs_hook=hook, parse_constant=constant)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, help='JSON object with instance and request')
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    data = load_strict(args.input)
    require(type(data) is dict and set(data) == {'instance', 'request'}, 'bad input object')
    result = {'schema': 1, **data, 'conversion': convert(data['instance'], data['request'])}
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print('Wrote', args.output)


if __name__ == '__main__':
    main()
