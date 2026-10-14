"""Independent exact checker. Does not import convert or run a matching optimizer.

Original supports are rebuilt by separate existential corner predicates. Every
claimed optimum is witnessed by a matching and an equal-cardinality cover.
All coordinate decoding precedes membership/equality tests and rejects aliases.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path

COUNT = 0
LENGTHS = {'R': 3, 'C': 3, 'H': 3, 'ZL': 3, 'ZR': 3, 'P': 2, 'I': 2}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def fields(obj, required, optional=()):
    need(type(obj) is dict and set(required) <= set(obj)
         and set(obj) <= set(required) | set(optional), 'invalid object fields')


def integer(x, lower, upper):
    need(type(x) is int and lower <= x < upper, 'coordinate must be exact in-range integer')
    return x


def pairs(raw, n):
    need(type(raw) is list, 'pair collection must be a JSON list')
    result = []
    for row in raw:
        need(type(row) is list and len(row) == 2, 'bad coordinate pair')
        result.append(tuple(integer(x, 0, n) for x in row))
    need(len(result) == len(set(result)), 'duplicate pair')
    return set(result)


def decode(raw, n):
    need(type(raw) is list and len(raw) > 0 and type(raw[0]) is str, 'bad tagged vertex')
    need(raw[0] in LENGTHS and len(raw) == LENGTHS[raw[0]], 'invalid tag/arity')
    return (raw[0], *(integer(x, 0, n) for x in raw[1:]))


def vertex_set(raw, n, allowed):
    need(type(raw) is list, 'vertex collection must be a JSON list')
    rows = [decode(v, n) for v in raw]
    need(len(rows) == len(set(rows)) and set(rows) <= allowed, 'duplicate/out-of-graph vertex')
    return set(rows)


def rebuild(instance):
    fields(instance, {'n', 'arrows', 'R', 'C'})
    n = instance['n']
    need(type(n) is int and n >= 0, 'n must be an exact nonnegative integer')
    arrows, R, C = (pairs(instance[k], n) for k in ('arrows', 'R', 'C'))
    X = range(n)
    Z = {(i, j) for i in X for j in X
         if any((p, j) in R and (p, i) in arrows for p in X)
         and any((i, s) in C and (s, j) in arrows for s in X)}
    H = {(p, s) for p in X for s in X
         if any((p, j) in R and (s, j) in arrows for j in X)
         and any((i, s) in C and (p, i) in arrows for i in X)}
    families = {'R': R, 'C': C, 'H': H, 'ZL': Z, 'ZR': Z}
    V = {tag: {(tag, x, y) for x, y in coord} for tag, coord in families.items()}
    G = {}
    for name, left, right in [('L', V['R'], V['ZR']), ('N', V['ZL'], V['C']),
                              ('B', V['R'], V['H']), ('A', V['H'], V['C']),
                              ('Gamma', V['R'] | V['ZL'], V['C'] | V['ZR'])]:
        E = set()
        for u in left:
            for v in right:
                kind = (u[0], v[0])
                ok = False
                if kind == ('R', 'C'):
                    ok = (u[1], v[1]) in arrows and (v[2], u[2]) in arrows
                elif kind in [('R', 'ZR'), ('H', 'C')]:
                    ok = u[2] == v[2] and (u[1], v[1]) in arrows
                elif kind in [('R', 'H'), ('ZL', 'C')]:
                    ok = u[1] == v[1] and (v[2], u[2]) in arrows
                if ok:
                    E.add((u, v))
        need(not left & right, 'tags overlap')
        G[name] = (left, right, E)
    return n, arrows, R, C, Z, H, G


def restrict(G, U):
    L, R, E = G
    return (L & U, R, {(u, v) for u, v in E if u in U})


def matching(G, raw, n):
    need(type(raw) is list, 'matching must be a list')
    L, R, E = G
    out = {}; used = set()
    for row in raw:
        need(type(row) is list and len(row) == 2, 'matching edge must contain two vertices')
        u, v = decode(row[0], n), decode(row[1], n)
        need(u in L and v in R and (u, v) in E, 'matching edge absent')
        need(u not in out and v not in used, 'matching repeats endpoint')
        out[u] = v; used.add(v)
    return out


def cover(G, raw, n):
    K = vertex_set(raw, n, G[0] | G[1])
    need(all(u in K or v in K for u, v in G[2]), 'cover misses an edge')
    return K


def certificate(G, cert, n):
    global COUNT
    fields(cert, {'matching', 'cover'})
    M = matching(G, cert['matching'], n)
    K = cover(G, cert['cover'], n)
    need(len(M) == len(K), 'matching/cover cardinalities differ')
    COUNT += 1
    return M


def selection(P, I, arrows, order, item, coordinate, n):
    fields(item, {'coordinate', 'selected', 'prefix_certificates'})
    need(integer(item['coordinate'], 0, n) == coordinate, 'selector coordinate mismatch')
    need(type(item['selected']) is list, 'selected coordinates must be a list')
    selected = [integer(i, 0, n) for i in item['selected']]
    need(len(selected) == len(set(selected)), 'repeated selected coordinate')
    certs = item['prefix_certificates']
    seq = [i for i in order if i in I]
    need(type(certs) is list and len(certs) == len(seq) + 1, 'wrong prefix certificate count')
    previous = 0; expected = []; prefix = set()
    for index in range(len(seq) + 1):
        if index:
            prefix.add(seq[index - 1])
        G = ({('P', p) for p in P}, {('I', i) for i in prefix},
             {(('P', p), ('I', i)) for p in P for i in prefix if (p, i) in arrows})
        m = len(certificate(G, certs[index], n))
        need(m in (previous, previous + 1), 'invalid matching-size increment')
        if m > previous:
            need(index > 0, 'nonempty zero-prefix matching')
            expected.append(seq[index - 1])
        previous = m
    need(selected == expected and len(selected) == previous, 'selector differs from certified increments')
    return set(selected)


def verify_conversion(instance, request, output):
    n, arrows, R, C, Z, H, G = rebuild(instance)
    fields(request, {'W', 'alpha', 'KB', 'order'})
    W0 = pairs(request['W'], n)
    need(W0 <= R, 'W outside R')
    W = {('R', p, j) for p, j in W0}
    alpha = matching(restrict(G['L'], W), request['alpha'], n)
    need(set(alpha) == W, 'L matching does not saturate W')
    KB = cover(restrict(G['B'], W), request['KB'], n)
    order = request['order']
    need(type(order) is list, 'order must be a list')
    order = [integer(i, 0, n) for i in order]
    need(len(order) == n and set(order) == set(range(n)), 'order not a permutation')
    fields(output, {'branch', 'KN', 'selectors_Z', 'selectors_C'})
    KN = cover(G['N'], output['KN'], n)
    need(len(KN) <= len(Z) - len(W) + len(KB), 'N cover exceeds converted budget')
    if len(KB) >= len(W):
        need(output['branch'] == 'all-Z' and KN == G['N'][0], 'wrong trivial branch')
        need(output['selectors_Z'] == [] and output['selectors_C'] == [], 'unexpected trivial selectors')
    else:
        need(output['branch'] == 'ordered-selector', 'wrong nontrivial branch')
        SZ, SC = output['selectors_Z'], output['selectors_C']
        need(type(SZ) is list and type(SC) is list and len(SZ) == n and len(SC) == n, 'bad selector arrays')
        remaining = W - KB; V = KB & G['B'][1]
        Q = set(); D = set()
        for j in range(n):
            P = {p for _, p, jj in remaining if j == jj}
            I = {i for i, jj in Z if j == jj}
            S = selection(P, I, arrows, order, SZ[j], j, n)
            need(len(S) == len(P), 'Z selector lost saturation')
            Q.update(('ZL', i, j) for i in S)
        for s in range(n):
            P = {p for _, p, ss in V if s == ss}
            I = {i for i, ss in C if s == ss}
            S = selection(P, I, arrows, order, SC[s], s, n)
            need(len(S) <= len(P), 'C selector exceeds H resources')
            D.update(('C', i, s) for i in S)
        need(KN == (G['N'][0] - Q) | D, 'KN not the specified construction')
        need(len(Q) == len(remaining) and len(D) <= len(V), 'resource accounting mismatch')
        need(all(c in D for z, c in G['N'][2] if z in Q), 'selected-Z neighborhood containment fails')
    return (n, arrows, R, C, Z, H, G), (len(W), len(KB), len(KN))


def augmentation(G, M, raw, n):
    need(type(raw) is list, 'augmenting path must be a list')
    path = [decode(v, n) for v in raw]
    need(len(path) >= 2 and len(path) % 2 == 0 and len(path) == len(set(path)), 'invalid augmenting path shape')
    need(set(path[0::2]) <= G[0] and set(path[1::2]) <= G[1], 'path has wrong sides')
    need(path[0] not in M and path[-1] not in set(M.values()), 'path endpoints are not free')
    for index in range(len(path) - 1):
        u, v = ((path[index], path[index+1]) if index % 2 == 0 else (path[index+1], path[index]))
        need((u, v) in G[2] and ((M.get(u) == v) == (index % 2 == 1)), 'path is not alternating')
    after = dict(M)
    for u in path[2::2]:
        del after[u]
    after.update(zip(path[0::2], path[1::2]))
    need(len(after) == len(M) + 1 and set(M) <= set(after), 'augmentation lost left saturation')
    return after


def transpose_vertex(v):
    return ({'R': 'C', 'C': 'R', 'H': 'H', 'ZL': 'ZR', 'ZR': 'ZL'}[v[0]], v[2], v[1])


def verify_accounting(instance, rebuilt, account):
    n, arrows, R, C, Z, H, G = rebuilt
    fields(account, {'certificates', 'extension_paths', 'extension', 'extracted'})
    certs = account['certificates']
    fields(certs, {'Gamma', 'L', 'N', 'B', 'A', 'B_RT', 'B_alpha'})
    matches = {key: certificate(G[key], certs[key], n) for key in ('Gamma', 'L', 'N', 'B', 'A')}
    M = matches['Gamma']
    alpha = {u: v for u, v in M.items() if v[0] == 'ZR'}
    eta = {u: v for u, v in M.items() if u[0] == 'ZL'}
    T = {u for u, v in M.items() if u[0] == 'R' and v[0] == 'C'}
    need(alpha == matches['L'] and eta == matches['N'], 'auxiliary parts not certified maximum')
    k, ell, t = len(T), len(alpha), len(eta)
    need(len(M) == k + ell + t, 'Gamma matching decomposition mismatch')
    RT = certificate(restrict(G['B'], G['B'][0] - T), certs['B_RT'], n)
    seed = certificate(restrict(G['B'], set(alpha)), certs['B_alpha'], n)
    need(len(matches['B']) == k + len(RT), 'inherited core-deletion identity mismatch')
    need(len(seed) >= ell + t - len(Z), 'G+ mismatch')
    need(len(RT) >= ell + t - len(Z), 'G mismatch')
    current = dict(seed)
    need(type(account['extension_paths']) is list, 'extension paths must be a list')
    for raw in account['extension_paths']:
        current = augmentation(G['B'], current, raw, n)
    need(current == matching(G['B'], account['extension'], n), 'extension trace mismatch')
    need(T | set(seed) <= set(current), 'extension loses required left vertices')
    extracted = matching(G['B'], account['extracted'], n)
    need(extracted == {u: current[u] for u in T | set(seed)}, 'wrong extraction')
    need(len(extracted) == k + len(seed) and len(extracted) >= max(0, len(M) - len(Z)), 'extraction budget mismatch')
    need(len(M) <= len(Z) + min(len(matches['B']), len(matches['A'])), 'capacity mismatch')
    transposed = {'n': n, 'arrows': instance['arrows'],
                  'R': [list(reversed(c)) for c in instance['C']],
                  'C': [list(reversed(r)) for r in instance['R']]}
    _, _, _, _, ZT, HT, GT = rebuild(transposed)
    need(ZT == {(j, i) for i, j in Z} and HT == {(s, p) for p, s in H}, 'transposed corners mismatch')
    for name, other in [('Gamma', 'Gamma'), ('L', 'N'), ('N', 'L'), ('B', 'A'), ('A', 'B')]:
        L, Rr, E = G[name]
        expected = ({transpose_vertex(v) for v in Rr}, {transpose_vertex(u) for u in L},
                    {(transpose_vertex(v), transpose_vertex(u)) for u, v in E})
        need(expected == GT[other], 'same-relation transpose support mismatch')
        transformed = {'matching': [[list(transpose_vertex(v)), list(transpose_vertex(u))]
                                   for u, v in matches[name].items()],
                       'cover': [list(transpose_vertex(decode(v, n))) for v in certs[name]['cover']]}
        certificate(GT[other], transformed, n)
    return k, ell, t, len(seed)


def verify_record(record):
    fields(record, {'schema', 'instance', 'request', 'conversion'}, {'accounting', 'label'})
    need(type(record['schema']) is int and record['schema'] == 1, 'invalid schema')
    if 'label' in record:
        need(type(record['label']) is str, 'label must be a string')
    rebuilt, stats = verify_conversion(record['instance'], record['request'], record['conversion'])
    accounting = verify_accounting(record['instance'], rebuilt, record['accounting']) if 'accounting' in record else None
    return stats, accounting


def load(path):
    def object_pairs(rows):
        result = {}
        for key, value in rows:
            need(key not in result, 'duplicate JSON object key')
            result[key] = value
        return result
    def constant(value):
        raise ValueError('nonfinite JSON number: ' + value)
    return json.loads(Path(path).read_text(), object_pairs_hook=object_pairs, parse_constant=constant)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paths', nargs='+', type=Path)
    args = parser.parse_args()
    before = COUNT
    for path in args.paths:
        stats, account = verify_record(load(path))
        print('PASS', path.name, 'W,b,KN=', stats, 'k,ell,t,B_alpha=', account)
    print('PASS', len(args.paths), 'records;', COUNT - before, 'equal-size matching/cover certificates')


if __name__ == '__main__':
    main()
