"""Preserve inherited obstructions and challenge the need for a shared order."""
from pathlib import Path
import verify as v


def check(condition, message):
    if not condition:
        raise ValueError(message)


def encode(M, K):
    return {'matching': [[list(a), list(b)] for a, b in M], 'cover': [list(x) for x in K]}


def boolean_product(A, B):
    return [[int(any(A[i][k] and B[k][j] for k in range(len(B))))
             for j in range(len(B[0]))] for i in range(len(A))]


def matrix_graph(A):
    left = {('P', j) for j in range(len(A[0]))}
    right = {('I', i) for i in range(len(A))}
    return left, right, {(('P', j), ('I', i)) for i, row in enumerate(A) for j, x in enumerate(row) if x}


def main():
    root = Path(__file__).resolve().parents[1]
    before = v.COUNT
    record = v.load(root / 'fixtures/hall-shortcut-preserved.json')
    n, _, _, _, Z, H, G = v.rebuild(record['instance'])
    check(Z == {(i, j) for i in range(2) for j in range(2)} and H == {(0, 0)}, 'diagnostic check failed')
    bc = record['accounting']['certificates']['B']
    nc = record['accounting']['certificates']['N']
    gc = record['accounting']['certificates']['Gamma']
    b = len(v.certificate(G['B'], bc, n)); t = len(v.certificate(G['N'], nc, n))
    g = len(v.certificate(G['Gamma'], gc, n))
    for r in G['B'][0]:
        sub = v.restrict(G['B'], G['B'][0] - {r})
        other = next(iter(sub[0]))
        check(len(v.certificate(sub, encode([(other, ('H', 0, 0))], [('H', 0, 0)]), n)) == b, 'diagnostic check failed')
    for z in G['N'][0]:
        sub = v.restrict(G['N'], G['N'][0] - {z})
        M = []
        for i in range(2):
            chosen = min(u for u in sub[0] if u[1] == i)
            M.append((chosen, ('C', i, 0)))
        check(len(v.certificate(sub, encode(M, [('C', 0, 0), ('C', 1, 0)]), n)) == t, 'diagnostic check failed')
    S = G['B'][0] | G['N'][0]
    neighbors = {y for x, y in G['Gamma'][2] if x in S}
    check(len(S) - len(neighbors) == 0 < len(G['B'][0]) - b == 1, 'diagnostic check failed')
    check(g == 4 <= len(Z) + b == 5, 'diagnostic check failed')
    print('PASS inherited Hall shortcut obstruction: deficiency 0 < required 1; capacity still 4 <= 5.')
    # Independent orders for j=0 and j=1 choose different i coordinates.
    # The H resource is only (0,0); either single C choice misses one edge.
    Q = {('ZL', 0, 0), ('ZL', 1, 1)}
    D = {('C', 0, 0)}
    bad_K = (G['N'][0] - Q) | D
    missed = {(z, c) for z, c in G['N'][2] if z not in bad_K and c not in bad_K}
    check(missed == {(('ZL', 1, 1), ('C', 1, 0))}, 'diagnostic check failed')
    check(len((G['N'][0] - Q) | {c for z, c in G['N'][2] if z in Q}) == 4 > 3, 'diagnostic check failed')
    print('PASS local-order shortcut fails: budget-3 set misses ZL(1,1)--C(1,0); repair costs 4.')
    record = v.load(root / 'fixtures/repeated-H-positive.json')
    n, _, _, _, Z, H, G = v.rebuild(record['instance'])
    alpha = v.matching(G['L'], record['request']['alpha'], n)
    eta_pairs = [(('ZL', 0, 0), ('C', 0, 0)), (('ZL', 1, 1), ('C', 1, 0))]
    eta = v.certificate(G['N'], encode(eta_pairs, [('C', 0, 0), ('C', 1, 0)]), n)
    inv = {z[1:]: r for r, z in alpha.items()}
    resources = []
    for z, c in eta.items():
        r = inv[z[1:]]; h = ('H', r[1], c[2])
        check((r, h) in G['B'][2] and (h, c) in G['A'][2], 'diagnostic check failed')
        resources.append(h)
    check(resources == [('H', 0, 0), ('H', 0, 0)], 'diagnostic check failed')
    check(len(alpha) + len(eta) - len(Z) == 2, 'diagnostic check failed')
    check(len(v.cover(G['N'], record['conversion']['KN'], n)) == 2, 'diagnostic check failed')
    print('PASS repeated-H positive residual: two naive paths demand H(0,0); residual=2; converted cover=2.')
    matrices = {'L': [[1, 0], [0, 1]], 'N': [[1, 1], [1, 1]],
                'B': [[1, 1]], 'A': [[1], [1]]}
    check(boolean_product(matrices['N'], matrices['L']) == boolean_product(matrices['A'], matrices['B']) == [[1, 1], [1, 1]], 'diagnostic check failed')
    certs = {
        'L': encode([(('P', 0), ('I', 0)), (('P', 1), ('I', 1))], [('P', 0), ('P', 1)]),
        'N': encode([(('P', 0), ('I', 0)), (('P', 1), ('I', 1))], [('P', 0), ('P', 1)]),
        'B': encode([(('P', 0), ('I', 0))], [('I', 0)]),
        'A': encode([(('P', 0), ('I', 0))], [('P', 0)])}
    sizes = {name: len(v.certificate(matrix_graph(A), certs[name], 2)) for name, A in matrices.items()}
    check(sizes == {'L': 2, 'N': 2, 'B': 1, 'A': 1}, 'diagnostic check failed')
    check(sizes['B'] < sizes['L'] + sizes['N'] - 2, 'diagnostic check failed')
    print('PASS inherited Boolean-commutation obstruction: nu(B)=1 < 2, despite equal Boolean products.')
    print(v.COUNT - before, 'equal-size matching/cover certificates; no matching optimizer used.')


if __name__ == '__main__':
    main()
