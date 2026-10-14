"""Two predeclared diagnostics: 3x3 selector shapes and fixed-cover/order tests.

No random search, no saved census. Exact tests are diagnostic, not the proof.
"""
from itertools import combinations, permutations
from pathlib import Path
import argparse
import convert as c
import verify as v


def check(condition, message):
    if not condition:
        raise ValueError(message)


def all_subsets(elements):
    seq = sorted(elements)
    for k in range(len(seq) + 1):
        for subset in combinations(seq, k):
            yield set(subset)


def dp_nu(P, I, E):
    # Independent exhaustive DP over matching right-endpoint sets.
    used = {frozenset()}
    for p in sorted(P):
        previous = tuple(used)
        used |= {U | {i} for U in previous for i in I if i not in U and (p, i) in E}
    return max(map(len, used), default=0)


def primitive():
    X = set(range(3)); subsets = list(all_subsets(X))
    pairs = [(p, i) for p in range(3) for i in range(3)]
    before = v.COUNT; checks = 0; systems = 0
    for mask in range(512):
        E = {edge for t, edge in enumerate(pairs) if mask >> t & 1}
        cache = {}
        for P in subsets:
            for I in subsets:
                chosen, proof = c.selector(P, I, E, [0, 1, 2])
                verified = v.selection(P, I, E, [0, 1, 2], {'coordinate': 0, **proof}, 0, 3)
                check(chosen == verified, 'diagnostic check failed')
                check(len(chosen) == dp_nu(P, I, E) == dp_nu(P, chosen, E), 'diagnostic check failed')
                cache[frozenset(P), frozenset(I)] = chosen
                systems += 1
        for P in subsets:
            for I in subsets:
                S = cache[frozenset(P), frozenset(I)]
                for Q in subsets:
                    if P <= Q:
                        check(S <= cache[frozenset(Q), frozenset(I)], 'diagnostic check failed')
                        checks += 1
                    if Q <= I:
                        check(S & Q <= cache[frozenset(P), frozenset(Q)], 'diagnostic check failed')
                        checks += 1
    print('PASS selector diagnostic: 512 labelled 3x3 supports;', systems, 'subset systems;', checks, 'monotonicity inclusions;')
    print(v.COUNT - before, 'equal-size matching/cover certificates, also cross-checked with independent exhaustive DP.')


def fixed_covers(directory):
    before = v.COUNT; converted = 0; nontrivial = 0; positive = 0; transpose_count = 0
    for path in sorted(Path(directory).glob('*.json')):
        record = v.load(path)
        data = record['instance']
        if data['n'] > 3:
            continue
        n, arrows, R, C, Z, H, G = v.rebuild(data)
        _, _, _, _, Z2, H2, G2 = c.supports(data)
        check(G2 == G and Z == Z2 and H == H2, 'diagnostic check failed')
        original_request = record['request']
        W = {('R', *pair) for pair in original_request['W']}
        E = c.left_restrict(G['B'], W)[2]
        t = len(v.certificate(G['N'], record['accounting']['certificates']['N'], n))
        for K in all_subsets(W | G['B'][1]):
            if not all(u in K or h in K for u, h in E):
                continue
            for order in permutations(range(n)):
                request = {**original_request, 'KB': [list(x) for x in sorted(K)], 'order': list(order)}
                output = c.convert(data, request)
                v.verify_conversion(data, request, output)
                converted += 1
                nontrivial += len(K) < len(W)
                positive += len(W) + t - len(Z) > 0
        # Also run the conversion on the actual same-relation transpose, not
        # merely a renamed output cover. Use its L maximum's saturated W.
        transposed = {'n': n, 'arrows': data['arrows'],
                      'R': [list(reversed(x)) for x in data['C']],
                      'C': [list(reversed(x)) for x in data['R']]}
        *_, TG = c.supports(transposed)
        lc, alpha, _ = c.solve(TG['L'])
        v.certificate(v.rebuild(transposed)[-1]['L'], lc, n)
        bc, _, _ = c.solve(c.left_restrict(TG['B'], set(alpha)))
        v.certificate(v.restrict(v.rebuild(transposed)[-1]['B'], set(alpha)), bc, n)
        req = {'W': [list(u[1:]) for u in sorted(alpha)], 'alpha': c.encode_matching(alpha),
               'KB': bc['cover'], 'order': list(reversed(range(n)))}
        v.verify_conversion(transposed, req, c.convert(transposed, req))
        transpose_count += 1
        print('PASS fixed instance', path.stem)
    print('PASS', converted, 'cover/order combinations;', nontrivial, 'nontrivial b<W;', positive, 'with positive |W|+nu(N)-|Z|;')
    print(transpose_count, 'separately constructed same-relation transpose conversions;')
    print(v.COUNT - before, 'equal-size matching/cover certificates in this diagnostic.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['primitive', 'covers'])
    parser.add_argument('--fixtures', type=Path, default=Path(__file__).resolve().parents[1] / 'fixtures')
    args = parser.parse_args()
    if args.mode == 'primitive':
        primitive()
    else:
        fixed_covers(args.fixtures)


if __name__ == '__main__':
    main()
