"""Produce nine named diagnostic fixtures, not a verification atlas."""
import argparse
import json
from pathlib import Path
import convert as c


def instance(n, arrows, R, C):
    return {'n': n, 'arrows': [list(v) for v in sorted(arrows)],
            'R': [list(v) for v in sorted(R)], 'C': [list(v) for v in sorted(C)]}


def named_inputs():
    full2 = {(p, i) for p in range(2) for i in range(2)}
    full3 = {(p, i) for p in range(3) for i in range(3)}
    yield 'empty-X', instance(0, [], [], []), set(), [], None
    yield 'one-loop-all-tags', instance(1, {(0, 0)}, {(0, 0)}, {(0, 0)}), {(0, 0)}, [('H', 0, 0)], None
    yield 'no-conflicts', instance(2, {(0, 0)}, {(1, 1)}, {(1, 1)}), set(), [], None
    hall = instance(2, {(0, 0), (0, 1)}, {(0, 0), (0, 1)}, {(0, 0), (1, 0)})
    adversarial = {('R', 0, 0): ('ZR', 0, 0), ('R', 0, 1): ('ZR', 1, 1)}
    yield 'hall-shortcut-preserved', hall, {(0, 0), (0, 1)}, [('H', 0, 0)], adversarial
    repeated = instance(2, full2, full2, {(0, 0), (1, 0)})
    adversarial = {('R', 0, 0): ('ZR', 0, 0), ('R', 0, 1): ('ZR', 1, 1),
                   ('R', 1, 0): ('ZR', 1, 0), ('R', 1, 1): ('ZR', 0, 1)}
    yield 'repeated-H-positive', repeated, full2, [('H', 0, 0), ('H', 1, 0)], adversarial
    fixed_corners = instance(3, full2 | {(2, 2)}, full2 | {(2, 2)}, {(0, 0), (1, 0), (2, 2)})
    yield 'original-corners-retained', fixed_corners, full2, [('H', 0, 0), ('H', 1, 0)], None
    mixed = instance(3, full3, full3, {(i, 0) for i in range(3)})
    yield 'mixed-cover-positive', mixed, full3 - {(2, 2)}, [('R', 2, 0), ('R', 2, 1), ('H', 0, 0), ('H', 1, 0)], None
    asym = instance(2, full2, {(0, 0)}, {(0, 0), (0, 1), (1, 0)})
    yield 'asymmetric-auxiliaries', asym, {(0, 0)}, [('R', 0, 0)], None
    sharp = instance(8, {(p, 0) for p in (2, 3, 4)} | {(s, 1) for s in (5, 6, 7)},
                     {(p, 1) for p in (2, 3, 4)}, {(0, s) for s in (5, 6, 7)})
    yield 'inherited-sharp-core', sharp, {(2, 1)}, [('R', 2, 1)], None


def record(label, data, Wpairs, KB, supplied_alpha=None):
    *_, G = c.supports(data)
    W = {('R', *v) for v in Wpairs}
    _, M, _ = c.solve(c.left_restrict(G['L'], W))
    c.require(set(M) == W, 'fixture W not L-saturable')
    if supplied_alpha is not None:
        M = supplied_alpha
    request = {'W': [list(v) for v in sorted(Wpairs)], 'alpha': c.encode_matching(M),
               'KB': [list(v) for v in KB], 'order': list(range(data['n']))}
    return {'schema': 1, 'label': label, 'instance': data, 'request': request,
            'conversion': c.convert(data, request), 'accounting': c.normalized_accounting(G)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    args = parser.parse_args(); args.output.mkdir(parents=True, exist_ok=True)
    total = 0
    for params in named_inputs():
        result = record(*params)
        path = args.output / (params[0] + '.json')
        path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
        print('WROTE', path.name, 'branch=' + result['conversion']['branch'])
        total += 1
    print('Generated', total, 'fixed fixtures. No random input generation.')


if __name__ == '__main__':
    main()
