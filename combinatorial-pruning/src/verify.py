"""Standalone exact verifier, independently reconstructed from the definitions.

Does not import producer.py or probe.py and does not run a matching optimizer.
An equally sized legal matching and vertex cover certify each optimum. The only
exhaustive step is optional enumeration of prunings on the eleven small fixtures.

Public v1.1.0 change: decode every certificate vertex with exact integer
coordinates; Boolean/float aliases and non-integer schema versions are rejected.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
from pathlib import Path

CHECK_COUNT = 0


def require(condition, message):
    if not condition:
        raise ValueError(message)


def certificate_vertex(value):
    require(isinstance(value, (list, tuple)) and len(value) == 3,
            'certificate vertex must have three fields')
    require(type(value[0]) is str and value[0] in {'R', 'C', 'H', 'ZL', 'ZR'},
            'invalid certificate vertex tag')
    require(all(type(x) is int for x in value[1:]),
            'certificate coordinates must be exact integers')
    return tuple(value)


def input_data(data):
    n = data['n']
    require(type(n) is int and n >= 0, 'n must be a nonnegative integer')
    sets = []
    for name in ['arrows', 'R', 'C']:
        seq = data[name]
        require(isinstance(seq, list), 'pair collection must be a list')
        require(all(isinstance(e, (list, tuple)) and len(e) == 2 and
                    all(type(v) is int and 0 <= v < n for v in e) for e in seq), 'invalid pair')
        result = set(map(tuple, seq))
        require(len(result) == len(seq), 'duplicate input pair')
        sets.append(result)
    return n, *sets


def reconstruct(data):
    # Factor the two existential conditions for each corner separately. This
    # deliberately differs from the producer's projection of its conflict list.
    n, arrows, R, C = input_data(data)
    arrow = [[(x, y) in arrows for y in range(n)] for x in range(n)]
    Z, H = set(), set()
    for i in range(n):
        for j in range(n):
            if (any((p, j) in R and arrow[p][i] for p in range(n)) and
                any((i, s) in C and arrow[s][j] for s in range(n))):
                Z.add((i, j))
    for p in range(n):
        for s in range(n):
            if (any((p, j) in R and arrow[s][j] for j in range(n)) and
                any((i, s) in C and arrow[p][i] for i in range(n))):
                H.add((p, s))
    RR = {('R', p, j) for p, j in R}
    CC = {('C', i, s) for i, s in C}
    HH = {('H', p, s) for p, s in H}
    ZL, ZR = {('ZL', i, j) for i, j in Z}, {('ZR', i, j) for i, j in Z}
    output = {}
    for name, left, right in [('Gamma', RR | ZL, CC | ZR), ('L', RR, ZR),
                               ('N', ZL, CC), ('B', RR, HH), ('A', HH, CC)]:
        edges = set()
        for u in left:
            for v in right:
                kind = (u[0], v[0])
                ok = False
                if kind == ('R', 'C'):
                    ok = arrow[u[1]][v[1]] and arrow[v[2]][u[2]]
                elif kind == ('R', 'ZR'):
                    ok = u[2] == v[2] and arrow[u[1]][v[1]]
                elif kind == ('ZL', 'C'):
                    ok = u[1] == v[1] and arrow[v[2]][u[2]]
                elif kind == ('R', 'H'):
                    ok = u[1] == v[1] and arrow[v[2]][u[2]]
                elif kind == ('H', 'C'):
                    ok = u[2] == v[2] and arrow[u[1]][v[1]]
                if ok:
                    edges.add((u, v))
        require(not left & right, 'tags not disjoint')
        output[name] = (left, right, edges)
    return output, Z, H


def matching_dict(graph, sequence):
    left, right, edges = graph
    pairs = [(certificate_vertex(u), certificate_vertex(v)) for u, v in sequence]
    require(all(u in left and v in right and (u, v) in edges for u, v in pairs), 'illegal matching edge')
    require(len({u for u, v in pairs}) == len(pairs), 'repeated left endpoint')
    require(len({v for u, v in pairs}) == len(pairs), 'repeated right endpoint')
    return dict(pairs)


def check_certificate(graph, cert):
    global CHECK_COUNT
    left, right, edges = graph
    mate = matching_dict(graph, cert['matching'])
    cover_sequence = [certificate_vertex(v) for v in cert['cover']]
    cover = set(cover_sequence)
    require(len(cover) == len(cover_sequence), 'duplicate cover vertex')
    require(cover <= left | right, 'cover outside graph')
    require(all(u in cover or v in cover for u, v in edges), 'uncovered edge')
    require(len(cover) == len(mate), 'matching and cover differ in size')
    CHECK_COUNT += 1
    return len(mate)


def removed_graph(graph, vertex):
    left, right, edges = graph
    return left - {vertex}, right - {vertex}, {(u, v) for u, v in edges if u != vertex and v != vertex}


def left_subgraph(graph, vertices):
    left, right, edges = graph
    return left & vertices, right, {(u, v) for u, v in edges if u in vertices}


def invert(graph):
    left, right, edges = graph
    return right, left, {(v, u) for u, v in edges}


def apply_augment(graph, mate, raw_path):
    path = [certificate_vertex(v) for v in raw_path]
    L, R, E = graph
    require(len(path) >= 2 and len(path) % 2 == 0 and len(path) == len(set(path)), 'bad path')
    require(set(path[0::2]) <= L and set(path[1::2]) <= R, 'path sides')
    require(path[0] not in mate and path[-1] not in set(mate.values()), 'path endpoints not free')
    for pos in range(len(path) - 1):
        u, v = (path[pos], path[pos+1]) if pos % 2 == 0 else (path[pos+1], path[pos])
        require((u, v) in E, 'path edge absent')
        require((mate.get(u) == v) == (pos % 2 == 1), 'path not alternating')
    out = dict(mate)
    for u in path[2::2]:
        out.pop(u)
    for u, v in zip(path[0::2], path[1::2]):
        out[u] = v
    matching_dict(graph, list(out.items()))
    require(len(out) == len(mate) + 1 and set(mate) <= set(out), 'augmentation loses capacity')
    return out


def tau(v):
    return ({'R': 'C', 'C': 'R', 'ZL': 'ZR', 'ZR': 'ZL', 'H': 'H'}[v[0]], v[2], v[1])


def transpose_checks(data, G, certs):
    transposed = {'n': data['n'], 'arrows': data['arrows'],
                  'R': [list(reversed(c)) for c in data['C']],
                  'C': [list(reversed(r)) for r in data['R']]}
    GT, ZT, HT = reconstruct(transposed)
    mapping = {'Gamma': 'Gamma', 'B': 'A', 'A': 'B', 'L': 'N', 'N': 'L'}
    for old, new in mapping.items():
        L, R, E = G[old]
        expected = ({tau(v) for v in R}, {tau(u) for u in L}, {(tau(v), tau(u)) for u, v in E})
        require(expected == GT[new], 'transposed support mismatch: ' + old)
        cert = certs[old]
        transformed = {'matching': [(tau(v), tau(u)) for u, v in cert['matching']],
                       'cover': [tau(v) for v in cert['cover']]}
        check_certificate(GT[new], transformed)


def pruning_optimum(data, G, Z):
    n, arrows, R, C = input_data(data)
    originals = sorted(G['L'][0] | G['N'][1])
    require(len(originals) <= 20, 'fixture pruning enumeration limited to 20 originals')
    conflicts = {(u, v) for u, v in G['Gamma'][2] if u[0] == 'R' and v[0] == 'C'}
    incident = {v for e in conflicts for v in e}
    initially_free = set(originals) - incident
    best, feasible = None, 0
    for mask in range(1 << len(originals)):
        keep = {v for bit, v in enumerate(originals) if mask >> bit & 1}
        if not initially_free <= keep or any(u in keep and v in keep for u, v in conflicts):
            continue
        feasible += 1
        deleted = set(originals) - keep
        K = set(deleted)
        q = 0
        for i, j in Z:  # Original Z is never recomputed after pruning.
            lc = any(k == 'R' and y == j and (x, i) in arrows for k, x, y in keep)
            rc = any(k == 'C' and x == i and (y, j) in arrows for k, x, y in keep)
            require(not (lc and rc), 'two-sided coverage in a conflict-free pruning')
            if lc:
                K.add(('ZR', i, j))
            elif rc:
                K.add(('ZL', i, j))
            else:
                q += 1
        value = len(deleted) - q
        require(len(K) == len(Z) + value, 'pruning cover count')
        require(all(u in K or v in K for u, v in G['Gamma'][2]), 'pruning did not give cover')
        best = value if best is None else min(best, value)
    require(best is not None, 'no admissible pruning')
    return best, feasible


def verify_record(record, pruning=False):
    require(type(record['schema']) is int and record['schema'] == 1, 'unknown schema')
    data, certs = record['instance'], record['certificates']
    G, Z, H = reconstruct(data)
    sizes = {name: check_certificate(graph, certs[name]) for name, graph in G.items()}
    final_mate = matching_dict(G['Gamma'], certs['Gamma']['matching'])
    core_pairs = {(u, v) for u, v in final_mate.items() if u[0] == 'R' and v[0] == 'C'}
    core = {u for u, v in core_pairs}
    alpha = {u: v for u, v in final_mate.items() if v[0] == 'ZR'}
    eta = {u: v for u, v in final_mate.items() if u[0] == 'ZL'}
    require(list(sorted(alpha.items())) == list(sorted(matching_dict(G['L'], certs['L']['matching']).items())), 'alpha differs')
    require(list(sorted(eta.items())) == list(sorted(matching_dict(G['N'], certs['N']['matching']).items())), 'eta differs')
    k, ell, t = len(core), len(alpha), len(eta)
    require(k + ell + t == sizes['Gamma'], 'normalization counts')
    # Replay source normalization, validating the intermediate matchings.
    current = matching_dict(G['Gamma'], record['normalization_start'])
    require(len(current) == sizes['Gamma'], 'normalization did not start maximum')
    for step in record['normalization_trace']:
        removed = tuple(certificate_vertex(v) for v in step['removed'])
        require(removed in set(current.items()) and removed[0][0] == 'R' and removed[1][0] == 'C', 'bad removed core edge')
        if step['side'] == 'L':
            old = {u: v for u, v in current.items() if v[0] == 'ZR'}
            require(certificate_vertex(step['path'][0]) == removed[0], 'wrong L root')
            new = apply_augment(G['L'], old, step['path'])
            current.pop(removed[0])
            for u in old:
                current.pop(u)
            current.update(new)
        else:
            require(step['side'] == 'N', 'unknown normalization side')
            old = {v: u for u, v in current.items() if u[0] == 'ZL'}
            require(certificate_vertex(step['path'][0]) == removed[1], 'wrong N root')
            new = apply_augment(invert(G['N']), old, step['path'])
            current.pop(removed[0])
            for u in old.values():
                current.pop(u)
            current.update({u: v for v, u in new.items()})
        matching_dict(G['Gamma'], list(current.items()))
        require(len(current) == sizes['Gamma'], 'normalization changed size')
    require(current == final_mate, 'normalization trace ends elsewhere')
    exposures = {}
    for label, name, side in [('B_left', 'B', 0), ('N_left', 'N', 0),
                               ('N_right', 'N', 1), ('A_right', 'A', 1)]:
        seen, exposed = set(), set()
        for item in record['exposure_deletions'][label]:
            u = certificate_vertex(item['removed'])
            require(u in G[name][side] and u not in seen, 'bad deletion index')
            seen.add(u)
            value = check_certificate(removed_graph(G[name], u), item['certificate'])
            require(value in (sizes[name], sizes[name] - 1), 'deletion count')
            if value == sizes[name]:
                exposed.add(u)
        require(seen == G[name][side], 'incomplete exposure classification')
        exposures[label] = exposed
    E_B, E_N = exposures['B_left'], exposures['N_left']
    W = {('ZL', v[1], v[2]) for u, v in G['L'][2] if u in E_B}
    require(W <= E_N, 'exposure transfer')
    require(not any(u in E_N and v in exposures['N_right'] for u, v in G['N'][2]), 'opposite exposed vertices adjacent')
    require(not core & E_B, 'core left endpoint not mandatory')
    require(not {v for u, v in core_pairs} & exposures['A_right'], 'core right endpoint not mandatory')
    ba = check_certificate(left_subgraph(G['B'], set(alpha)), certs['Balpha'])
    bm = check_certificate(left_subgraph(G['B'], G['B'][0] - core), certs['Bminus'])
    require(sizes['B'] == k + bm, 'mandatory-core deletion identity')
    require(sizes['B'] >= k + ba, 'core plus auxiliary submatching')
    extension = record['core_extension']
    cur = matching_dict(G['B'], certs['Balpha']['matching'])
    initial_keys = set(cur)
    for path in extension['paths']:
        cur = apply_augment(G['B'], cur, path)
    check_certificate(G['B'], extension['final'])
    require(cur == matching_dict(G['B'], extension['final']['matching']), 'extension trace ends elsewhere')
    selected = matching_dict(G['B'], extension['selected'])
    require(set(selected) == core | initial_keys and set(selected.items()) <= set(cur.items()), 'bad core extension selection')
    require(len(selected) == k + ba, 'core extension count')
    # These two tests are sanity checks of the established inequality, not proof.
    require(sizes['Gamma'] <= len(Z) + min(sizes['B'], sizes['A']), 'baseline capacity inequality')
    require(ba >= ell + t - len(Z), 'unproved rank-free auxiliary step failed numerically')
    transpose_checks(data, G, certs)
    hall_set = E_B | E_N
    hall_neighbors = {v for u, v in G['Gamma'][2] if u in hall_set}
    shortcut = len(hall_set) - len(hall_neighbors)
    delta_B = len(G['B'][0]) - sizes['B']
    result = dict(sizes, Z=len(Z), H=len(H), k=k, ell=ell, t=t,
                  delta_B=delta_B, shortcut_deficiency=shortcut)
    if pruning:
        optimum, count = pruning_optimum(data, G, Z)
        require(optimum == sizes['Gamma'] - len(Z), 'original-Z pruning optimum')
        result.update(pruning_optimum=optimum, admissible_prunings=count)
    return result


def mutation_tests(records):
    record = records['one-loop-all-tags']
    G, _, _ = reconstruct(record['instance'])
    original = record['certificates']['Gamma']
    mutants = []
    m = copy.deepcopy(original); m['matching'] = m['matching'][:-1]; mutants.append(m)
    m = copy.deepcopy(original); m['matching'].append(m['matching'][0]); mutants.append(m)
    m = copy.deepcopy(original); m['cover'] = m['cover'][:-1]; mutants.append(m)
    m = copy.deepcopy(original); m['cover'].append(m['cover'][0]); mutants.append(m)
    m = copy.deepcopy(original); m['matching'][0][0][0] = 'H'; mutants.append(m)
    m = copy.deepcopy(original); m['matching'][0][1][2] = 99; mutants.append(m)
    for number, cert in enumerate(mutants):
        try:
            check_certificate(G['Gamma'], cert)
        except ValueError:
            continue
        raise ValueError('mutation accepted: ' + str(number))
    return len(mutants)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fixtures', type=Path, default=Path(__file__).resolve().parents[1] / 'fixtures')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    data = (root / 'sources/02-pruning.pinned.tex').read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    require(blob == '4fe3b01285d67d6fb5a5e7a8798a3c12f432ff76', 'source blob hash mismatch')
    print('source_bytes', len(data), 'git_blob_sha1', blob)
    print('source_sha256', hashlib.sha256(data).hexdigest())
    records, results = {}, {}
    for path in sorted(args.fixtures.glob('*.json')):
        record = json.loads(path.read_text())
        result = verify_record(record, pruning=True)
        records[path.stem], results[path.stem] = record, result
        print(path.stem, json.dumps(result, sort_keys=True))
    require(len(records) == 11, 'wrong fixture count')
    r = results['hall-shortcut-failure']
    require(r['shortcut_deficiency'] == 0 and r['delta_B'] == 1 and r['Gamma'] == 4 and r['Z'] == 4 and r['B'] == 1, 'shortcut counterexample changed')
    require(results['asymmetric-auxiliaries']['ell'] == 1 and results['asymmetric-auxiliaries']['t'] == 2, 'asymmetry lost')
    require(results['negative-integer-optimum']['pruning_optimum'] == -3, 'ordinary integer subtraction lost')
    r = results['sharp-n3']
    require((r['Z'], r['H'], r['B'], r['A'], r['Gamma'], r['pruning_optimum']) == (1, 9, 3, 3, 4, 3), 'sharpness sanity')
    print('rejected_certificate_mutations', mutation_tests(records))
    print('equal_size_matching_cover_certificates_checked', CHECK_COUNT)
    print('PASS: eleven fixtures and their exact transpositions; finite evidence only.')

if __name__ == '__main__':
    main()
