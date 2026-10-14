"""Exact fixture/certificate producer. Standard library only.

No claim that computation proves the unbounded capacity theorem.  The independent
verifier imports neither this module nor the exploratory probe.
"""
from __future__ import annotations
import json
from collections import deque
from pathlib import Path

Vertex = tuple[str, int, int]


def tagged(kind, pair):
    return (kind, *pair)


def graphs(instance):
    R = {tuple(x) for x in instance['R']}
    C = {tuple(x) for x in instance['C']}
    arrows = {tuple(x) for x in instance['arrows']}
    F = {(r, c) for r in R for c in C
         if (r[0], c[0]) in arrows and (c[1], r[1]) in arrows}
    Z = {(c[0], r[1]) for r, c in F}
    H = {(r[0], c[1]) for r, c in F}
    RR, CC = {tagged('R', r) for r in R}, {tagged('C', c) for c in C}
    ZL, ZR = {tagged('ZL', z) for z in Z}, {tagged('ZR', z) for z in Z}
    HH = {tagged('H', h) for h in H}
    L = {(tagged('R', r), tagged('ZR', z)) for r in R for z in Z
         if r[1] == z[1] and (r[0], z[0]) in arrows}
    N = {(tagged('ZL', z), tagged('C', c)) for z in Z for c in C
         if z[0] == c[0] and (c[1], z[1]) in arrows}
    B = {(tagged('R', r), tagged('H', h)) for r in R for h in H
         if r[0] == h[0] and (h[1], r[1]) in arrows}
    A = {(tagged('H', h), tagged('C', c)) for h in H for c in C
         if h[1] == c[1] and (h[0], c[0]) in arrows}
    G = {(tagged('R', r), tagged('C', c)) for r, c in F} | L | N
    return {'Gamma': (RR | ZL, CC | ZR, G), 'L': (RR, ZR, L),
            'N': (ZL, CC, N), 'B': (RR, HH, B), 'A': (HH, CC, A)}


def adjacency(graph):
    left, right, edges = graph
    return {u: sorted(v for x, v in edges if x == u) for u in sorted(left)}


def augment(graph, matching):
    """One BFS augmenting path, preserving all previously saturated left vertices."""
    adj = adjacency(graph)
    mate = dict(matching)
    reverse = {v: u for u, v in mate.items()}
    roots = sorted(set(adj) - set(mate))
    queue, reached = deque(roots), set(roots)
    parent_right = {}
    while queue:
        u = queue.popleft()
        for v in adj[u]:
            if mate.get(u) == v or v in parent_right:
                continue
            parent_right[v] = u
            if v not in reverse:
                # Backtrack before changing any edges.
                backward = [v]
                w = v
                while True:
                    x = parent_right[w]
                    backward.append(x)
                    old = mate.get(x)
                    if old is None:
                        root = x
                        break
                    backward.append(old)
                    w = old
                path = list(reversed(backward))
                for x in path[0::2]:
                    mate.pop(x, None)
                for x, w in zip(path[0::2], path[1::2]):
                    mate[x] = w
                return mate, path, root
            x = reverse[v]
            if x not in reached:
                reached.add(x)
                queue.append(x)
    return None


def maximum(graph, initial=None):
    mate = {} if initial is None else dict(initial)
    trace = []
    while True:
        step = augment(graph, mate)
        if step is None:
            return mate, trace
        mate, path, root = step
        trace.append(path)


def cover(graph, mate):
    adj = adjacency(graph)
    reverse = {v: u for u, v in mate.items()}
    WL = set(adj) - set(mate)
    WR = set()
    queue = deque(sorted(WL))
    while queue:
        u = queue.popleft()
        for v in adj[u]:
            if mate.get(u) == v or v in WR:
                continue
            WR.add(v)
            if v in reverse and reverse[v] not in WL:
                WL.add(reverse[v])
                queue.append(reverse[v])
    return (set(adj) - WL) | WR


def certificate(graph, mate=None):
    if mate is None:
        mate, _ = maximum(graph)
    return {'matching': sorted(mate.items()), 'cover': sorted(cover(graph, mate))}


def delete_vertex(graph, vertex):
    L, R, E = graph
    return L - {vertex}, R - {vertex}, {(u, v) for u, v in E if vertex not in (u, v)}


def induced_left(graph, vertices):
    L, R, E = graph
    return L & vertices, R, {(u, v) for u, v in E if u in vertices}


def reverse_graph(graph):
    L, R, E = graph
    return R, L, {(v, u) for u, v in E}


def normalize(G, initial=None):
    """Source's augment/remove normalization, not an algebraic algorithm."""
    mate, _ = maximum(G['Gamma'], initial)
    start = dict(mate)
    trace = []
    while True:
        alpha = {u: v for u, v in mate.items() if u[0] == 'R' and v[0] == 'ZR'}
        step = augment(G['L'], alpha)
        if step is None:
            break
        new, path, root = step
        old = mate.pop(root)  # A maximum Gamma matching must match root to C.
        if old[0] != 'C':
            raise ValueError('invalid normalization root')
        for u in alpha:
            mate.pop(u)
        mate.update(new)
        trace.append({'side': 'L', 'removed': (root, old), 'path': path})
    while True:
        beta_reverse = {v: u for u, v in mate.items() if u[0] == 'ZL' and v[0] == 'C'}
        step = augment(reverse_graph(G['N']), beta_reverse)
        if step is None:
            break
        new, path, root = step
        predecessor = next(u for u, v in mate.items() if v == root)
        if predecessor[0] != 'R':
            raise ValueError('invalid normalization root')
        mate.pop(predecessor)
        for u in beta_reverse.values():
            mate.pop(u)
        mate.update({u: v for v, u in new.items()})
        trace.append({'side': 'N', 'removed': (predecessor, root), 'path': path})
    return mate, trace, start


def make_record(instance):
    G = graphs(instance)
    supplied = {tuple(u): tuple(v) for u, v in instance.get('supplied_M', [])}
    mate, trace, start = normalize(G, supplied)
    certs = {name: certificate(g, mate if name == 'Gamma' else None) for name, g in G.items()}
    core = {u for u, v in mate.items() if u[0] == 'R' and v[0] == 'C'}
    alpha = {u: v for u, v in mate.items() if u[0] == 'R' and v[0] == 'ZR'}
    eta = {u: v for u, v in mate.items() if u[0] == 'ZL' and v[0] == 'C'}
    certs['L'] = certificate(G['L'], alpha)
    certs['N'] = certificate(G['N'], eta)
    Balpha = induced_left(G['B'], set(alpha))
    Bminus = induced_left(G['B'], G['B'][0] - core)
    certs['Balpha'] = certificate(Balpha)
    certs['Bminus'] = certificate(Bminus)
    exposure = {}
    for name, side, label in [('B', 0, 'B_left'), ('N', 0, 'N_left'),
                               ('N', 1, 'N_right'), ('A', 1, 'A_right')]:
        exposure[label] = [{'removed': u, 'certificate': certificate(delete_vertex(G[name], u))}
                           for u in sorted(G[name][side])]
    initial = {tuple(u): tuple(v) for u, v in certs['Balpha']['matching']}
    extended, extension_trace = maximum(G['B'], initial)
    wanted = core | set(initial)
    selected = {u: v for u, v in extended.items() if u in wanted}
    return {'schema': 1, 'instance': instance, 'certificates': certs,
            'normalization_start': sorted(start.items()),
            'normalization_trace': trace, 'exposure_deletions': exposure,
            'core_extension': {'paths': extension_trace, 'final': certificate(G['B'], extended),
                               'selected': sorted(selected.items())}}


def sharp(n):
    return {'n': 2 + 2*n, 'arrows': [[2+a, 0] for a in range(n)] +
            [[2+n+b, 1] for b in range(n)], 'R': [[2+a, 1] for a in range(n)],
            'C': [[0, 2+n+b] for b in range(n)]}


def fixture_inputs():
    all2 = [[i, j] for i in range(2) for j in range(2)]
    rectangle = {'n': 2, 'arrows': [[0, 0], [0, 1]],
                 'R': [[0, 0], [0, 1]], 'C': [[0, 0], [1, 0]],
                 'supplied_M': [[['R', 0, 0], ['ZR', 0, 0]],
                                [['R', 0, 1], ['ZR', 1, 1]],
                                [['ZL', 0, 0], ['C', 0, 0]],
                                [['ZL', 1, 1], ['C', 1, 0]]]}
    isolated = sharp(2)
    isolated['n'] += 1
    isolated['R'].append([6, 6])
    isolated['C'].append([6, 6])
    return {
        'empty-X': {'n': 0, 'arrows': [], 'R': [], 'C': []},
        'empty-R': {'n': 2, 'arrows': all2, 'R': [], 'C': [[0, 0], [1, 1]]},
        'empty-C': {'n': 2, 'arrows': all2, 'R': [[0, 0], [1, 1]], 'C': []},
        'no-conflicts': {'n': 2, 'arrows': [[0, 0]], 'R': [[1, 1]], 'C': [[1, 1]]},
        'one-loop-all-tags': {'n': 1, 'arrows': [[0, 0]], 'R': [[0, 0]], 'C': [[0, 0]]},
        'opposite-arrows': {'n': 2, 'arrows': [[0, 1], [1, 0]],
                            'R': [[0, 0], [1, 1]], 'C': [[0, 0], [1, 1]]},
        'hall-shortcut-failure': rectangle,
        'asymmetric-auxiliaries': {'n': 2, 'arrows': all2, 'R': [[0, 0]],
                                  'C': [[0, 0], [0, 1], [1, 0]]},
        'negative-integer-optimum': {'n': 3, 'arrows': [[0, j] for j in range(3)],
                                    'R': [[0, j] for j in range(3)],
                                    'C': [[i, 0] for i in range(3)]},
        'sharp-n3': sharp(3),
        'sharp-plus-isolated': isolated,
    }


def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    for name, instance in sorted(fixture_inputs().items()):
        record = make_record(instance)
        (args.output / (name + '.json')).write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
        print('produced', name)

if __name__ == '__main__':
    main()
