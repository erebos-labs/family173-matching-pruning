"""Replay the bounded seeded probes with independent exact certificates.

No atlas is written. Every size used is certified by a matching and an equally
sized vertex cover. Sampling is not exhaustive and proves no universal claim.
"""
from __future__ import annotations
import hashlib
import json
from itertools import product
from random import Random
import producer
import probe
import verify


def transpose(data):
    return {'n': data['n'], 'arrows': data['arrows'],
            'R': [[s, i] for i, s in data['C']],
            'C': [[j, p] for p, j in data['R']]}


def route_check(data, G, Z, H):
    # Reproduce the exact matchings used by the first exploratory probe.
    n, arrows, R, C = verify.input_data(data)
    _, _, _, L, N, _, _ = probe.supports(n, arrows, R, C)
    alpha, eta = probe.matching(L), probe.matching(N)
    alpha_tagged = {('R', *r): ('ZR', *z) for r, z in alpha.items()}
    eta_tagged = {('ZL', *z): ('C', *c) for z, c in eta.items()}
    verify.check_certificate(G['L'], producer.certificate(G['L'], alpha_tagged))
    verify.check_certificate(G['N'], producer.certificate(G['N'], eta_tagged))
    Cs = set(eta.values())
    unused = Z - set(alpha.values())
    left = {('C', *c) for c in Cs}
    right = {('H', *h) for h in H} | {('ZR', *z) for z in unused}
    # Producer uses coordinate predicates; verifier uses separately reconstructed
    # A and N supports. The candidate itself remains unproved in general.
    edges = {(('C', i, s), ('H', p, ss)) for i, s in Cs for p, ss in H
             if s == ss and (p, i) in arrows}
    edges |= {(('C', i, s), ('ZR', ii, j)) for i, s in Cs for ii, j in unused
              if i == ii and (s, j) in arrows}
    independent_edges = {(c, h) for h, c in G['A'][2] if c in left}
    independent_edges |= {(c, ('ZR', z[1], z[2])) for z, c in G['N'][2]
                          if c in left and (z[1], z[2]) in unused}
    verify.require(edges == independent_edges, 'routing support reconstruction mismatch')
    Q = (left, right, edges)
    cert = producer.certificate(Q)
    size = verify.check_certificate((left, right, independent_edges), cert)
    verify.require(size == len(Cs), 'fixed-alpha routing candidate counterexample')


def main():
    rng = Random(173)
    digest = hashlib.sha256()
    totals = {'original_inputs': 0, 'transposed_inputs': 0,
              'records_with_core': 0, 'normalization_L_steps': 0,
              'normalization_N_steps': 0, 'core_extension_steps': 0,
              'fixed_alpha_route_checks': 0}
    for n in range(1, 5):
        pairs = list(product(range(n), repeat=2))
        for trial in range(1000):
            data = {'n': n}
            for name in ['arrows', 'R', 'C']:
                data[name] = [list(e) for e in pairs if rng.random() < 0.45]
            digest.update((json.dumps(data, sort_keys=True, separators=(',', ':')) + '\n').encode())
            for direction, instance in [('original_inputs', data), ('transposed_inputs', transpose(data))]:
                record = producer.make_record(instance)
                G, Z, H = verify.reconstruct(instance)
                verify.require(producer.graphs(instance) == G, 'independent support reconstruction mismatch')
                result = verify.verify_record(record)
                totals[direction] += 1
                totals['records_with_core'] += int(result['k'] > 0)
                for step in record['normalization_trace']:
                    totals['normalization_' + step['side'] + '_steps'] += 1
                totals['core_extension_steps'] += len(record['core_extension']['paths'])
                if direction == 'original_inputs':
                    route_check(instance, G, Z, H)
                    totals['fixed_alpha_route_checks'] += 1
        print('completed_n', n, 'original_inputs', totals['original_inputs'], flush=True)
    print('input_stream_sha256', digest.hexdigest())
    print('totals', json.dumps(totals, sort_keys=True))
    print('equal_size_matching_cover_certificates_checked', verify.CHECK_COUNT)
    print('PASS: bounded falsification checks only; no universal proof or novelty claim.')


if __name__ == '__main__':
    main()
