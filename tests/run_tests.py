#!/usr/bin/env python3
"""Bounded regression suite. Its finite outputs are NOT the general proof."""
from __future__ import annotations
import copy
import itertools
import json
from pathlib import Path
import platform
import random
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))
from construct import construct
from examples import cases, instance, sharp, transposed
from verify import InvalidCertificate, brute_force_original, rebuild, verify


def check(condition, message):
    if not condition:
        raise RuntimeError(message)


def emit(event, **fields):
    print(json.dumps({"event": event, **fields}, sort_keys=True), flush=True)


def transpose_check(data):
    o = rebuild(data)
    t = rebuild(transposed(data))
    def swap(v):
        kind, x, y = v.split(":")
        return {"R": "C", "C": "R", "ZL": "ZR", "ZR": "ZL", "H": "H"}[kind] + ":" + y + ":" + x
    check({(swap(v), swap(u)) for u, v in o["graphs"]["Gamma"][2]} == t["graphs"]["Gamma"][2], "Gamma transpose")
    check({(swap(v), swap(u)) for u, v in o["graphs"]["A0"][2]} == t["graphs"]["B0"][2], "A0/B0 transpose")
    check({(swap(v), swap(u)) for u, v in o["graphs"]["B0"][2]} == t["graphs"]["A0"][2], "B0/A0 transpose")
    check({z[::-1] for z in o["Z"]} == t["Z"] and {h[::-1] for h in o["H"]} == t["H"], "corner transpose")
    tc = construct(transposed(data))
    return verify(transposed(data), tc)


def main():
    start = time.perf_counter()
    emit("environment", python=sys.version, platform=platform.platform(), seed=17320261014,
         dependencies="Python standard library only")
    example_count = 0
    for data in cases():
        path = ROOT / "examples" / (data["name"] + ".certificate.json")
        cert = json.loads(path.read_text())
        check(cert == construct(data), "non-reproducible stored example " + data["name"])
        original_count = len(data["R"]) + len(data["C"])
        result = verify(data, cert, brute=original_count <= 12)
        transpose_check(data)
        emit("example", name=data["name"], **result)
        example_count += 1
    exhaustive_count, masks, feasible, negatives = 0, 0, 0, 0
    # ALL labeled inputs on X={0,...,n-1}; three arbitrary subsets of X x X.
    # No relabeling quotient or symmetry assumption is used.
    for n in range(3):
        pairs = list(itertools.product(range(n), repeat=2))
        subsets = [[p for i, p in enumerate(pairs) if (bits >> i) & 1]
                   for bits in range(1 << len(pairs))]
        count_n = 0
        for E, R, C in itertools.product(subsets, repeat=3):
            data = instance("exhaustive", n, E, R, C)
            cert = construct(data)
            result = verify(data, cert, brute=True)
            tr = transpose_check(data)
            check(tr["minimum"] == result["minimum"], "transpose objective")
            masks += result["brute_force"]["masks_considered"]
            feasible += result["brute_force"]["feasible"]
            negatives += int(result["minimum"] < 0)
            count_n += 1
        check(count_n == 2 ** (3 * n * n), "exhaustive coverage count")
        emit("exhaustive_n", n=n, inputs=count_n, status="PASS")
        exhaustive_count += count_n
    rng = random.Random(17320261014)
    random_count = 360
    for k in range(random_count):
        n = (3, 4, 5)[k % 3]
        pairs = list(itertools.product(range(n), repeat=2))
        density = (0.2, 0.5, 0.8)[(k // 3) % 3]
        E = [p for p in pairs if rng.random() < density]
        R = rng.sample(pairs, rng.randrange(7))
        C = rng.sample(pairs, rng.randrange(7))
        data = instance("seeded_random", n, E, R, C)
        result = verify(data, construct(data), brute=True)
        tr = transpose_check(data)
        check(tr["minimum"] == result["minimum"], "random transpose")
    # Independent enumeration of all matchings in two fixed small Gamma graphs,
    # in addition to the matching/cover certificate argument in verify.py.
    def brute_matching(L, R, E):
        L = sorted(L)
        def visit(pos, used):
            if pos == len(L):
                return 0
            best = visit(pos + 1, used)
            for u, v in E:
                if u == L[pos] and v not in used:
                    best = max(best, 1 + visit(pos + 1, used | {v}))
            return best
        return visit(0, set())
    for data in (sharp(2, 2), cases()[6]):
        o = rebuild(data)
        c = construct(data)
        for name, graph in o["graphs"].items():
            check(brute_matching(*graph) == c["graphs"][name]["size"], "brute matching disagrees")
    mutations = []
    base = sharp(2, 2)
    original = construct(base)
    def changed(label, mutate):
        c = copy.deepcopy(original)
        mutate(c)
        mutations.append((label, base, c))
    changed("false_beta", lambda c: c["stats"].__setitem__("beta", 0))
    changed("false_q", lambda c: c["pruning"].__setitem__("q", 1))
    changed("missing_H", lambda c: c["derived"]["H"].pop())
    changed("missing_Z", lambda c: c["derived"]["Z"].pop())
    changed("missing_cover_vertex", lambda c: c["graphs"]["Gamma"]["cover_left"].pop())
    changed("missing_matching_edge", lambda c: c["graphs"]["Gamma"]["matching"].pop())
    changed("duplicate_matching_edge", lambda c: c["graphs"]["Gamma"]["matching"].append(c["graphs"]["Gamma"]["matching"][0]))
    changed("forbidden_Z_Z_edge", lambda c: c["graphs"]["Gamma"]["edges"].append(["ZL:0:1", "ZR:0:1"]))
    changed("retained_conflict", lambda c: c["pruning"].update(R_retained=base["R"], C_retained=base["C"]))
    changed("duplicate_retained", lambda c: c["pruning"]["C_retained"].append(c["pruning"]["C_retained"][0]))
    altered = copy.deepcopy(base)
    altered["relation"].pop()
    mutations.append(("stale_input", altered, original))
    iso = next(x for x in cases() if x["name"] == "isolates_must_survive")
    c = construct(iso)
    c["pruning"]["R_retained"].remove([4, 4])
    mutations.append(("deleted_isolate", iso, c))
    for label, data, cert in mutations:
        try:
            verify(data, cert)
        except InvalidCertificate as exc:
            emit("mutation_rejected", name=label, reason=str(exc))
        else:
            raise RuntimeError("accepted bad certificate " + label)
    invalid_inputs = [
        {"schema": "family173.instance.v1", "n": -1, "relation": [], "R": [], "C": []},
        instance("out_of_range", 1, [(1, 0)], [], []),
        instance("duplicate_relation", 1, [(0, 0), (0, 0)], [], []),
        instance("bool_coordinate", 1, [], [(False, 0)], []),
    ]
    for data in invalid_inputs:
        for decoder in (construct, rebuild):
            try:
                decoder(data)
            except ValueError:
                pass
            else:
                raise RuntimeError("invalid input accepted")
    emit("summary", status="PASS", examples=example_count,
         exhaustive_inputs=exhaustive_count, exhaustive_retention_masks=masks,
         exhaustive_feasible_prunings=feasible, exhaustive_negative_optima=negatives,
         seeded_random_inputs=random_count, mutation_tests=len(mutations),
         invalid_input_tests=len(invalid_inputs), brute_matching_graphs=6,
         elapsed_seconds=round(time.perf_counter() - start, 3),
         scope="finite regression only; general theorem proved in MATHEMATICAL_NOTE.md")


if __name__ == "__main__":
    main()
