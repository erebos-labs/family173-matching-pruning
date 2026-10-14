#!/usr/bin/env python3
"""Construct exact matching/cover and optimal-pruning certificates.

Python 3.10+, standard library only. This file does not import the verifier.
The algorithm never chooses coefficients or uses numerical matrix ranks.
"""
from __future__ import annotations
import argparse
from collections import deque
import hashlib
import json
from pathlib import Path


def read_instance(data: dict) -> tuple[int, set, list, list]:
    if not isinstance(data, dict) or data.get("schema") != "family173.instance.v1":
        raise ValueError("Expected family173.instance.v1")
    n = data.get("n")
    if type(n) is not int or n < 0:
        raise ValueError("n must be a nonnegative integer")
    out = []
    for name in ("relation", "R", "C"):
        seq = data.get(name)
        if not isinstance(seq, list):
            raise ValueError(f"{name} must be a list")
        pairs = []
        for pair in seq:
            if (not isinstance(pair, list) or len(pair) != 2
                    or any(type(x) is not int or not 0 <= x < n for x in pair)):
                raise ValueError(f"Invalid pair in {name}: {pair!r}")
            pairs.append(tuple(pair))
        if len(set(pairs)) != len(pairs):
            raise ValueError(f"Duplicate pair in {name}")
        out.append(sorted(pairs))
    return n, set(out[0]), out[1], out[2]


def vertex(tag: str, pair: tuple) -> str:
    return f"{tag}:{pair[0]}:{pair[1]}"


def canonical_hash(data: dict) -> str:
    return hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":"),
                                    ensure_ascii=True).encode("ascii")).hexdigest()


def make_objects(data: dict) -> dict:
    _, relation, R, C = read_instance(data)
    conflicts, Z, H = [], set(), set()
    for r in R:
        p, j = r
        for c in C:
            i, s = c
            if (p, i) in relation and (s, j) in relation:
                conflicts.append((vertex("R", r), vertex("C", c)))
                Z.add((i, j))
                H.add((p, s))
    edges = set(conflicts)
    for p, j in R:
        for i, jj in Z:
            if j == jj and (p, i) in relation:
                edges.add((vertex("R", (p, j)), vertex("ZR", (i, j))))
    for i, s in C:
        for ii, j in Z:
            if i == ii and (s, j) in relation:
                edges.add((vertex("ZL", (i, j)), vertex("C", (i, s))))
    B = {(vertex("R", (p, j)), vertex("H", (pp, s)))
         for p, j in R for pp, s in H if p == pp and (s, j) in relation}
    A = {(vertex("H", (p, ss)), vertex("C", (i, s)))
         for p, ss in H for i, s in C if s == ss and (p, i) in relation}
    graphs = {
        "Gamma": (sorted([vertex("R", r) for r in R] + [vertex("ZL", z) for z in Z]),
                  sorted([vertex("C", c) for c in C] + [vertex("ZR", z) for z in Z]), edges),
        "B0": (sorted(vertex("R", r) for r in R), sorted(vertex("H", h) for h in H), B),
        "A0": (sorted(vertex("H", h) for h in H), sorted(vertex("C", c) for c in C), A),
    }
    return {"R": R, "C": C, "Z": sorted(Z), "H": sorted(H),
            "conflicts": sorted(conflicts), "graphs": graphs, "relation": relation}


def matching_cover(left: list[str], right: list[str], edges: set) -> dict:
    """Repeated breadth-first augmenting paths; then alternating-path cover."""
    adjacency = {u: [] for u in left}
    for u, v in sorted(edges):
        adjacency[u].append(v)
    ml, mr = {}, {}
    while True:
        seen_left = {u for u in left if u not in ml}
        queue = deque(sorted(seen_left))
        parent_right = {}
        free = None
        while queue and free is None:
            u = queue.popleft()
            for v in adjacency[u]:
                if v == ml.get(u) or v in parent_right:
                    continue
                parent_right[v] = u
                if v not in mr:
                    free = v
                    break
                w = mr[v]
                if w not in seen_left:
                    seen_left.add(w)
                    queue.append(w)
        if free is None:
            break
        v = free
        while v is not None:
            u = parent_right[v]
            previous = ml.get(u)
            ml[u], mr[v] = v, u
            if previous is not None:
                del mr[previous]
            v = previous
    reached_left = {u for u in left if u not in ml}
    reached_right = set()
    queue = deque(sorted(reached_left))
    while queue:
        u = queue.popleft()
        for v in adjacency[u]:
            if v == ml.get(u) or v in reached_right:
                continue
            reached_right.add(v)
            if v not in mr:
                raise RuntimeError("Internal error: an augmenting path remains")
            w = mr[v]
            if w not in reached_left:
                reached_left.add(w)
                queue.append(w)
    return {
        "left": left, "right": right, "edges": [list(e) for e in sorted(edges)],
        "matching": [list(e) for e in sorted(ml.items())],
        "cover_left": sorted(set(left) - reached_left),
        "cover_right": sorted(reached_right), "size": len(ml),
    }


def construct(data: dict) -> dict:
    o = make_objects(data)
    graphs = {name: matching_cover(*g) for name, g in o["graphs"].items()}
    gamma = graphs["Gamma"]
    cover = set(gamma["cover_left"]) | set(gamma["cover_right"])
    Rkeep = [r for r in o["R"] if vertex("R", r) not in cover]
    Ckeep = [c for c in o["C"] if vertex("C", c) not in cover]
    uncovered = [(i, j) for i, j in o["Z"]
                 if not any(jj == j and (p, i) in o["relation"] for p, jj in Rkeep)
                 and not any(ii == i and (s, j) in o["relation"] for ii, s in Ckeep)]
    deletions = len(o["R"]) + len(o["C"]) - len(Rkeep) - len(Ckeep)
    beta = min(graphs["B0"]["size"], graphs["A0"]["size"])
    return {
        "schema": "family173.certificate.v1", "instance_sha256": canonical_hash(data),
        "derived": {"Z": [list(z) for z in o["Z"]], "H": [list(h) for h in o["H"]],
                    "conflicts": [list(e) for e in o["conflicts"]]},
        "graphs": graphs,
        "stats": {"Z": len(o["Z"]), "H": len(o["H"]),
                  "nu_B0": graphs["B0"]["size"], "nu_A0": graphs["A0"]["size"],
                  "beta": beta, "nu_Gamma": gamma["size"]},
        "pruning": {"R_retained": [list(r) for r in Rkeep],
                    "C_retained": [list(c) for c in Ckeep],
                    "uncovered": [list(z) for z in uncovered],
                    "deletions": deletions, "q": len(uncovered),
                    "value": deletions - len(uncovered)},
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("instance", type=Path)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    try:
        data = json.loads(args.instance.read_text(encoding="utf-8"))
        result = construct(data)
        args.certificate.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    except (OSError, ValueError, TypeError, KeyError) as exc:
        parser.exit(1, f"ERROR: {exc}\n")
    print(json.dumps({"certificate": str(args.certificate), **result["stats"],
                      "deletions_minus_q": result["pruning"]["value"]}, sort_keys=True))


if __name__ == "__main__":
    main()
