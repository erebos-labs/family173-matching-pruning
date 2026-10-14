#!/usr/bin/env python3
"""Finite instances of the proved families, plus boundary/regression cases."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from construct import construct


def instance(name: str, n: int, relation, R, C) -> dict:
    return {"schema": "family173.instance.v1", "name": name, "n": n,
            "relation": [list(x) for x in sorted(relation)],
            "R": [list(x) for x in sorted(R)], "C": [list(x) for x in sorted(C)]}


def sharp(m: int, n: int) -> dict:
    """Distinct roles i=0,j=1,p=2..m+1,s=m+2..m+n+1; acyclic arrows."""
    if m < 1 or n < 1:
        raise ValueError("m and n must be positive")
    P, S = range(2, m + 2), range(m + 2, m + n + 2)
    return instance(f"sharp_{m}x{n}", m + n + 2,
                    [(p, 0) for p in P] + [(s, 1) for s in S],
                    [(p, 1) for p in P], [(0, s) for s in S])


def grid(n: int) -> dict:
    """One H point, n^2 Z points; objective 2n-n^2 can be negative."""
    if n < 1:
        raise ValueError("n must be positive")
    I, J = range(2, n + 2), range(n + 2, 2 * n + 2)
    return instance(f"grid_{n}", 2 * n + 2,
                    [(0, i) for i in I] + [(1, j) for j in J],
                    [(0, j) for j in J], [(i, 1) for i in I])


def transposed(data: dict) -> dict:
    # Relation is NOT reversed. Original sides exchange and every pair reverses.
    return instance(data["name"] + "_transpose", data["n"], data["relation"],
                    [(s, i) for i, s in data["C"]], [(j, p) for p, j in data["R"]])


def cases() -> list[dict]:
    out = [
        instance("empty_X", 0, [], [], []),
        instance("empty_families", 2, [(0, 0), (0, 1), (1, 0), (1, 1)], [], []),
        instance("no_relation_coinciding", 2, [], [(0, 0), (1, 1)], [(0, 0), (1, 1)]),
        instance("one_side_empty", 2, [(0, 1), (1, 0)], [(0, 0), (1, 1)], []),
        instance("loop_coinciding_single", 1, [(0, 0)], [(0, 0)], [(0, 0)]),
        instance("opposite_pairs_coinciding", 2, [(0, 1), (1, 0)], [(0, 0), (1, 1)], [(0, 0), (1, 1)]),
        instance("all_loops_all_pairs", 2, [(0, 0), (0, 1), (1, 0), (1, 1)],
                 [(0, 0), (0, 1), (1, 0), (1, 1)], [(0, 0), (0, 1), (1, 0), (1, 1)]),
        instance("isolates_must_survive", 5, [(2, 0), (3, 1)],
                 [(2, 1), (4, 4)], [(0, 3), (4, 4)]),
    ]
    out += [sharp(n, n) for n in (1, 2, 3, 4, 8, 16)]
    out += [sharp(1, 5), sharp(5, 1), transposed(sharp(1, 5))]
    out += [grid(n) for n in (2, 3, 4)]
    return out


def generate(directory: Path) -> list:
    directory.mkdir(parents=True, exist_ok=True)
    records = []
    for data in cases():
        name = data["name"]
        cert = construct(data)
        for suffix, payload in (("instance", data), ("certificate", cert)):
            (directory / f"{name}.{suffix}.json").write_text(
                json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        records.append({"name": name, **cert["stats"], **{k: cert["pruning"][k]
                        for k in ("deletions", "q", "value")}})
    (directory / "INDEX.json").write_text(json.dumps(records, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return records


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    print(json.dumps({"generated_examples": len(generate(args.directory))}, sort_keys=True))


if __name__ == "__main__":
    main()
