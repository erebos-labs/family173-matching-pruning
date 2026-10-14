#!/usr/bin/env python3
"""Independent exact certificate checker. Python 3.10+, no dependencies.

Does not import construct.py or any graph/matching library. Rebuilds objects
from the raw relation and coordinate families, then checks finite witnesses.
Equal matching/cover sizes certify optimality without trusting an algorithm.
The optional brute-force objective calculation uses only the original data.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
from pathlib import Path


class InvalidCertificate(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidCertificate(message)


def unique_pairs(value, name: str, n: int) -> set:
    require(isinstance(value, list), f"{name}: not a list")
    result = set()
    for e in value:
        require(isinstance(e, list) and len(e) == 2, f"{name}: not a pair")
        require(all(type(x) is int and 0 <= x < n for x in e), f"{name}: out of domain")
        e = tuple(e)
        require(e not in result, f"{name}: duplicate")
        result.add(e)
    return result


def decode(data: dict) -> tuple:
    require(isinstance(data, dict) and data.get("schema") == "family173.instance.v1", "input schema")
    n = data.get("n")
    require(type(n) is int and n >= 0, "input n")
    return (n, unique_pairs(data.get("relation"), "relation", n),
            unique_pairs(data.get("R"), "R", n), unique_pairs(data.get("C"), "C", n))


def rebuild(data: dict) -> dict:
    n, E, R, C = decode(data)
    # Vertex names are made independently, and never identify the R and C copies.
    rid = {r: "R:%d:%d" % r for r in R}
    cid = {c: "C:%d:%d" % c for c in C}
    witnesses = {(p, j, i, s) for (p, j), (i, s) in itertools.product(R, C)
                 if (p, i) in E and (s, j) in E}
    Z = {(i, j) for p, j, i, s in witnesses}
    H = {(p, s) for p, j, i, s in witnesses}
    zl = {z: "ZL:%d:%d" % z for z in Z}
    zr = {z: "ZR:%d:%d" % z for z in Z}
    hid = {h: "H:%d:%d" % h for h in H}
    conflict = {(rid[p, j], cid[i, s]) for p, j, i, s in witnesses}
    gamma = set(conflict)
    for z in Z:
        for r in R:
            if r[1] == z[1] and (r[0], z[0]) in E:
                gamma.add((rid[r], zr[z]))
        for c in C:
            if c[0] == z[0] and (c[1], z[1]) in E:
                gamma.add((zl[z], cid[c]))
    bedges, aedges = set(), set()
    for h in H:
        for r in R:
            if h[0] == r[0] and (h[1], r[1]) in E:
                bedges.add((rid[r], hid[h]))
        for c in C:
            if h[1] == c[1] and (h[0], c[0]) in E:
                aedges.add((hid[h], cid[c]))
    graphs = {
        "Gamma": (set(rid.values()) | set(zl.values()), set(cid.values()) | set(zr.values()), gamma),
        "B0": (set(rid.values()), set(hid.values()), bedges),
        "A0": (set(hid.values()), set(cid.values()), aedges),
    }
    return {"n": n, "E": E, "R": R, "C": C, "Z": Z, "H": H,
            "rid": rid, "cid": cid, "zl": zl, "zr": zr,
            "conflicts": conflict, "graphs": graphs}


def unique_strings(value, name: str) -> set:
    require(isinstance(value, list) and all(type(x) is str for x in value), f"{name}: string list")
    require(len(set(value)) == len(value), f"{name}: duplicate")
    return set(value)


def edge_set(value, name: str) -> set:
    require(isinstance(value, list), f"{name}: list")
    result = set()
    for item in value:
        require(isinstance(item, list) and len(item) == 2
                and all(type(x) is str for x in item), f"{name}: edge format")
        pair = tuple(item)
        require(pair not in result, f"{name}: duplicate edge")
        result.add(pair)
    return result


def check_graph(name: str, graph: tuple, supplied: dict) -> int:
    require(isinstance(supplied, dict), f"{name}: object")
    L, R, E = graph
    require(unique_strings(supplied.get("left"), name + " left") == L, name + " left mismatch")
    require(unique_strings(supplied.get("right"), name + " right") == R, name + " right mismatch")
    require(edge_set(supplied.get("edges"), name + " edges") == E, name + " edge mismatch")
    matching = edge_set(supplied.get("matching"), name + " matching")
    require(matching <= E, name + " matching uses a nonedge")
    require(len({u for u, v in matching}) == len(matching), name + " repeated left endpoint")
    require(len({v for u, v in matching}) == len(matching), name + " repeated right endpoint")
    CL = unique_strings(supplied.get("cover_left"), name + " cover_left")
    CR = unique_strings(supplied.get("cover_right"), name + " cover_right")
    require(CL <= L and CR <= R, name + " cover outside its side")
    require(all(u in CL or v in CR for u, v in E), name + " uncovered edge")
    require(len(CL) + len(CR) == len(matching), name + " unequal matching/cover sizes")
    require(type(supplied.get("size")) is int and supplied["size"] == len(matching), name + " size")
    # Every matching is no larger than every cover; these witnesses attain equality.
    return len(matching)


def brute_force_original(data: dict, limit: int = 18) -> dict:
    """Enumerate EVERY retention mask, using neither Gamma nor its certificate."""
    n, E, rr, cc = decode(data)
    R, C = sorted(rr), sorted(cc)
    require(len(R) + len(C) <= limit, "brute-force limit exceeded (not a mathematical failure)")
    # Deliberately rebuild Z through its quantified definition on X x X.
    Z = [(i, j) for i in range(n) for j in range(n)
         if any(r[1] == j and c[0] == i and (r[0], i) in E and (c[1], j) in E
                for r in R for c in C)]
    preserve_R = {a for a, (p, j) in enumerate(R)
                  if not any((p, i) in E and (s, j) in E for i, s in C)}
    preserve_C = {b for b, (i, s) in enumerate(C)
                  if not any((p, i) in E and (s, j) in E for p, j in R)}
    best, witness, feasible = None, None, 0
    for mask in range(1 << (len(R) + len(C))):
        if any(not (mask >> a) & 1 for a in preserve_R):
            continue
        if any(not (mask >> (len(R) + b)) & 1 for b in preserve_C):
            continue
        rp = [r for a, r in enumerate(R) if (mask >> a) & 1]
        cp = [c for b, c in enumerate(C) if (mask >> (len(R) + b)) & 1]
        if any((p, i) in E and (s, j) in E for p, j in rp for i, s in cp):
            continue
        feasible += 1
        q = sum(not any(j == jj and (p, i) in E for p, jj in rp)
                and not any(i == ii and (s, j) in E for ii, s in cp) for i, j in Z)
        d = len(R) + len(C) - len(rp) - len(cp)
        value = d - q
        if best is None or value < best:
            best, witness = value, {"R_retained": rp, "C_retained": cp, "deletions": d, "q": q}
    require(best is not None, "no feasible pruning")
    return {"minimum": best, "witness": witness, "feasible": feasible,
            "masks_considered": 1 << (len(R) + len(C))}


def verify(data: dict, cert: dict, brute: bool = False, limit: int = 18) -> dict:
    o = rebuild(data)
    require(isinstance(cert, dict) and cert.get("schema") == "family173.certificate.v1", "certificate schema")
    digest = hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":"),
                                      ensure_ascii=True).encode("ascii")).hexdigest()
    require(cert.get("instance_sha256") == digest, "input digest mismatch")
    derived = cert.get("derived", {})
    require(unique_pairs(derived.get("Z"), "derived Z", o["n"]) == o["Z"], "Z mismatch")
    require(unique_pairs(derived.get("H"), "derived H", o["n"]) == o["H"], "H mismatch")
    require(edge_set(derived.get("conflicts"), "conflicts") == o["conflicts"], "conflicts mismatch")
    require(isinstance(cert.get("graphs"), dict) and set(cert["graphs"]) == set(o["graphs"]), "graph keys")
    sizes = {name: check_graph(name, graph, cert["graphs"][name]) for name, graph in o["graphs"].items()}
    beta = min(sizes["B0"], sizes["A0"])
    expected_stats = {"Z": len(o["Z"]), "H": len(o["H"]), "nu_B0": sizes["B0"],
                      "nu_A0": sizes["A0"], "beta": beta, "nu_Gamma": sizes["Gamma"]}
    stats = cert.get("stats")
    require(isinstance(stats, dict) and all(type(v) is int for v in stats.values())
            and stats == expected_stats, "statistics mismatch")
    require(sizes["Gamma"] <= len(o["Z"]) + beta, "refined matching inequality fails")
    require(beta <= len(o["H"]), "capacity exceeds H")
    p = cert.get("pruning", {})
    rp = unique_pairs(p.get("R_retained"), "retained R", o["n"])
    cp = unique_pairs(p.get("C_retained"), "retained C", o["n"])
    require(rp <= o["R"] and cp <= o["C"], "retention outside original families")
    require(not any((r[0], c[0]) in o["E"] and (c[1], r[1]) in o["E"] for r in rp for c in cp),
            "retained conflict")
    for r in o["R"]:
        if not any((r[0], c[0]) in o["E"] and (c[1], r[1]) in o["E"] for c in o["C"]):
            require(r in rp, "initially conflict-free R member deleted")
    for c in o["C"]:
        if not any((r[0], c[0]) in o["E"] and (c[1], r[1]) in o["E"] for r in o["R"]):
            require(c in cp, "initially conflict-free C member deleted")
    uncovered, natural_left, natural_right = set(), set(), set()
    for z in o["Z"]:
        lc = any(r[1] == z[1] and (r[0], z[0]) in o["E"] for r in rp)
        rc = any(c[0] == z[0] and (c[1], z[1]) in o["E"] for c in cp)
        require(not (lc and rc), "a point is covered by both retained sides")
        if lc:
            natural_right.add(o["zr"][z])
        elif rc:
            natural_left.add(o["zl"][z])
        else:
            uncovered.add(z)
    require(unique_pairs(p.get("uncovered"), "uncovered", o["n"]) == uncovered, "uncovered set mismatch")
    d = len(o["R"] - rp) + len(o["C"] - cp)
    q = len(uncovered)
    for name, value in (("deletions", d), ("q", q), ("value", d - q)):
        require(type(p.get(name)) is int and p[name] == value, "pruning " + name + " mismatch")
    require(d <= beta + q, "refined deletion inequality fails")
    require(d <= len(o["H"]) + q, "source deletion inequality fails")
    natural_left.update(o["rid"][r] for r in o["R"] - rp)
    natural_right.update(o["cid"][c] for c in o["C"] - cp)
    require(all(u in natural_left or v in natural_right for u, v in o["graphs"]["Gamma"][2]),
            "canonical pruning cover fails")
    require(len(natural_left) + len(natural_right) == d + len(o["Z"]) - q,
            "canonical cover count")
    require(d - q == sizes["Gamma"] - len(o["Z"]), "certificate pruning is not objective-optimal")
    result = {"status": "PASS", **expected_stats, "deletions": d, "q": q, "minimum": d - q}
    if brute:
        enumeration = brute_force_original(data, limit)
        require(enumeration["minimum"] == d - q, "direct enumeration disagrees with certificate")
        result["brute_force"] = {k: enumeration[k] for k in ("minimum", "feasible", "masks_considered")}
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("instance", type=Path)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--bruteforce", action="store_true")
    parser.add_argument("--limit", type=int, default=18)
    args = parser.parse_args()
    try:
        data = json.loads(args.instance.read_text(encoding="utf-8"))
        cert = json.loads(args.certificate.read_text(encoding="utf-8"))
        result = verify(data, cert, args.bruteforce, args.limit)
    except (OSError, ValueError, TypeError, KeyError, AttributeError) as exc:
        parser.exit(1, f"FAIL: {exc}\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
