"""Validates: finite multiplexer adaptivity and K4 Tseitin representation obstructions.

Deterministic exhaustive checks; no random seeds or third-party packages.
Does not establish any asymptotic circuit or resolution lower bound.
Run: python3 research/circuit-lower-bound-frontiers/barriers-perspective/data/check_obstructions.py
"""

from itertools import combinations, product
import json


def mux(bits, address_bits):
    address = sum(bits[i] << i for i in range(address_bits))
    return bits[address_bits + address]


def mux_checks():
    rows = []
    for k in range(1, 4):
        n = k + (1 << k)
        table = {x: mux(x, k) for x in product((0, 1), repeat=n)}
        essential = []
        for i in range(n):
            essential.append(any(table[x] != table[x[:i] + (1 - x[i],) + x[i + 1:]]
                                 for x in table))
        assert all(essential)
        # Read k address bits, then the selected data bit; an exact evaluator.
        for x in table:
            address = sum(x[i] << i for i in range(k))
            assert table[x] == x[k + address]
        rows.append({"address_bits": k, "input_bits": n,
                     "all_inputs_essential": True,
                     "adaptive_depth_upper_bound": k + 1,
                     "oblivious_1_local_depth_exact": n,
                     "assignments_checked": len(table)})
    return rows


def tseitin_clauses(vertices, edges, charges):
    clauses = set()
    for vertex in vertices:
        incident = [i for i, edge in enumerate(edges) if vertex in edge]
        for assignment in product((0, 1), repeat=len(incident)):
            if sum(assignment) % 2 != charges[vertex]:
                # Clause false at exactly this forbidden local assignment.
                clauses.add(frozenset((i + 1) if b == 0 else -(i + 1)
                                      for i, b in zip(incident, assignment)))
    return clauses


def refutable_at_width(initial, width):
    clauses = sorted(initial, key=lambda clause: (len(clause), tuple(sorted(clause))))
    known = set(clauses)
    cursor = 0
    while cursor < len(clauses):
        left = clauses[cursor]
        for right in clauses[:cursor]:
            for pivot in sorted(left):
                if -pivot not in right:
                    continue
                resolvent = (left - {pivot}) | (right - {-pivot})
                if len(resolvent) > width or any(-v in resolvent for v in resolvent):
                    continue
                if not resolvent:
                    return True, len(known) + 1
                if resolvent not in known:
                    known.add(resolvent)
                    clauses.append(resolvent)
        cursor += 1
    return False, len(known)


def k4_checks():
    vertices = tuple(range(4))
    edges = tuple(combinations(vertices, 2))
    charges = (1, 0, 0, 0)
    clauses = tseitin_clauses(vertices, edges, charges)
    xor_count = and_count = 0
    for x in product((0, 1), repeat=len(edges)):
        xor_ok = all(sum(x[i] for i, e in enumerate(edges) if v in e) % 2 == charges[v]
                     for v in vertices)
        and_ok = all(int(all(x[i] for i, e in enumerate(edges) if v in e)) == charges[v]
                     for v in vertices)
        cnf_ok = all(any(x[abs(lit) - 1] == (lit > 0) for lit in clause)
                     for clause in clauses)
        assert xor_ok == cnf_ok
        xor_count += xor_ok
        and_count += and_ok
    width3, count3 = refutable_at_width(clauses, 3)
    width4, count4 = refutable_at_width(clauses, 4)
    assert (xor_count, and_count) == (0, 4)
    assert (width3, width4) == (False, True)
    assert len(clauses) == 16
    return {"vertices": len(vertices), "edge_variables": len(edges),
            "charges": charges, "clauses": len(clauses), "initial_width": 3,
            "assignments_checked": 1 << len(edges),
            "xor_satisfying_assignments": xor_count,
            "and_satisfying_assignments_same_graph": and_count,
            "minimum_resolution_width": 4,
            "width3_saturation_clauses": count3,
            "width4_clauses_before_refutation": count4,
            "direct_binary_cnf_gates": 3 * len(clauses) - 1,
            "semantic_constant_zero_gates": 1}


if __name__ == "__main__":
    print("Validates: finite multiplexer adaptivity and K4 Tseitin representation obstructions.")
    print(json.dumps({"multiplexer": mux_checks(), "k4_tseitin": k4_checks()}, indent=2))
