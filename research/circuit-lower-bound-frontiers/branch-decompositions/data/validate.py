"""Validates: finite branch-compiler equivalence, joint-cut loss, and DNNF charging.

Run with Python 3, no dependencies. Seed 20261004; exhaustive cases and finite
sampling only. This is not a proof of the asymptotic graph hypothesis.
"""

import itertools
import json
import math
import random


SEED = 20261004
RNG = random.Random(SEED)


def trees(vertices):
    if len(vertices) == 1:
        return [vertices[0]]
    first, *rest = vertices
    result = []
    for mask in range(1 << len(rest)):
        left = (first,) + tuple(v for i, v in enumerate(rest) if mask >> i & 1)
        right = tuple(v for v in vertices if v not in left)
        if not right:
            continue
        result.extend((a, b) for a in trees(left) for b in trees(right))
    return result


def leaves(tree):
    return {tree} if isinstance(tree, int) else leaves(tree[0]) | leaves(tree[1])


def cut(edges, region):
    return tuple(i for i, (u, v) in enumerate(edges) if (u in region) != (v in region))


def widths(edges, tree):
    if isinstance(tree, int):
        return len(cut(edges, {tree})), 0
    a, b = tree
    ba, wa = widths(edges, a)
    bb, wb = widths(edges, b)
    da, db = set(cut(edges, leaves(a))), set(cut(edges, leaves(b)))
    parent = set(cut(edges, leaves(tree)))
    assert 2 * len(da | db) == len(da) + len(db) + len(parent)
    return max(ba, bb, len(parent)), max(wa, wb, len(da | db))


def compile_network(edges, checks, owners, tree, n):
    """Truth-set semantics of boundary-state symbolic AND/OR gates.

    Truth sets are represented cylindrically on all n variables, while scopes
    track the unique owners. No numeric tensor contraction substitutes for OR.
    """
    incidence = {v: tuple(i for i, e in enumerate(edges) if v in e) for v in checks}
    full = (1 << (1 << n)) - 1
    metrics = {"and_terms": 0, "or_nodes": 0, "overlapping_merges": 0}

    def build(t):
        boundary = cut(edges, leaves(t))
        if isinstance(t, int):
            table = {}
            scope = frozenset([owners[t][0]]) if t in owners else frozenset()
            for values in itertools.product((0, 1), repeat=len(boundary)):
                bits = dict(zip(boundary, values))
                allowed = checks[t](bits)
                truth = full if allowed else 0
                if t in owners:
                    variable, edge = owners[t]
                    truth &= sum(1 << x for x in range(1 << n)
                                 if ((x >> variable) & 1) == bits[edge])
                table[values] = truth
            return boundary, table, scope
        da, a, sa = build(t[0])
        db, b, sb = build(t[1])
        assert not sa & sb
        joint = tuple(sorted(set(da) | set(db)))
        groups = {}
        for values in itertools.product((0, 1), repeat=len(joint)):
            bits = dict(zip(joint, values))
            pa = a[tuple(bits[e] for e in da)]
            pb = b[tuple(bits[e] for e in db)]
            key = tuple(bits[e] for e in boundary)
            groups.setdefault(key, []).append(pa & pb)
            metrics["and_terms"] += 1
        table = {}
        for key, terms in groups.items():
            total = 0
            for term in terms:
                if total & term:
                    metrics["overlapping_merges"] += 1
                total |= term
            table[key] = total
            metrics["or_nodes"] += len(terms) - 1
        return boundary, table, sa | sb

    boundary, table, scope = build(tree)
    assert not boundary
    assert scope == frozenset(range(n))
    brute = 0
    for values in itertools.product((0, 1), repeat=len(edges)):
        bits = dict(enumerate(values))
        if not all(checks[v](bits) for v in checks):
            continue
        for x in range(1 << n):
            if all(((x >> variable) & 1) == bits[edge]
                   for variable, edge in owners.values()):
                brute |= 1 << x
    assert brute == table[()]
    b, w = widths(edges, tree)
    assert 2 * w <= 3 * b
    assert metrics["and_terms"] + metrics["or_nodes"] <= 2 * (len(checks) - 1) * 2**w
    return metrics


def circuit_network(n, gates):
    """Acyclic full-binary-basis gates; parallel edges retain their identities."""
    edges = []
    incoming = {}
    outgoing = {v: [] for v in range(n + len(gates))}
    for j, (a, b, truth) in enumerate(gates, n):
        incoming[j] = []
        for source in (a, b):
            incoming[j].append(len(edges))
            outgoing[source].append(len(edges))
            edges.append((source, j))
    checks, owners = {}, {}
    for v in range(n):
        assert outgoing[v]
        ids = tuple(outgoing[v])
        checks[v] = lambda bits, ids=ids: len({bits[e] for e in ids}) <= 1
        owners[v] = (v, ids[0])
    for v, (_, _, truth) in enumerate(gates, n):
        ins, outs = tuple(incoming[v]), tuple(outgoing[v])
        is_output = v == n + len(gates) - 1

        def check(bits, ins=ins, outs=outs, truth=truth, is_output=is_output):
            result = (truth >> (2 * bits[ins[0]] + bits[ins[1]])) & 1
            return all(bits[e] == result for e in outs) and (not is_output or result == 1)

        checks[v] = check
    return edges, checks, owners


def rectangle_threshold(truth, n):
    """Exact least K: every one-rectangle has at least one side smaller than K."""
    largest = 0
    for scope in range(1 << n):
        a = [v for v in range(n) if scope >> v & 1]
        b = [v for v in range(n) if not scope >> v & 1]
        if len(a) > len(b):
            continue
        rows = []
        for av in range(1 << len(a)):
            row = 0
            for bv in range(1 << len(b)):
                assignment = sum(((av >> i) & 1) << v for i, v in enumerate(a))
                assignment |= sum(((bv >> i) & 1) << v for i, v in enumerate(b))
                if truth >> assignment & 1:
                    row |= 1 << bv
            rows.append(row)
        for subset in range(1, 1 << len(rows)):
            common = (1 << (1 << len(b))) - 1
            for i, row in enumerate(rows):
                if subset >> i & 1:
                    common &= row
            largest = max(largest, min(subset.bit_count(), common.bit_count()))
    return largest + 1


def test_dnffrontier(truth, n):
    """Build smooth shared DAGs, then verify gate contexts and every charge."""
    nodes, cache = [], {}
    full = (1 << (1 << n)) - 1

    def intern(kind, args, scope, value):
        key = (kind, args)
        if key not in cache:
            cache[key] = len(nodes)
            nodes.append((kind, args, scope, value))
        return cache[key]

    def literal(v, bit):
        value = sum(1 << x for x in range(1 << n) if (x >> v & 1) == bit)
        return intern("literal", (v, bit), 1 << v, value)

    def operation(kind, a, b):
        sa, va = nodes[a][2:]
        sb, vb = nodes[b][2:]
        assert sa == sb if kind == "or" else not sa & sb
        return intern(kind, (a, b), sa | sb, va | vb if kind == "or" else va & vb)

    terms = []
    for x in range(1 << n):
        if truth >> x & 1:
            order = list(range(n))
            RNG.shuffle(order)
            term = literal(order[0], x >> order[0] & 1)
            for v in order[1:]:
                term = operation("and", term, literal(v, x >> v & 1))
            terms.append(term)
    if not terms:
        return 0, 0
    while len(terms) > 1:
        a, b = terms.pop(), terms.pop()
        terms.append(operation("or", a, b))
    root = terms[0]
    # An overlapping OR with shared descendants explicitly tests nondeterminism.
    root = operation("or", root, terms[0])
    contexts = [0] * len(nodes)
    contexts[root] = full
    for g in reversed(range(len(nodes))):
        kind, args, _, _ = nodes[g]
        if kind == "or":
            for child in args:
                contexts[child] |= contexts[g]
        elif kind == "and":
            a, b = args
            contexts[a] |= contexts[g] & nodes[b][3]
            contexts[b] |= contexts[g] & nodes[a][3]
    k = max(2, rectangle_threshold(truth, n))
    counts = []
    for g, (_, _, scope, value) in enumerate(nodes):
        count = value.bit_count() // (1 << (n - scope.bit_count()))
        counts.append(count)
        context_count = contexts[g].bit_count() // (1 << scope.bit_count())
        product = value & contexts[g]
        assert not product & ~truth
        assert product.bit_count() == count * context_count
        if count >= k:
            assert context_count < k
    charges = {}
    if truth.bit_count() >= k:
        for x in range(1 << n):
            if not truth >> x & 1:
                continue
            g = root
            while True:
                kind, args, _, _ = nodes[g]
                assert counts[g] >= k
                a, b = args
                if kind == "or":
                    child = a if nodes[a][3] >> x & 1 else b
                    if counts[child] < k:
                        key = ("edge", g, child)
                        break
                    g = child
                else:
                    assert kind == "and"
                    if counts[a] >= k or counts[b] >= k:
                        g = a if counts[a] >= k else b
                    else:
                        key = ("and", g)
                        break
            charges.setdefault(key, []).append(x)
        for key, assignments in charges.items():
            assert len(assignments) <= (k - 1) ** (2 if key[0] == "edge" else 3)
        assert truth.bit_count() <= 2 * len(nodes) * (k - 1) ** 3
    return len(nodes), len(charges)


def main():
    graph_trees = 0
    possible = list(itertools.combinations(range(4), 2))
    four_trees = trees(tuple(range(4)))
    for mask in range(1 << len(possible)):
        edges = [e for i, e in enumerate(possible) if mask >> i & 1]
        for tree in four_trees:
            b, w = widths(edges, tree)
            assert 2 * w <= 3 * b
            graph_trees += 1
    triangle = widths([(0, 1), (1, 2), (2, 0)], ((0, 1), 2))
    assert triangle == (2, 3)
    random_compilers, overlaps = 0, 0
    for _ in range(64):
        edges = [(v, (v + 1) % 6) for v in range(6)]
        extras = [(0, 3), (1, 4), (2, 5)]
        edges += [e for e in extras if RNG.randrange(2)]
        checks, owners = {}, {}
        for v in range(6):
            ids = tuple(i for i, e in enumerate(edges) if v in e)
            table = RNG.randrange(1 << (1 << len(ids)))
            checks[v] = lambda bits, ids=ids, table=table: bool(
                table >> sum(bits[e] << j for j, e in enumerate(ids)) & 1)
            if v < 3:
                owners[v] = (v, ids[0])
        tree = RNG.choice(trees(tuple(range(6))))
        metrics = compile_network(edges, checks, owners, tree, 3)
        overlaps += metrics["overlapping_merges"]
        random_compilers += 1
    deterministic_compilers = 0
    for truth in range(16):
        for repeated in (False, True):
            n = 1 if repeated else 2
            gates = [(0, 0 if repeated else 1, truth), (n, n, 8)]
            edges, checks, owners = circuit_network(n, gates)
            for tree in trees(tuple(checks)):
                metrics = compile_network(edges, checks, owners, tree, n)
                assert metrics["overlapping_merges"] == 0
                deterministic_compilers += 1
    dnfs, charges = 0, 0
    for truth in [0, 65535, 0x6996, 0xE4E4] + [RNG.randrange(65536) for _ in range(252)]:
        _, charged = test_dnffrontier(truth, 4)
        dnfs += 1
        charges += charged
    # Cancellation and repeated variable ownership defeat support/decomposition.
    assert [x - x for x in (0, 1)] == [0, 0]
    assert [bool(x) or bool(x) for x in (0, 1)] == [False, True]
    assert sum(x and not x for x in (0, 1)) == 0
    assert sum(x and not y for x, y in itertools.product((0, 1), repeat=2)) == 1
    p = 3 / (2 * math.pi) * math.acos((1 + 2 * math.sqrt(2)) / 4)
    print(json.dumps({
        "seed": SEED,
        "exhaustive_four_vertex_graph_tree_pairs": graph_trees,
        "triangle": {"b": triangle[0], "W": triangle[1], "W_over_b": 1.5},
        "random_constraint_networks": random_compilers,
        "nondeterministic_merge_overlaps_observed": overlaps,
        "full_binary_basis_circuit_tree_tests": deterministic_compilers,
        "smooth_shared_DNNF_context_and_frontier_tests": dnfs,
        "charged_frontiers_checked": charges,
        "baseline_A": 2 * p,
        "baseline_L": 1 + 1 / (2 * p),
        "carving_beta_must_be_less_than": 4 * p / 3,
        "cubic_carving_c_must_be_less_than": 2 * p / 3,
        "all_assertions_passed": True,
        "limitations": "Finite tests only; no universal graph bound or novelty claim."
    }, indent=2))


if __name__ == "__main__":
    main()
