#!/usr/bin/env python3
"""Finite correctness checks for the paper's counting and derandomization procedures.

These executable reference procedures use arbitrary layouts, not the asymptotically good
Gaussian layout algorithm. Exhaustive circuit evaluation is the independent counting oracle.
The checks neither establish the asymptotic bounds nor replace the Lean proofs.
"""

from collections import Counter, defaultdict
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from random import Random


@dataclass(frozen=True)
class Gate:
    op: int | str  # integer truth table, or an aggregate operation
    args: tuple[int, ...]

    def evaluate(self, values):
        return self.apply([values[a] for a in self.args])

    def apply(self, xs):
        if isinstance(self.op, int):
            return (self.op >> sum(x << i for i, x in enumerate(xs))) & 1
        if self.op == "and":
            return int(all(xs))
        if self.op == "or":
            return int(any(xs))
        if self.op == "xor":
            return sum(xs) % 2
        if self.op == "mod3":
            return int(sum(xs) % 3 == 1)
        raise ValueError(self.op)


def exhaustive(n, gates, out):
    count = 0
    for x in product(range(2), repeat=n):
        values = list(x)
        for gate in gates:
            values.append(gate.evaluate(values))
        count += values[out]
    return count


class Network:
    """The paper's junction-chain compiler, with explicit slots and signal labels."""

    def __init__(self, n, gates, outputs):
        self.n, self.gates = n, gates
        reachable = set()

        def reach(w):
            if w in reachable:
                return
            reachable.add(w)
            if w >= n:
                for a in gates[w - n].args:
                    assert a < w
                    reach(a)

        for w, _ in outputs:
            reach(w)
        self.vertices = [("wire", w) for w in sorted(reachable)]
        self.vertices += [("out", i) for i in range(len(outputs))]
        consumers = defaultdict(list)
        for w in sorted(reachable):
            if w >= n:
                for slot, a in enumerate(gates[w - n].args):
                    consumers[a].append((("wire", w), slot))
        for i, (w, _) in enumerate(outputs):
            consumers[w].append((("out", i), 0))
        self.edges, self.ports, self.head = [], {}, {}
        self.incident = defaultdict(list)

        def edge(u, v, w):
            e = len(self.edges)
            self.edges.append((u, v, w))
            self.incident[u].append(e)
            self.incident[v].append(e)
            return e

        for w in sorted(reachable):
            previous = ("wire", w)
            for j, (owner, slot) in enumerate(consumers[w]):
                vertex = ("junction", w, j)
                self.vertices.append(vertex)
                feed = edge(previous, vertex, w)
                if j == 0:
                    self.head[w] = feed
                self.ports[owner, slot] = edge(vertex, owner, w)
                previous = vertex
        self.outputs = outputs
        self.unread = n - sum(w < n for w in reachable)

    def check(self, vertex, value, input_bit):
        kind, w = vertex[:2]
        if kind == "junction":
            return len({value(e) for e in self.incident[vertex]}) == 1
        if kind == "out":
            return not self.outputs[w][1] or value(self.ports[vertex, 0]) == 1
        if w < self.n:
            wanted = input_bit
        else:
            gate = self.gates[w - self.n]
            wanted = gate.apply([value(self.ports[vertex, i]) for i in range(len(gate.args))])
        return value(self.head[w]) == wanted


def multiply(a, b, ops):
    return tuple((x * y if op == "and" else max(x, y) if op == "or"
                  else (x + y) % (3 if op == "mod3" else 2))
                 for x, y, op in zip(a, b, ops))


def frontier_count(net, order, compressed=True, ops=(), initial=(), contribution=None):
    """Return the exact table indexed by accumulated ledger value."""
    assert set(order) == set(net.vertices) and len(order) == len(net.vertices)
    name = (lambda e: net.edges[e][2]) if compressed else (lambda e: e)
    before, old_names = set(), []
    states = {((), initial): 1}
    maximum = 0
    for vertex in order:
        before.add(vertex)
        cut = [e for e, (u, v, _) in enumerate(net.edges) if (u in before) != (v in before)]
        new_names = sorted({name(e) for e in cut})
        fresh = sorted(set(new_names) - set(old_names))
        maximum = max(maximum, len(set(old_names) | set(new_names)))
        next_states = Counter()
        for (bits, ledger), count in states.items():
            known = dict(zip(old_names, bits))
            for new_bits in product(range(2), repeat=len(fresh)):
                assignment = known | dict(zip(fresh, new_bits))
                value = lambda e: assignment[name(e)]
                input_site = vertex[0] == "wire" and vertex[1] < net.n
                for bit in range(2) if input_site else (0,):
                    if not net.check(vertex, value, bit):
                        continue
                    updated = ledger
                    if contribution is not None and vertex[0] == "wire":
                        w = vertex[1]
                        updated = multiply(ledger, contribution(w, value(net.head[w])), ops)
                    key = (tuple(assignment[a] for a in new_names), updated)
                    next_states[key] += count
        states, old_names = next_states, new_names
    assert not old_names
    return {ledger: count * 2**net.unread for (_, ledger), count in states.items()}, maximum


def aggregate_count(n, gates, out, rng):
    special = [(i, gate) for i, gate in enumerate(gates) if isinstance(gate.op, str)]
    ops = tuple(gate.op for _, gate in special)
    identity = tuple(1 if op == "and" else 0 for op in ops)
    live = set(range(n)) | {n + i for i, g in enumerate(gates)
                            if isinstance(g.op, int) and g.args}

    def contribution(w, value):
        return tuple((value if w in gate.args else 1) if gate.op == "and"
                     else (value if w in gate.args else 0) if gate.op == "or"
                     else (gate.args.count(w) * value) % (3 if gate.op == "mod3" else 2)
                     for _, gate in special)

    answer = 0
    for guess in product(*(range(3 if op == "mod3" else 2) for op in ops)):
        erased = list(gates)
        for (i, gate), state in zip(special, guess):
            erased[i] = Gate(int(state == 1) if gate.op == "mod3" else state, ())
        initial = identity
        for i, gate in enumerate(erased):
            if n + i not in live:
                initial = multiply(initial, contribution(n + i, gate.evaluate({})), ops)
        net = Network(n, erased, [(out, True)] + [(w, False) for w in sorted(live)])
        order = list(net.vertices)
        rng.shuffle(order)
        table, _ = frontier_count(net, order, ops=ops, initial=initial,
                                 contribution=lambda w, v: contribution(w, v)
                                 if w in live else identity)
        answer += table.get(guess, 0)
    return answer


def check_counting():
    rng = Random(20261005)
    checked = 0
    # All binary gates, plus randomized DAGs with repeated and unused inputs and constants.
    cases = [(2, [Gate(table, (0, 1))], 2) for table in range(16)]
    cases += [(4, [Gate(1, ())], 4), (4, [Gate(0, ())], 4), (3, [], 1),
              (0, [Gate(1, ())], 0), (0, [Gate(0, ())], 0)]
    for _ in range(60):
        n, gates = rng.randrange(1, 5), []
        for i in range(rng.randrange(1, 6)):
            arity = rng.randrange(3)
            gates.append(Gate(rng.randrange(1 << (1 << arity)),
                              tuple(rng.randrange(n + i) for _ in range(arity))))
        cases.append((n, gates, rng.randrange(n + len(gates))))
    savings = 0
    for n, gates, out in cases:
        expected = exhaustive(n, gates, out)
        net = Network(n, gates, [(out, True)])
        for _ in range(3):
            order = list(net.vertices)
            rng.shuffle(order)
            raw, raw_width = frontier_count(net, order, compressed=False)
            labels, label_width = frontier_count(net, order)
            assert raw.get((), 0) == labels.get((), 0) == expected
            assert label_width <= raw_width
            savings += label_width < raw_width
            checked += 1
    assert savings > 0
    mixed = [
        (0, [Gate("and", ())], 0),
        (2, [Gate("and", (0, 1)), Gate("xor", (0, 2, 2, 1))], 3),
        (3, [Gate("or", ()), Gate("and", ()), Gate("mod3", (4, 4, 0, 0, 0))], 5),
        (2, [Gate(8, (0, 1)), Gate("or", (0, 2)), Gate("xor", (2, 3, 3))], 4),
    ]
    for _ in range(40):
        n, gates = rng.randrange(1, 4), []
        for i in range(rng.randrange(1, 5)):
            if rng.randrange(2):
                op, arity = rng.choice(("and", "or", "xor", "mod3")), rng.randrange(6)
            else:
                arity = rng.randrange(3)
                op = rng.randrange(1 << (1 << arity))
            gates.append(Gate(op, tuple(rng.randrange(n + i) for _ in range(arity))))
        mixed.append((n, gates, rng.randrange(n + len(gates))))
    for n, gates, out in mixed:
        assert aggregate_count(n, gates, out, rng) == exhaustive(n, gates, out)
    print(f"Counting: {checked} raw/signal layout comparisons, {savings} strict signal savings, "
          f"{len(mixed)} ledger circuits matched exhaustive evaluation.")


def check_conditional_expectations():
    h = 8
    # Two sums of overlapping two-coordinate tests; complements deliberately share supports.
    counts = [[((i, i + 1), parity) for i in range(h - 1)] for parity in (0, 1)]

    def test(term, assignment):
        support, parity = term
        return int(sum(assignment[i] for i in support) % 2 == parity)

    def moment(terms, prefix):
        free = sorted({i for support, _ in terms for i in support} - set(prefix))
        total = 0
        for values in product(range(2), repeat=len(free)):
            assignment = prefix | dict(zip(free, values))
            total += all(test(term, assignment) for term in terms)
        return Fraction(total, 2**len(free))

    means = [sum(moment([term], {}) for term in terms) for terms in counts]
    denominator = Fraction(h, 2)**2

    def potential(prefix):
        return sum((sum(moment([a, b], prefix) for a in terms for b in terms)
                    - 2 * mean * sum(moment([a], prefix) for a in terms) + mean**2)
                   / denominator for terms, mean in zip(counts, means))

    def exact(prefix):
        free = [i for i in range(h) if i not in prefix]
        total = 0
        for values in product(range(2), repeat=len(free)):
            assignment = prefix | dict(zip(free, values))
            total += sum((sum(test(t, assignment) for t in terms) - mean)**2 / denominator
                         for terms, mean in zip(counts, means))
        return total / 2**len(free)

    prefix = {}
    assert potential(prefix) == exact(prefix) < 1
    for i in range(h):
        choices = [prefix | {i: bit} for bit in (0, 1)]
        for choice in choices:
            assert potential(choice) == exact(choice)
        next_prefix = min(choices, key=potential)
        assert potential(next_prefix) <= potential(prefix)
        prefix = next_prefix
    assert all(abs(sum(test(t, prefix) for t in terms) - mean) < Fraction(h, 2)
               for terms, mean in zip(counts, means))
    print("Conditional expectations: exact local moments matched full enumeration at every "
          "choice; the potential decreased and all final deviations met the bound.")


def check_weighted_peeling():
    """Guess the last bit first, then compute parity with one complete path per input."""
    n = 8
    start = (0, -1, -1)
    edges = [(start, (1, guess, 0), None) for guess in (0, 1)]
    for i in range(n):
        for guess, parity in product(range(2), repeat=2):
            u = (i + 1, guess, parity)
            for bit in (0, 1):
                if i == n - 1:
                    if bit != guess:
                        continue
                    v = (n + 1, parity ^ bit, -1)
                else:
                    v = (i + 2, guess, parity ^ bit)
                edges.append((u, v, bit))
    outgoing = defaultdict(list)
    for u, v, label in edges:
        outgoing[u].append((v, label))
    universe = list(product(range(2), repeat=n))

    def accepted(banned, output):
        result = {}
        for x in universe:
            paths = []

            def walk(u, path):
                if u in banned:
                    return
                if u[0] == n + 1:
                    if u[1] == output:
                        paths.append(path)
                    return
                for v, label in outgoing[u]:
                    if label is None or label == x[u[0] - 1]:
                        walk(v, path + (v,))

            walk(start, (start,))
            assert len(paths) <= 1
            if paths:
                result[x] = paths[0]
        return result

    originals = [accepted(set(), output) for output in (0, 1)]
    for output, original in enumerate(originals):
        assert set(original) == {x for x in universe if sum(x) % 2 == output}
    atom_weights = {x: 1 + sum((i + 1) * bit for i, bit in enumerate(x)) % 11
                    for x in universe}
    total_weight = sum(atom_weights.values())
    mu = {x: Fraction(a, total_weight) for x, a in atom_weights.items()}
    f = {x: (-1)**(x[0] ^ (x[1] & x[3]) ^ x[6]) for x in universe}
    exceptional = {x for x in universe if x[:5] == (0, 1, 0, 1, 0)}
    zeta = sum(mu[x] for x in exceptional)
    rectangles = 0
    for left, right in ((2, 2), (4, 4), (8, 8), (2, 8), (8, 2), (257, 2)):
        budget = (left - 1) * (right - 1)
        all_pieces, leftover = [], set()
        for output, original in enumerate(originals):
            banned, pieces = set(), []
            current = original
            while True:
                classes = defaultdict(set)
                for x, path in current.items():
                    for v in path:
                        classes[v].add(x)
                sides = {}
                for v, members in classes.items():
                    t = max(0, v[0] - 1)
                    past, future = {x[:t] for x in members}, {x[t:] for x in members}
                    assert members == {a + b for a in past for b in future}
                    sides[v] = (past, future)
                large = next((v for v, (a, b) in sides.items()
                              if len(a) >= left and len(b) >= right), None)
                if large is None:
                    break
                removed = classes[large]
                assert all(removed.isdisjoint(piece) for piece in pieces)
                pieces.append(removed)
                banned.add(large)
                following = accepted(banned, output)
                assert set(following) == set(current) - removed
                current = following
            if len(current) >= left:
                charges = Counter()
                for x, path in current.items():
                    i = next(i for i, v in enumerate(path) if len(sides[v][0]) >= left)
                    assert i > 0
                    u, v = path[i - 1:i + 1]
                    assert len(sides[u][0]) < left and len(sides[v][1]) < right
                    label = None if u == start else x[u[0] - 1]
                    charges[u, v, label] += 1
                assert max(charges.values(), default=0) <= budget
            assert len(current) <= budget * len(edges)
            assert sum(map(len, pieces)) + len(current) == len(original)
            weights = {x: Fraction((sum((i + 1) * bit for i, bit in enumerate(x)) % 5) - 2, 2)
                       for x in universe}
            bias = max((abs(sum(weights[x] for x in piece)) / len(piece)
                        for piece in pieces), default=Fraction(0))
            assert abs(sum(weights[x] for x in original)) <= bias * len(original) + len(current)
            all_pieces.extend(pieces)
            leftover.update(current)
        assert sum(map(len, all_pieces)) + len(leftover) == len(universe)
        assert len(set().union(*all_pieces, leftover)) == len(universe)
        packed_bias = sum(abs(sum(mu[x] * f[x] for x in piece)) for piece in all_pieces)
        residual_mass = sum(mu[x] for x in leftover)
        correlation = abs(sum(mu[x] * f[x] * (-1)**sum(x) for x in universe))
        assert correlation <= packed_bias + residual_mass
        assert residual_mass <= budget * (2 * len(edges)) * max(mu.values())
        # The actual pieces suffice to test the shared-measure summation mechanism.
        beta = max([Fraction(0)] + [
            (abs(sum(mu[x] * f[x] for x in piece))
             - sum(mu[x] for x in piece & exceptional)) / sum(mu[x] for x in piece)
            for piece in all_pieces])
        assert packed_bias <= beta + zeta
        rectangles += len(all_pieces)
    assert rectangles > 0
    print(f"Weighted frontier: {rectangles} disjoint rectangles; asymmetric thresholds, "
          "exact deletion, charges, nonuniform weights, and shared error budgets passed.")


if __name__ == "__main__":
    check_counting()
    check_conditional_expectations()
    check_weighted_peeling()
