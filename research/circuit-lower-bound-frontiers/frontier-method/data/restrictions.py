#!/usr/bin/env python3
"""Exact experiments for input-restriction accounting, not an asymptotic proof.

Normalization uses only constants, unary/complement absorption, duplicate gates,
dead gates, and a two-input composition when its intermediate gate has fanout one.
An output complement is free here; it can be absorbed into the final gate unless
the output is a literal, a terminal case costing at most one ordinary gate.
"""

from collections import Counter
from dataclasses import dataclass
from itertools import product
from math import cosh, exp2, log
from random import Random


@dataclass(frozen=True)
class Literal:
    wire: int | None
    neg: int = 0

    def value(self, values):
        return (0 if self.wire is None else values[self.wire]) ^ self.neg


@dataclass
class Circuit:
    n: int
    gates: dict[int, tuple[int, int, int]]
    output: Literal

    def evaluate(self, x):
        values = dict(enumerate(x))
        for w, (op, a, b) in sorted(self.gates.items()):
            values[w] = (op >> (values[a] + 2 * values[b])) & 1
        return self.output.value(values)

    def reachable(self):
        reached = set()

        def visit(w):
            if w is None or w in reached:
                return
            reached.add(w)
            if w in self.gates:
                _, a, b = self.gates[w]
                visit(a)
                visit(b)

        visit(self.output.wire)
        return reached

    def fanouts(self):
        return Counter(a for _, a, b in self.gates.values()) + Counter(
            b for _, a, b in self.gates.values())

    def normalize(self, fixed=None):
        fixed = fixed or {}
        current = self
        while True:
            uses = current.fanouts()
            if current.output.wire is not None:
                uses[current.output.wire] += 1
            aliases = {i: Literal(None, fixed[i]) if i in fixed else Literal(i)
                       for i in range(self.n)}
            gates, intern = {}, {}

            def make(op, a, b):
                bases = sorted({v.wire for v in (a, b) if v.wire is not None})
                truth = []
                for z in range(1 << len(bases)):
                    values = {w: (z >> i) & 1 for i, w in enumerate(bases)}
                    truth.append((op >> (a.value(values) + 2 * b.value(values))) & 1)
                if len(set(truth)) == 1:
                    return Literal(None, truth[0])
                for i, w in enumerate(bases):
                    if all(bit == (((z >> i) & 1) ^ truth[0])
                           for z, bit in enumerate(truth)):
                        return Literal(w, truth[0])
                assert len(bases) == 2
                neg = truth[0]
                table = sum((bit ^ neg) << z for z, bit in enumerate(truth))
                key = (table, *bases)
                if key not in intern:
                    w = self.n + len(gates)
                    intern[key] = w
                    gates[w] = key
                return Literal(intern[key], neg)

            for w, (op, a, b) in sorted(current.gates.items()):
                folded = False
                for child, other, slot in ((a, b, 0), (b, a, 1)):
                    if child not in current.gates or uses[child] != 1:
                        continue
                    subop, u, v = current.gates[child]
                    if other not in (u, v):
                        continue
                    composed = 0
                    for z in range(4):
                        cv = (subop >> z) & 1
                        ov = (z >> (other == v)) & 1
                        idx = cv + 2 * ov if slot == 0 else ov + 2 * cv
                        composed |= ((op >> idx) & 1) << z
                    aliases[w] = make(composed, aliases[u], aliases[v])
                    folded = True
                    break
                if not folded:
                    aliases[w] = make(op, aliases[a], aliases[b])
            out = current.output
            if out.wire is not None:
                mapped = aliases[out.wire]
                out = Literal(mapped.wire, mapped.neg ^ out.neg)
            candidate = Circuit(self.n, gates, out)
            live = candidate.reachable()
            candidate.gates = {w: g for w, g in gates.items() if w in live}
            if len(candidate.gates) == len(current.gates) and not fixed:
                return candidate
            current, fixed = candidate, {}

    def drops(self, i):
        """Drops in s-d+1, retaining all unfixed coordinates in dimension d."""
        return tuple(len(self.gates) - len(self.normalize({i: b}).gates) - 1
                     for b in (0, 1))

    def safe_rule(self, i):
        neighbors = {w for w, (_, a, b) in self.gates.items() if i in (a, b)}
        if len(neighbors) >= 5:
            return True
        if len(neighbors) != 4:
            return False
        witnesses = []
        for g in neighbors:
            op, _, _ = self.gates[g]
            # Essential affine binary tables are XOR and XNOR.
            if op in (6, 9):
                continue
            successors = {w for w, (_, a, b) in self.gates.items()
                          if g in (a, b) and w not in neighbors}
            witnesses.append(successors)
        return any(a != b for j, left in enumerate(witnesses)
                   for right in witnesses[j + 1:] for a in left for b in right)

    def safe_exact_rule(self, i):
        neighbors = {w for w, (_, a, b) in self.gates.items() if i in (a, b)}
        if len(neighbors) >= 5:
            return True
        return len(neighbors) == 4 and any(
            self.gates[g][0] not in (6, 9) and
            any(g in (a, b) and w not in neighbors
                for w, (_, a, b) in self.gates.items())
            for g in neighbors)


def random_circuit(rng, n, s):
    gates = {n + j: (rng.randrange(16), rng.randrange(n + j), rng.randrange(n + j))
             for j in range(s)}
    return Circuit(n, gates, Literal(n + s - 1))


def check_normalization():
    rng = Random(20261006)
    cases = restrictions = safe = 0
    for _ in range(160):
        n = rng.randrange(2, 8)
        original = random_circuit(rng, n, rng.randrange(1, 6 * n))
        normalized = original.normalize()
        assert len(normalized.gates) <= len(original.gates)
        words = list(product((0, 1), repeat=n))
        assert all(original.evaluate(x) == normalized.evaluate(x) for x in words)
        cases += 1
        for i in range(n):
            for b in (0, 1):
                restricted = normalized.normalize({i: b})
                assert i not in restricted.reachable()
                assert all(normalized.evaluate(x) == restricted.evaluate(x)
                           for x in words if x[i] == b)
                restrictions += 1
            if normalized.safe_rule(i):
                drops = normalized.drops(i)
                assert min(drops) >= 3 and sum(drops) >= 8, drops
                safe += 1
    print(f"Normalization: {cases} full truth tables, {restrictions} restrictions; "
          f"{safe} safe-rule instances checked.")


def check_branch_moments():
    # For drops (3,5), theta=1/2 fails at B=1/4. B>1/4 and theta near 1 succeed.
    def factor(theta, B, drops):
        return sum(exp2(-theta - (1 - theta) * B * d) for d in drops)

    assert factor(0.5, 0.25, (3, 5)) > 1
    for B in (0.251, 0.255, 0.26, 0.27):
        eta = min(0.5, (4 * B - 1) / (B * B * log(2)))
        result = factor(1 - eta, B, (3, 5))
        assert result < 1
        identity = exp2(eta * (1 - 4 * B)) * cosh(eta * B * log(2))
        assert abs(result - identity) < 1e-12
    print("Fractional branch factors: (3,5) fails at the exact quarter coefficient "
          "and passes the stated nearby-coefficient certificate.")


def check_safe_patterns():
    # Four gates fed by x, then two pairwise joins and a final join. The two
    # nonlinear children may control on the same or opposite values of x.
    checked = exact = 0
    for operations in product((6, 8, 4), repeat=4):
        for joins in product((6, 8, 14), repeat=3):
            gates = {5 + j: (op, 0, j + 1) for j, op in enumerate(operations)}
            gates.update({9: (joins[0], 5, 6), 10: (joins[1], 7, 8),
                          11: (joins[2], 9, 10)})
            circuit = Circuit(5, gates, Literal(11)).normalize()
            if circuit.safe_exact_rule(0):
                assert max(circuit.drops(0)) >= 4
                exact += 1
            if circuit.safe_rule(0):
                delta = circuit.drops(0)
                assert min(delta) >= 3 and sum(delta) >= 8, (operations, joins, delta)
                checked += 1
    print(f"Layered fanout patterns: {checked} safe-rule circuits checked.")
    print(f"Exact-only restriction rule: {exact} circuits have a paid chosen branch.")
    rng = Random(765)
    for _ in range(80):
        degree = rng.choice((5, 6))
        n = degree + 1
        gates = {n + j: (rng.choice((6, 8, 4)), 0, j + 1) for j in range(degree)}
        pending = list(gates)
        while len(pending) > 1:
            rng.shuffle(pending)
            a, b = pending.pop(), pending.pop()
            w = n + len(gates)
            gates[w] = (rng.choice((6, 8, 14)), a, b)
            pending.append(w)
        original = Circuit(n, gates, Literal(pending[0]))
        circuit = original.normalize()
        assert circuit.safe_rule(0) and min(circuit.drops(0)) >= 4
        assert all(circuit.evaluate(x) == original.evaluate(x)
                   for x in product((0, 1), repeat=n))
    print("High input fanout: 80 additional full truth tables and branch bounds checked.")


def affine_basis(rows):
    """Choose original rows as a basis and express every row in that basis."""
    pivots, basis, indices, expressions = {}, [], [], []
    for j, row in enumerate(rows):
        residual, coefficients = row, 0
        while residual:
            p = residual.bit_length() - 1
            if p not in pivots:
                unit = 1 << len(basis)
                pivots[p] = (residual, coefficients ^ unit)
                basis.append(row)
                indices.append(j)
                coefficients = unit
                break
            value, expression = pivots[p]
            residual ^= value
            coefficients ^= expression
        expressions.append(coefficients)
    return basis, indices, expressions


def parity(x):
    return x.bit_count() & 1


def check_affine_preparation():
    rng = Random(415)
    checked = 0
    for n in range(1, 8):
        for _ in range(16):
            m = rng.randrange(1, n + 5)
            rows = [rng.randrange(1 << n) for _ in range(m)]
            offsets = [rng.randrange(2) for _ in rows]
            basis, selected, expressions = affine_basis(rows)
            full_basis, _, _ = affine_basis(basis + [1 << i for i in range(n)])
            assert len(full_basis) == n
            constants = [offsets[i] for i in selected] + [0] * (n - len(basis))
            images = set()
            for x in range(1 << n):
                z = sum((parity(row & x) ^ c) << j
                        for j, (row, c) in enumerate(zip(full_basis, constants)))
                images.add(z)
                for row, offset, expression in zip(rows, offsets, expressions):
                    correction = offset ^ parity(expression & sum(
                        c << j for j, c in enumerate(constants[:len(basis)])))
                    assert parity(row & x) ^ offset == parity(expression & z) ^ correction
            assert len(images) == 1 << n
            checked += 1
    print(f"Affine preparation: {checked} affine maps checked on their entire domains.")
    for n in (10, 20):
        cycle = {tuple(sorted((i, (i + 1) % n))) for i in range(n)}
        for degree in (2, 3, 4):
            edges = cycle.copy()
            if degree == 3:
                edges.update((i, i + n // 2) for i in range(n // 2))
            if degree == 4:
                edges.update(tuple(sorted((i, (i + 2) % n))) for i in range(n))
            rows = [(1 << i) ^ (1 << j) for i, j in sorted(edges)]
            basis, _, _ = affine_basis(rows)
            assert len(rows) == degree * n // 2 and len(basis) == n - 1
            assert len(rows) - len(basis) == (degree - 2) * n // 2 + 1
    print("Graphic affine interfaces: degree 2, 3, and 4 defect formulas checked.")


def check_restriction_moments():
    # Unequal leaf depths and different subsequent queried coordinates.
    n = 5
    leaves = ({0: 0}, {0: 1, 3: 0}, {0: 1, 3: 1, 1: 0},
              {0: 1, 3: 1, 1: 1})
    words = list(product((0, 1), repeat=n))
    assert all(sum(all(x[i] == b for i, b in leaf.items()) for leaf in leaves) == 1
               for x in words)
    for theta in (0.1, 0.5, 0.9, 0.99):
        eta = 1 - theta
        direct = phi = 0.0
        for leaf in leaves:
            domain = [x for x in words if all(x[i] == b for i, b in leaf.items())]
            histogram = Counter((x[0] ^ x[1], x[2] & x[3], x[1] ^ x[4])
                                for x in domain)
            moment = sum((count / len(domain)) ** theta for count in histogram.values())
            depth = len(leaf)
            direct += exp2(-depth) * exp2(-eta * (n - depth)) * moment
            phi += exp2(-theta * depth) * moment
        assert abs(direct - exp2(-eta * n) * phi) < 1e-12
    print("Adaptive leaf averaging: four moment parameters and unequal depths checked.")


def find_core():
    """A reproducible obstruction to the rule 'some input always pays'."""
    rng = Random(5111)
    for _ in range(100):
        n = 10
        gates = {}
        previous = list(range(n))
        # All first-layer gates are XORs, so fixing an input need not propagate
        # constants beyond that layer. Every layer uses each predecessor twice.
        for layer in range(4):
            rng.shuffle(previous)
            following = []
            for j in range(n):
                w = n + len(gates)
                gates[w] = (6 if layer == 0 else rng.choice((6, 6, 8)),
                            previous[j], previous[(j + 1) % n])
                following.append(w)
            previous = following
        while len(previous) > 1:
            a, b = previous.pop(), previous.pop()
            w = n + len(gates)
            gates[w] = (6, a, b)
            previous.append(w)
        original = Circuit(n, gates, Literal(previous[0]))
        circuit = original.normalize()
        if len(circuit.gates) < 4 * n:
            continue
        deltas = {i: circuit.drops(i) for i in range(n)}
        if max(sum(d) for d in deltas.values()) < 8:
            words = list(product((0, 1), repeat=n))
            assert all(circuit.evaluate(x) == original.evaluate(x) for x in words)
            print("Local-rule core:", {"inputs": n, "gates": len(circuit.gates),
                                        "drops": deltas})
            prefix = [(1 << a) ^ (1 << b) for op, a, b in circuit.gates.values()
                      if a < n and b < n and op == 6]
            basis, _, _ = affine_basis(prefix)
            assert len(prefix) == n and len(basis) == n - 1
            print(f"Core affine interface: {len(prefix)} signals, rank {len(basis)}, "
                  "one special parity gate after a change of basis.")
            return circuit
    print("No local-rule core found in this bounded search; no universal conclusion.")
    return None


if __name__ == "__main__":
    check_normalization()
    check_branch_moments()
    check_safe_patterns()
    check_affine_preparation()
    check_restriction_moments()
    find_core()
