#!/usr/bin/env python3
"""Validates: the displayed numerical conversion L = 1 + 1/(2p)."""
import math

p = 3 / (2 * math.pi) * math.acos((1 + 2 * math.sqrt(2)) / 4)
print(f"Gaussian p = {p:.10f}")
print(f"Gaussian A = {2*p:.10f}")
print(f"Gaussian L = {1+1/(2*p):.10f}")
for target in (4, 4.6, 5, 6, 10):
    print(f"Target L = {target:g}: p <= {1/(2*(target-1)):.10f}")
