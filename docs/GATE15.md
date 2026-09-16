# Gate 15 — Cylinder Counting and Cover Geometry

## Research question

Gate 14 established that every finite symbolic depth reconstructs the unique compact triangle attractor and that a word of length `m` scales all point distances by exactly `2^-m`.

Gate 15 asks for the combinatorial half of the dimension argument:

> How many canonical symbolic pieces are available at depth `m`, and can they be used as a finite cover of the attractor with a controlled metric scale?

## Scope

This gate deliberately separates the **upper-dimension** ingredients from the harder **lower-dimension** ingredients.

### In Gate 15

1. Introduce a canonical exact-depth word type
   ```lean
   TriangleWord m := Fin m → Fin 3
   ```
2. Prove the exact address count
   ```text
   card(TriangleWord m) = 3^m.
   ```
3. Bridge canonical words to the existing list-based IFS address layer.
4. Define the corresponding canonically indexed cylinders.
5. Prove exact metric scale
   ```text
   d(T_a z, T_a w) = d(z,w) / 2^m.
   ```
6. Prove that the `3^m` indexed cylinders cover the full compact attractor.
7. Prepare a finite-cover formulation suitable for `hausdorffMeasure_le_liminf_sum` or an equivalent Hausdorff-measure estimate.

### Explicitly deferred to Gate 16

- pairwise overlap classification;
- open-set/separation condition;
- lower Hausdorff-dimension bound;
- proof that different symbolic words give genuinely distinct geometric cylinders where required.

The number `3^m` in Gate 15 counts **symbolic addresses**. It must not yet be silently identified with the number of pairwise distinct subsets, because boundary overlaps and possible coding multiplicity are exactly what Gate 16 must control.

## Target mathematical bridge

At depth `m` we want a certified cover of the form

```text
F = ⋃_{a : TriangleWord m} F_a
```

with

```text
# addresses = 3^m
scale(F_a) = 2^-m.
```

This is the formal precursor of the upper-dimension heuristic

```text
3^m * (2^-m)^d.
```

The similarity exponent is the unique `d` satisfying

```text
3 * 2^-d = 1,
```

namely `log 3 / log 2`, but Gate 15 does **not** claim the final Hausdorff-dimension equality.

## Exit criteria

Gate 15 is complete when:

- the new counting module builds with no `sorry`;
- `Fintype.card (TriangleWord m) = 3^m` is Lean-verified;
- the canonical cylinders cover the attractor at every depth;
- the exact `2^-m` scale theorem is available for the canonical indexing;
- CI is green;
- the next gate can begin directly from a finite cover indexed by a type of cardinality `3^m`.

## Next gate

**Gate 16 — Cylinder Separation and Lower-Dimension Infrastructure**

The expected focus is a rigorous treatment of overlaps between the three first-level copies and their descendants, followed by a separation or mass-distribution statement strong enough to support a lower Hausdorff-dimension bound.
