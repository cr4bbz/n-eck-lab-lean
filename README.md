# n-eck-lab-lean

Lean 4 / mathlib laboratory for studying regular polygons, the passage from finite side counts toward circular geometry, and possible geometric predecessors of the first regular polygon.

## Research split

- **Track A — n-gons:** regular `n`-gons for `n ≥ 3`, reciprocal angle step `2π · n⁻¹`, complex-coordinate rotations, and limiting behaviour as `n → ∞`.
- **Track B — pre-3 geometry:** do **not** assume that the geometric story starts at the triangle. Formalize what follows from `stage 3 = triangle` and what remains underdetermined about earlier stages. Fractal candidates are hypotheses, not axioms.
- **Track C — size notions:** keep cardinality, density, measure, and Hausdorff dimension distinct so different senses of “larger”, “denser”, and “more continuous” are not conflated.

## Gates

### Gate 0 — laboratory scaffold
- Lean/mathlib project builds.
- Minimal geometric-stage vocabulary.
- No theorem silently assumes a predecessor of the triangle.

### Gate 1 — regular polygon core
- Define the root-of-unity / complex-coordinate vertex map.
- State the angle step as both `2π / n` and `2π * n⁻¹` and prove their algebraic equivalence.
- Encode the `n ≥ 3` polygon condition explicitly.

### Gate 2 — predecessor underdetermination
- Prove that fixing stage 3 does not determine stage 2 without an additional transition law.
- Separate arbitrary predecessor sets from later fractal-specific hypotheses.

### Gate 3 — metric and dimensional observables
- Add Hausdorff-distance or related convergence observables where mathlib support is adequate.
- Investigate Hausdorff dimension separately from polygon side count.

The repository is intentionally a lab: conjectures should be marked as such, theorem statements should expose their assumptions, and every conceptual jump should be inspectable by Lean.
