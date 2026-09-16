# n-eck-lab-lean

Lean 4 / mathlib laboratory for studying regular polygons, the passage from finite side counts toward circular geometry, and possible geometric predecessors of the first regular polygon.

## Research split

- **Track A - n-gons:** regular `n`-gons for `n ≥ 3`, reciprocal angle step `2π · n⁻¹`, complex-coordinate rotations, and limiting behaviour as `n → ∞`.
- **Track B - pre-3 geometry:** do **not** assume that the geometric story starts at the triangle. Formalize what follows from `stage 3 = triangle` and what remains underdetermined about earlier stages. Fractal candidates are hypotheses, not axioms.
- **Track C - size notions:** keep cardinality, density, measure, and Hausdorff dimension distinct so different senses of “larger”, “denser”, and “more continuous” are not conflated.

## Gates

### Gate 0 - laboratory scaffold ✅
- Lean/mathlib project builds.
- Minimal geometric-stage vocabulary.
- No theorem silently assumes a predecessor of the triangle.

### Gate 1 - regular polygon core ✅
- Define the complex-coordinate vertex map.
- State the angle step as both `2π / n` and `2π * n⁻¹` and prove their algebraic equivalence.
- Encode the `n ≥ 3` polygon condition explicitly.
- Add native VS Code InfoView polygon rendering.

### Gate 2 - fixed rotation and cycle closure ✅
- Define the fixed complex rotator `ρₙ = exp(i θₙ)`.
- Prove `zₖ₊₁ = ρₙ zₖ`.
- Prove `zₖ = ρₙ^k`.
- Prove `ρₙ^n = 1` and `zₙ = 1` for nonzero `n`.

### Gate 3 - polygon-to-circle convergence observable
- Prove `θₙ → 0` as `n → ∞`.
- Define the radial defect `1 - cos(π/n)` and prove it tends to `0`.
- This is a verified scalar convergence witness. A full Hausdorff-distance theorem remains a later strengthening, not an assumed fact.

### Gate 4 - reciprocal scale and local/global invariant
- Make `n⁻¹` a first-class observable.
- Prove `n⁻¹ → 0`.
- Prove `θₙ = 2π n⁻¹` while `n θₙ = 2π` for nonzero `n`.

### Gate 5 - Hausdorff-dimension separation
- Define the finite exact vertex set of each regular polygon.
- Prove every such vertex set has Hausdorff dimension `0`.
- Prove increasing side count alone does not increase the Hausdorff dimension of the finite vertex cloud.

### Gate 6 - predecessor underdetermination
- Prove that fixing stage 3 does not determine stage 2 without an additional transition law.
- Express possible predecessors as fibers of a transition.
- Prove injectivity implies predecessor uniqueness.

### Gate 7 - transition-law classes
- Distinguish faithful/injective transitions from coarse-graining transitions.
- Prove a collision certifies coarse-graining.
- Prove a left inverse certifies faithful predecessor information.
- Prove composition preserves faithful transitions.

### Gate 8 - self-similar triangle candidate
- Use the three exact triangle corners to define three half-scale contractions.
- Build finite nested refinement clouds.
- Define the countable orbit and its closure as a geometric limit candidate.
- Prove every finite approximant and the countable finite-stage orbit have Hausdorff dimension `0`.
- No positive dimension is asserted for the closure without a separate proof.

### Gate 9 - two independent complexity axes
- Represent geometry as `G(n,m)`, where `n` is polygon order and `m` is refinement depth.
- Define polygon and refinement slices.
- Give a fully verified real-valued counterexample whose two iterated limits disagree.
- Therefore limit commutation must be proved for a concrete geometry, never assumed.

### Gate 10 - research visualization surface
- Keep the existing exact-to-Float visualization boundary explicit.
- Overlay `n = 3, 4, 6, 12, 40` against the unit circle in VS Code InfoView.
- Render a finite self-similar triangle cloud by refinement depth.
- Use visualization as an inspection instrument, never as proof evidence.

## Current research boundary

The repository now formally separates three phenomena that are easy to conflate:

1. local angular scale tends to zero;
2. finite vertex clouds remain Hausdorff-dimension zero;
3. a topological closure or other limiting construction may have genuinely different structure from every finite approximant.

The next major strengthening would be a true Hausdorff-distance convergence theorem for polygonal boundaries or filled polygons and a rigorous dimension theorem for the chosen self-similar closure.

The repository is intentionally a lab: conjectures should be marked as such, theorem statements should expose their assumptions, and every conceptual jump should be inspectable by Lean.
