import NEckLab.HutchinsonAttractor

namespace NEckLab

open Set Topology Filter TopologicalSpace
open scoped Topology

noncomputable section

/-!
Gate 14: Hausdorff convergence of the exact IFS generations.

Gate 12 introduced pure symbolic generations `triangleWordCloud m`. Gate 13 constructed the unique
nonempty compact fixed point of the Hutchinson operator. Here the two views are connected: starting
from the singleton seed and iterating the compact IFS produces exactly the pure word clouds, and
Banach convergence therefore turns the finite generations into a genuine Hausdorff approximation
scheme for the attractor.
-/

/-- The compact generation obtained after exactly `m` applications of the Hutchinson operator. -/
def triangleCompactGeneration (m : ℕ) : NonemptyCompacts ℂ :=
  (triangleCompactIFS^[m]) ({0} : NonemptyCompacts ℂ)

@[simp]
theorem triangleCompactGeneration_zero :
    triangleCompactGeneration 0 = ({0} : NonemptyCompacts ℂ) := by
  simp [triangleCompactGeneration]

/-- One more compact generation is exactly one more Hutchinson step. -/
theorem triangleCompactGeneration_succ (m : ℕ) :
    triangleCompactGeneration (m + 1) =
      triangleCompactIFS (triangleCompactGeneration m) := by
  simp [triangleCompactGeneration, Function.iterate_succ_apply']

/-- The compact-generation carrier is exactly the pure finite-word cloud from Gate 12. -/
theorem coe_triangleCompactGeneration (m : ℕ) :
    (triangleCompactGeneration m : Set ℂ) = triangleWordCloud m := by
  induction m with
  | zero =>
      simp [triangleWordCloud_zero]
  | succ m ih =>
      rw [Nat.succ_eq_add_one, triangleCompactGeneration_succ]
      rw [coe_triangleCompactIFS, ih, ← triangleWordCloud_succ]

/-- The chosen Gate 13 attractor agrees with mathlib's canonical Banach fixed point. -/
theorem triangleCompactAttractor_eq_fixedPoint :
    triangleCompactAttractor =
      ContractingWith.fixedPoint triangleCompactIFS triangleCompactIFS_contracting := by
  exact triangleCompactIFS_contracting.fixedPoint_unique triangleCompactAttractor_fixed

/-- Gate 14 core: the exact finite generations converge in Hausdorff metric to the unique
triangle attractor. -/
theorem triangleCompactGeneration_tendsto :
    Tendsto triangleCompactGeneration atTop (𝓝 triangleCompactAttractor) := by
  have h := triangleCompactIFS_contracting.tendsto_iterate_fixedPoint
    ({0} : NonemptyCompacts ℂ)
  rw [← triangleCompactAttractor_eq_fixedPoint] at h
  simpa [triangleCompactGeneration] using h

/-- Equivalently, the Hausdorff distance from the finite generation to the attractor tends to zero. -/
theorem triangleCompactGeneration_dist_tendsto_zero :
    Tendsto (fun m => dist (triangleCompactGeneration m) triangleCompactAttractor)
      atTop (𝓝 0) := by
  have h := triangleCompactGeneration_tendsto.dist tendsto_const_nhds
  simpa using h

end

end NEckLab
