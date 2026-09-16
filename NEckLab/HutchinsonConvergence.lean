import NEckLab.HutchinsonAttractor

namespace NEckLab

open Set Topology Filter TopologicalSpace
open scoped Topology

noncomputable section

/-!
Gate 13 continuation: identify the exact finite word generations with iterates of the compact IFS,
then inherit Hausdorff convergence from the contraction mapping theorem.
-/

/-- Package the pure depth-`m` word cloud as a nonempty compact set. -/
def triangleWordCompact (m : ℕ) : NonemptyCompacts ℂ := by
  refine ⟨⟨triangleWordCloud m, (triangleWordCloud_finite m).isCompact⟩, ?_⟩
  let a : List (Fin 3) := List.replicate m 0
  refine ⟨applyTriangleAddress a 0, ?_⟩
  exact ⟨a, by simp [a], rfl⟩

@[simp]
theorem coe_triangleWordCompact (m : ℕ) :
    (triangleWordCompact m : Set ℂ) = triangleWordCloud m := rfl

/-- The compact depth-zero generation is the singleton seed. -/
theorem triangleWordCompact_zero :
    triangleWordCompact 0 = ({0} : NonemptyCompacts ℂ) := by
  apply NonemptyCompacts.ext
  simpa using triangleWordCloud_zero

/-- The pure compact generations follow the lifted IFS exactly. -/
theorem triangleWordCompact_succ (m : ℕ) :
    triangleWordCompact (m + 1) = triangleCompactIFS (triangleWordCompact m) := by
  apply NonemptyCompacts.ext
  simpa using triangleWordCloud_succ m

/-- Iterating the compact IFS from the singleton seed gives exactly the finite word generation. -/
theorem triangleCompactIFS_iterate_singleton (m : ℕ) :
    (triangleCompactIFS^[m]) ({0} : NonemptyCompacts ℂ) = triangleWordCompact m := by
  induction m with
  | zero =>
      rw [Function.iterate_zero_apply]
      exact triangleWordCompact_zero.symm
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      simpa [Nat.succ_eq_add_one] using (triangleWordCompact_succ m).symm

/-- Gate 13 convergence theorem: exact finite IFS generations converge in Hausdorff distance to
    the unique compact attractor. -/
theorem tendsto_triangleWordCompact_attractor :
    Tendsto triangleWordCompact atTop (𝓝 triangleCompactAttractor) := by
  have hBuilt :
      Function.IsFixedPt triangleCompactIFS
        (triangleCompactIFS_contracting.fixedPoint triangleCompactIFS) :=
    triangleCompactIFS_contracting.fixedPoint_isFixedPt
  have hEq :
      triangleCompactIFS_contracting.fixedPoint triangleCompactIFS =
        triangleCompactAttractor :=
    triangleCompactAttractor_unique hBuilt triangleCompactAttractor_fixed
  have h :=
    triangleCompactIFS_contracting.tendsto_iterate_fixedPoint
      ({0} : NonemptyCompacts ℂ)
  rw [hEq] at h
  simpa only [triangleCompactIFS_iterate_singleton] using h

end

end NEckLab
