import NEckLab.HutchinsonConvergence

namespace NEckLab

open Set Topology Metric TopologicalSpace
open scoped Topology

noncomputable section

/-!
Gate 14: symbolic cylinders and quantitative finite-depth control.

Gate 13 gave a unique compact Hutchinson attractor and Hausdorff convergence of the exact finite
word generations. Here we expose the symbolic structure behind that attractor: every depth `m`
point lies in the image of the attractor under an address of length `m`, and conversely these
address images cover the attractor exactly. The point-level metric scaling remains exactly `2⁻ᵐ`.
-/

/-- Points obtained by applying some address of exact length `m` to a seed in `S`. -/
def triangleAddressImage (m : ℕ) (S : Set ℂ) : Set ℂ :=
  {z | ∃ a : List (Fin 3), a.length = m ∧ ∃ w ∈ S, applyTriangleAddress a w = z}

/-- At depth zero, address images do nothing. -/
theorem triangleAddressImage_zero (S : Set ℂ) :
    triangleAddressImage 0 S = S := by
  ext z
  simp [triangleAddressImage]

/-- One more symbolic digit is exactly one application of the three-branch IFS. -/
theorem triangleAddressImage_succ (m : ℕ) (S : Set ℂ) :
    triangleAddressImage (m + 1) S = triangleIFS (triangleAddressImage m S) := by
  ext z
  constructor
  · rintro ⟨a, ha, w, hw, haz⟩
    cases a with
    | nil => simp at ha
    | cons j a =>
        have hlen : a.length = m := by
          simpa using Nat.succ.inj ha
        unfold triangleIFS
        apply Set.mem_iUnion.mpr
        refine ⟨j, ?_⟩
        refine ⟨applyTriangleAddress a w, ?_, ?_⟩
        · exact ⟨a, hlen, w, hw, rfl⟩
        · simpa using haz
  · intro hz
    unfold triangleIFS at hz
    rcases Set.mem_iUnion.mp hz with ⟨j, hj⟩
    rcases hj with ⟨y, hy, rfl⟩
    rcases hy with ⟨a, ha, w, hw, rfl⟩
    refine ⟨j :: a, ?_, w, hw, rfl⟩
    simp [ha]

/-- Every symbolic depth reconstructs the compact attractor exactly. -/
theorem triangleAddressImage_attractor (m : ℕ) :
    triangleAddressImage m (triangleCompactAttractor : Set ℂ) =
      (triangleCompactAttractor : Set ℂ) := by
  induction m with
  | zero =>
      exact triangleAddressImage_zero _
  | succ m ih =>
      rw [triangleAddressImage_succ, ih, triangleCompactAttractor_set_fixed]

/-- A symbolic cylinder is the image of the attractor under one finite address. -/
def triangleCylinder (a : List (Fin 3)) : Set ℂ :=
  applyTriangleAddress a '' (triangleCompactAttractor : Set ℂ)

/-- Every finite cylinder lies inside the full attractor. -/
theorem triangleCylinder_subset_attractor (a : List (Fin 3)) :
    triangleCylinder a ⊆ (triangleCompactAttractor : Set ℂ) := by
  intro z hz
  have hz' :
      z ∈ triangleAddressImage a.length (triangleCompactAttractor : Set ℂ) := by
    rcases hz with ⟨w, hw, rfl⟩
    exact ⟨a, rfl, w, hw, rfl⟩
  rw [triangleAddressImage_attractor] at hz'
  exact hz'

/-- Every attractor point has a symbolic address of every prescribed finite depth. -/
theorem attractor_has_finite_address (m : ℕ) {z : ℂ}
    (hz : z ∈ (triangleCompactAttractor : Set ℂ)) :
    ∃ a : List (Fin 3), a.length = m ∧
      ∃ w ∈ (triangleCompactAttractor : Set ℂ), applyTriangleAddress a w = z := by
  have hz' : z ∈ triangleAddressImage m (triangleCompactAttractor : Set ℂ) := by
    rw [triangleAddressImage_attractor]
    exact hz
  exact hz'

/-- An address of length `m` scales point distances exactly by `2⁻ᵐ`. -/
theorem triangleCylinder_exact_scale (a : List (Fin 3)) (z w : ℂ) :
    dist (applyTriangleAddress a z) (applyTriangleAddress a w) =
      dist z w / (2 : ℝ) ^ a.length :=
  applyTriangleAddress_dist a z w

/-- Quantitative Gate 14 bound: the exact finite word generation approaches the attractor at least
    geometrically with ratio `1/2` in Hausdorff distance. -/
theorem triangleWordCompact_dist_attractor_le (m : ℕ) :
    dist (triangleWordCompact m) triangleCompactAttractor ≤
      dist ({0} : NonemptyCompacts ℂ) triangleCompactAttractor / (2 : ℝ) ^ m := by
  induction m with
  | zero =>
      simp [triangleWordCompact_zero]
  | succ m ih =>
      calc
        dist (triangleWordCompact (m + 1)) triangleCompactAttractor
            = dist (triangleCompactIFS (triangleWordCompact m))
                (triangleCompactIFS triangleCompactAttractor) := by
              rw [triangleWordCompact_succ, triangleCompactAttractor_fixed]
        _ ≤ dist (triangleWordCompact m) triangleCompactAttractor / 2 :=
          triangleCompactIFS_dist_le _ _
        _ ≤ (dist ({0} : NonemptyCompacts ℂ) triangleCompactAttractor / (2 : ℝ) ^ m) / 2 := by
          exact div_le_div_of_nonneg_right ih (by norm_num)
        _ = dist ({0} : NonemptyCompacts ℂ) triangleCompactAttractor / (2 : ℝ) ^ (m + 1) := by
          rw [pow_succ]
          ring

end

end NEckLab
