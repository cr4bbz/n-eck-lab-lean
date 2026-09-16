import NEckLab.HutchinsonConvergence

namespace NEckLab

open Set Topology TopologicalSpace

noncomputable section

/-!
Gate 14: symbolic cylinders of the unique compact triangle attractor.

A finite address `a : List (Fin 3)` determines the image of the full attractor under the
corresponding composition of half-scale similarities. These cylinder sets are the finite-scale
pieces from which the dimension argument will later be built.
-/

/-- The attractor piece selected by a finite symbolic address. -/
def triangleCylinder (a : List (Fin 3)) : Set ℂ :=
  applyTriangleAddress a '' (triangleCompactAttractor : Set ℂ)

/-- The empty address selects the whole attractor. -/
@[simp]
theorem triangleCylinder_nil :
    triangleCylinder [] = (triangleCompactAttractor : Set ℂ) := by
  ext z
  simp [triangleCylinder]

/-- Prepending a symbol applies the corresponding first-level contraction to the remaining
cylinder. -/
theorem triangleCylinder_cons (j : Fin 3) (a : List (Fin 3)) :
    triangleCylinder (j :: a) = triangleContraction j '' triangleCylinder a := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨applyTriangleAddress a x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- Every first-level branch maps the attractor back into the attractor. -/
theorem triangleContraction_maps_attractor (j : Fin 3) :
    Set.MapsTo (triangleContraction j)
      (triangleCompactAttractor : Set ℂ)
      (triangleCompactAttractor : Set ℂ) := by
  intro z hz
  rw [← triangleCompactAttractor_set_fixed]
  unfold triangleIFS
  apply Set.mem_iUnion.mpr
  exact ⟨j, ⟨z, hz, rfl⟩⟩

/-- Every finite address maps the attractor into itself. -/
theorem applyTriangleAddress_maps_attractor (a : List (Fin 3)) :
    Set.MapsTo (applyTriangleAddress a)
      (triangleCompactAttractor : Set ℂ)
      (triangleCompactAttractor : Set ℂ) := by
  induction a with
  | nil =>
      intro z hz
      simpa using hz
  | cons j a ih =>
      intro z hz
      exact triangleContraction_maps_attractor j (ih hz)

/-- Hence every symbolic cylinder is a genuine subset of the unique attractor. -/
theorem triangleCylinder_subset_attractor (a : List (Fin 3)) :
    triangleCylinder a ⊆ (triangleCompactAttractor : Set ℂ) := by
  rintro z ⟨x, hx, rfl⟩
  exact applyTriangleAddress_maps_attractor a hx

/-- A depth-`m` address scales metric distances by exactly `2⁻ᵐ`. This is the metric content of a
cylinder's scale. -/
theorem triangleCylinder_exact_scale (a : List (Fin 3)) (z w : ℂ) :
    dist (applyTriangleAddress a z) (applyTriangleAddress a w) =
      dist z w / (2 : ℝ) ^ a.length := by
  exact applyTriangleAddress_dist a z w

/-- Cylinders are nonempty because the compact attractor is nonempty. -/
theorem triangleCylinder_nonempty (a : List (Fin 3)) :
    (triangleCylinder a).Nonempty := by
  rcases triangleCompactAttractor.nonempty with ⟨z, hz⟩
  exact ⟨applyTriangleAddress a z, z, hz, rfl⟩

end

end NEckLab
