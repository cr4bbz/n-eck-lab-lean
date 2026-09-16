import NEckLab.SymbolicCylinders
import Mathlib.Data.List.OfFn

namespace NEckLab

open Set Topology TopologicalSpace

noncomputable section

/-!
Gate 15: finite symbolic indexing and cover geometry.

Gate 14 showed that every finite depth reconstructs the attractor from address images and that
an address of length `m` scales all distances by `2⁻ᵐ`. Here we replace variable-length lists by a
canonical fixed-length index type `Fin m → Fin 3`. This makes the combinatorics explicit: there are
exactly `3^m` symbolic addresses at depth `m`.

This gate deliberately separates the upper-dimension ingredients (finite cover count and scale)
from the harder lower-dimension ingredient (controlled overlap / separation), which is reserved for
the next gate.
-/

/-- Canonical symbolic words of exact depth `m`. -/
abbrev TriangleWord (m : ℕ) := Fin m → Fin 3

/-- Convert a fixed-length word to the list representation used by the earlier IFS layer. -/
def triangleWordAddress {m : ℕ} (a : TriangleWord m) : List (Fin 3) :=
  List.ofFn a

@[simp]
theorem triangleWordAddress_length {m : ℕ} (a : TriangleWord m) :
    (triangleWordAddress a).length = m := by
  simp [triangleWordAddress]

/-- There are exactly `3^m` symbolic words of depth `m`. -/
theorem triangleWord_card (m : ℕ) :
    Fintype.card (TriangleWord m) = 3 ^ m := by
  simp [TriangleWord]

/-- The attractor cylinder indexed by a canonical depth-`m` word. -/
def triangleIndexedCylinder {m : ℕ} (a : TriangleWord m) : Set ℂ :=
  triangleCylinder (triangleWordAddress a)

/-- Canonically indexed cylinders inherit the exact depth scale `2⁻ᵐ`. -/
theorem triangleIndexedCylinder_exact_scale {m : ℕ} (a : TriangleWord m) (z w : ℂ) :
    dist (applyTriangleAddress (triangleWordAddress a) z)
      (applyTriangleAddress (triangleWordAddress a) w) =
      dist z w / (2 : ℝ) ^ m := by
  simpa only [triangleWordAddress_length] using
    (triangleCylinder_exact_scale (triangleWordAddress a) z w)

/-- Every canonical depth-`m` cylinder is contained in the unique compact attractor. -/
theorem triangleIndexedCylinder_subset_attractor {m : ℕ} (a : TriangleWord m) :
    triangleIndexedCylinder a ⊆ (triangleCompactAttractor : Set ℂ) := by
  exact triangleCylinder_subset_attractor (triangleWordAddress a)

/-- Every list address of length `m` has a canonical `Fin m → Fin 3` representative. -/
theorem exists_triangleWord_of_address {m : ℕ} (a : List (Fin 3))
    (ha : a.length = m) :
    ∃ f : TriangleWord m, triangleWordAddress f = a := by
  let f : TriangleWord m := fun i => a.get (Fin.cast ha.symm i)
  refine ⟨f, ?_⟩
  dsimp [triangleWordAddress, f]
  simpa using (List.ofFn_congr ha a.get).symm

/-- The `3^m` canonically indexed cylinders cover the full attractor at every finite depth. -/
theorem triangleIndexedCylinders_cover (m : ℕ) :
    (⋃ a : TriangleWord m, triangleIndexedCylinder a) =
      (triangleCompactAttractor : Set ℂ) := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨a, ha⟩
    exact triangleIndexedCylinder_subset_attractor a ha
  · intro z hz
    obtain ⟨a, haLen, w, hw, hzw⟩ := attractor_has_finite_address m hz
    obtain ⟨f, hf⟩ := exists_triangleWord_of_address a haLen
    apply Set.mem_iUnion.mpr
    refine ⟨f, ?_⟩
    change z ∈ applyTriangleAddress (triangleWordAddress f) ''
      (triangleCompactAttractor : Set ℂ)
    refine ⟨w, hw, ?_⟩
    rw [hf]
    exact hzw

end

end NEckLab
