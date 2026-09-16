import Mathlib

namespace NEckLab

/-- A deliberately weak geometric stage: for Gate 0 we record only which complex
points belong to the stage. More structure should be added only when a theorem
actually needs it. -/
structure GeometricStage where
  carrier : Set ℂ

/-- The regular-polygon regime begins at three sides. This is a condition on the
polygon model, not a claim that geometry itself begins at `n = 3`. -/
def IsPolygonStage (n : ℕ) : Prop := 3 ≤ n

@[simp] theorem isPolygonStage_three : IsPolygonStage 3 := by
  simp [IsPolygonStage]

/-- Replace exactly one stage in a sequence of sets. -/
def replaceStage {α : Type*} (F : ℕ → Set α) (k : ℕ) (A : Set α) : ℕ → Set α :=
  fun n => if n = k then A else F n

@[simp] theorem replaceStage_same {α : Type*}
    (F : ℕ → Set α) (k : ℕ) (A : Set α) :
    replaceStage F k A k = A := by
  simp [replaceStage]

@[simp] theorem replaceStage_of_ne {α : Type*}
    (F : ℕ → Set α) (k n : ℕ) (A : Set α) (h : n ≠ k) :
    replaceStage F k A n = F n := by
  simp [replaceStage, h]

/-- Fixing stage 3 as a triangle leaves stage 2 completely arbitrary unless an
additional transition law is supplied. This is the minimal formal version of
"the triangle does not determine its predecessor". -/
theorem arbitrary_stage_two_preserves_triangle {α : Type*}
    (F : ℕ → Set α) (A triangle : Set α)
    (hTriangle : F 3 = triangle) :
    replaceStage F 2 A 3 = triangle := by
  rw [replaceStage_of_ne F 2 3 A (by decide)]
  exact hTriangle

/-- Exterior/rotation angle step written with division. -/
def angleStep (n : ℕ) : ℝ :=
  2 * Real.pi / (n : ℝ)

/-- The same step written to expose the reciprocal explicitly. -/
def angleStepInv (n : ℕ) : ℝ :=
  2 * Real.pi * (n : ℝ)⁻¹

/-- `2π / n` and `2π * n⁻¹` are algebraically identical in Lean. -/
theorem angleStep_eq_angleStepInv (n : ℕ) :
    angleStep n = angleStepInv n := by
  simp [angleStep, angleStepInv, div_eq_mul_inv]

/-- For a genuine polygon stage the side count is nonzero. -/
theorem polygonStage_ne_zero {n : ℕ} (h : IsPolygonStage n) : n ≠ 0 := by
  omega

end NEckLab
