import NEckLab.CylinderCounting
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace NEckLab

open Set Topology Filter Metric TopologicalSpace
open scoped Topology ENNReal NNReal MeasureTheory

noncomputable section

/-!
Gate 16: upper Hausdorff-dimension infrastructure.

Gate 15 gave an exact finite cover at depth `m` indexed by `3^m` symbolic words, while every
address of length `m` scales point distances by `2^-m`. Here we package the composed maps as
Lipschitz maps and convert the exact pointwise scale into a uniform extended-diameter bound for
each cylinder. This is the analytic input required by `hausdorffMeasure_le_liminf_sum`.
-/

/-- The exact nonnegative scale attached to an address of depth `m`. -/
private def triangleWordScale (m : ℕ) : NNReal :=
  ⟨(1 / 2 : ℝ) ^ m, pow_nonneg (by norm_num) _⟩

@[simp]
theorem triangleWordScale_coe (m : ℕ) :
    (triangleWordScale m : ℝ) = (1 / 2 : ℝ) ^ m := rfl

/-- Every finite address is globally Lipschitz with its exact scale `2^-|a|`. -/
theorem applyTriangleAddress_lipschitz (a : List (Fin 3)) :
    LipschitzWith (triangleWordScale a.length) (applyTriangleAddress a) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro z w
  rw [applyTriangleAddress_dist]
  change dist z w / (2 : ℝ) ^ a.length ≤
    (1 / 2 : ℝ) ^ a.length * dist z w
  rw [one_div_pow]
  ring_nf
  exact le_rfl

/-- A canonical depth-`m` cylinder has extended diameter at most `2^-m` times the diameter of the
full attractor. -/
theorem triangleIndexedCylinder_ediam_le {m : ℕ} (a : TriangleWord m) :
    ediam (triangleIndexedCylinder a) ≤
      (triangleWordScale m : ℝ≥0∞) * ediam (triangleCompactAttractor : Set ℂ) := by
  change ediam
      (applyTriangleAddress (triangleWordAddress a) ''
        (triangleCompactAttractor : Set ℂ)) ≤ _
  have h :=
    (applyTriangleAddress_lipschitz (triangleWordAddress a)).ediam_image_le
      (triangleCompactAttractor : Set ℂ)
  simpa only [triangleWordAddress_length] using h

/-- The depth-`m` uniform diameter bound used by the Hausdorff-cover argument. -/
def triangleCoverRadius (m : ℕ) : ℝ≥0∞ :=
  (triangleWordScale m : ℝ≥0∞) * ediam (triangleCompactAttractor : Set ℂ)

/-- The attractor has finite extended diameter because it is compact. -/
theorem triangleAttractor_ediam_ne_top :
    ediam (triangleCompactAttractor : Set ℂ) ≠ ∞ := by
  exact Metric.isBounded_iff_ediam_ne_top.mp triangleCompactAttractor.isCompact.isBounded

/-- The uniform cylinder diameter tends to zero geometrically. -/
theorem tendsto_triangleCoverRadius_zero :
    Tendsto triangleCoverRadius atTop (𝓝 0) := by
  have hscale :
      Tendsto (fun m : ℕ => (1 / 2 : ℝ≥0∞) ^ m) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hmul :=
    ENNReal.Tendsto.mul_const hscale (Or.inr triangleAttractor_ediam_ne_top)
  simpa [triangleCoverRadius, triangleWordScale] using hmul

/-- Every cylinder in the canonical depth-`m` cover obeys the common radius bound. -/
theorem triangleIndexedCylinder_ediam_le_coverRadius (m : ℕ) (a : TriangleWord m) :
    ediam (triangleIndexedCylinder a) ≤ triangleCoverRadius m := by
  exact triangleIndexedCylinder_ediam_le a

/-- Gate 16 cover package: the `3^m` symbolic cylinders cover the attractor and all have diameter
bounded by a common quantity tending to zero. -/
theorem triangleFiniteCover_geometry (m : ℕ) :
    ((triangleCompactAttractor : Set ℂ) ⊆
        (⋃ a : TriangleWord m, triangleIndexedCylinder a)) ∧
    (∀ a : TriangleWord m,
      ediam (triangleIndexedCylinder a) ≤ triangleCoverRadius m) := by
  constructor
  · rw [triangleIndexedCylinders_cover]
  · exact triangleIndexedCylinder_ediam_le_coverRadius m

end

end NEckLab
