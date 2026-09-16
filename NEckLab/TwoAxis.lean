import NEckLab.LimitsAndDimension
import NEckLab.FractalCandidate

namespace NEckLab

open Filter Topology

/-!
Gate 9: side count and refinement depth are independent axes.
The file also contains a verified counterexample showing that two iterated limits need not commute.
-/

/-- Abstract two-axis geometric family: `n` is polygon order, `m` is refinement depth. -/
structure TwoAxisGeometry where
  carrier : ℕ → ℕ → Set ℂ

namespace TwoAxisGeometry

/-- Hold refinement depth fixed and vary polygon order. -/
def polygonSlice (G : TwoAxisGeometry) (m : ℕ) : ℕ → Set ℂ :=
  fun n => G.carrier n m

/-- Hold polygon order fixed and vary refinement depth. -/
def refinementSlice (G : TwoAxisGeometry) (n : ℕ) : ℕ → Set ℂ :=
  fun m => G.carrier n m

end TwoAxisGeometry

/-- A real-valued observable on the two independent complexity axes. -/
def orderObservable (n m : ℕ) : ℝ :=
  if n ≤ m then 1 else 0

/-- For fixed polygon order `n`, increasing refinement depth eventually puts the observable at `1`. -/
theorem orderObservable_refinement_tendsto (n : ℕ) :
    Tendsto (fun m => orderObservable n m) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop n] with m hm
  simp [orderObservable, hm]

/-- For fixed refinement depth `m`, increasing polygon order eventually puts the observable at `0`. -/
theorem orderObservable_polygon_tendsto (m : ℕ) :
    Tendsto (fun n => orderObservable n m) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop m] with n hn
  simp [orderObservable, Nat.not_le.mpr hn]

/-- A witness package for genuinely noncommuting iterated limits. -/
structure NoncommutingIteratedLimits (f : ℕ → ℕ → ℝ) where
  refinementLimit : ℕ → ℝ
  polygonLimit : ℕ → ℝ
  refinementThenPolygon : ℝ
  polygonThenRefinement : ℝ
  refinement_tendsto : ∀ n, Tendsto (fun m => f n m) atTop (𝓝 (refinementLimit n))
  polygon_tendsto : ∀ m, Tendsto (fun n => f n m) atTop (𝓝 (polygonLimit m))
  outer_refinement_tendsto : Tendsto refinementLimit atTop (𝓝 refinementThenPolygon)
  outer_polygon_tendsto : Tendsto polygonLimit atTop (𝓝 polygonThenRefinement)
  limits_ne : refinementThenPolygon ≠ polygonThenRefinement

/-- Gate 9: a fully verified witness that the two orders of limiting can disagree. -/
def orderObservable_noncommuting : NoncommutingIteratedLimits orderObservable where
  refinementLimit := fun _ => 1
  polygonLimit := fun _ => 0
  refinementThenPolygon := 1
  polygonThenRefinement := 0
  refinement_tendsto := orderObservable_refinement_tendsto
  polygon_tendsto := orderObservable_polygon_tendsto
  outer_refinement_tendsto := tendsto_const_nhds
  outer_polygon_tendsto := tendsto_const_nhds
  limits_ne := one_ne_zero

end NEckLab
