import NEckLab.FractalCandidate
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.HausdorffDimension

namespace NEckLab

open Topology

/-!
Gate 11: closure as a genuinely structure-creating operation.

The reference example uses the rational numbers inside the reals. The rational cloud is countable,
so its Hausdorff dimension is zero, but it is dense in `ℝ`; therefore its closure is all of `ℝ`,
whose Hausdorff dimension is one.

The second half places `sierpinskiCandidate` at the same formal boundary without assuming a positive
Hausdorff dimension for that candidate before it is proved.
-/

/-- The rational numbers viewed as a subset of the real line. -/
def rationalCloud : Set ℝ :=
  Set.range ((↑) : ℚ → ℝ)

/-- The rational cloud is countable. -/
theorem rationalCloud_countable : rationalCloud.Countable := by
  unfold rationalCloud
  exact Set.countable_range _

/-- Countability forces the rational cloud to have Hausdorff dimension zero. -/
theorem rationalCloud_dimH_zero :
    dimH rationalCloud = 0 := by
  exact rationalCloud_countable.dimH_zero

/-- The rational cloud is dense in the real line. -/
theorem rationalCloud_dense : Dense rationalCloud := by
  unfold rationalCloud
  exact Rat.denseRange_cast

/-- Closing the rational cloud fills the entire real line. -/
theorem closure_rationalCloud :
    closure rationalCloud = Set.univ := by
  exact rationalCloud_dense.closure_eq

/-- The closure has Hausdorff dimension one. -/
theorem closure_rationalCloud_dimH_one :
    dimH (closure rationalCloud) = 1 := by
  rw [closure_rationalCloud]
  exact Real.dimH_univ

/-- Gate 11 reference theorem: topological closure can strictly increase Hausdorff dimension. -/
theorem closure_strictly_increases_dimH_on_rationalCloud :
    dimH rationalCloud < dimH (closure rationalCloud) := by
  rw [rationalCloud_dimH_zero, closure_rationalCloud_dimH_one]
  exact zero_lt_one

/-- There exists a Hausdorff-dimension-zero set whose closure has Hausdorff dimension one. -/
theorem exists_closure_dimension_jump :
    ∃ s : Set ℝ, dimH s = 0 ∧ dimH (closure s) = 1 := by
  exact ⟨rationalCloud, rationalCloud_dimH_zero, closure_rationalCloud_dimH_one⟩

/-- The chosen triangle limit candidate is closed by construction. -/
theorem sierpinskiCandidate_closed :
    IsClosed sierpinskiCandidate := by
  exact isClosed_closure

/-- The candidate is the smallest closed set containing every finite-stage orbit point. -/
theorem sierpinskiCandidate_minimal {s : Set ℂ}
    (horbit : sierpinskiOrbit ⊆ s) (hs : IsClosed s) :
    sierpinskiCandidate ⊆ s := by
  unfold sierpinskiCandidate
  exact closure_minimal horbit hs

/-- Passing from the finite-stage orbit to its closure cannot lower Hausdorff dimension. -/
theorem sierpinskiOrbit_dimH_le_candidate :
    dimH sierpinskiOrbit ≤ dimH sierpinskiCandidate := by
  exact dimH_mono sierpinskiOrbit_subset_candidate

/-- If the candidate eventually receives a positive-dimension proof, then Gate 8 and Gate 11
combine to certify a strict dimension jump at the closure step. -/
theorem sierpinski_positive_dim_implies_closure_jump
    (hpos : 0 < dimH sierpinskiCandidate) :
    dimH sierpinskiOrbit < dimH sierpinskiCandidate := by
  rw [sierpinskiOrbit_dimH_zero]
  exact hpos

/-- Positive Hausdorff dimension of the candidate would also imply that it is uncountable. -/
theorem sierpinskiCandidate_not_countable_of_positive_dim
    (hpos : 0 < dimH sierpinskiCandidate) :
    ¬ sierpinskiCandidate.Countable := by
  intro hcount
  have hzero : dimH sierpinskiCandidate = 0 := hcount.dimH_zero
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

end NEckLab
