import NEckLab.RegularPolygon
import Mathlib.Topology.MetricSpace.HausdorffDimension

namespace NEckLab

open Filter Topology

/-!
Gates 3–5: asymptotic polygon observables, reciprocal scale, and dimension separation.
-/

/-- The reciprocal side-count scale made explicit. -/
noncomputable def inverseScale (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹

/-- Gate 4: the reciprocal scale tends to zero. -/
theorem tendsto_inverseScale_zero :
    Tendsto inverseScale atTop (𝓝 0) := by
  unfold inverseScale
  exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

/-- The angular step is exactly a fixed `2π` factor times the reciprocal scale. -/
theorem angleStep_eq_two_pi_mul_inverseScale (n : ℕ) :
    angleStep n = 2 * Real.pi * inverseScale n := by
  simp [angleStep, inverseScale, div_eq_mul_inv]

/-- Gate 3: local angular change vanishes as the side count diverges. -/
theorem tendsto_angleStep_zero :
    Tendsto angleStep atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (2 * Real.pi) * (n : ℝ)⁻¹) atTop (𝓝 0)
  simpa [inverseScale] using
    (tendsto_const_nhds.mul tendsto_inverseScale_zero :
      Tendsto (fun n : ℕ => (2 * Real.pi) * inverseScale n) atTop (𝓝 ((2 * Real.pi) * 0)))

/-- A radial defect observable for the inscribed regular polygon.
It is the difference between the unit radius and the apothem factor `cos (π/n)`. -/
noncomputable def radialDefect (n : ℕ) : ℝ :=
  1 - Real.cos (Real.pi * inverseScale n)

/-- Gate 3: the radial defect tends to zero, a scalar witness of polygon-to-circle convergence. -/
theorem tendsto_radialDefect_zero :
    Tendsto radialDefect atTop (𝓝 0) := by
  have harg : Tendsto (fun n : ℕ => Real.pi * inverseScale n) atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul tendsto_inverseScale_zero :
        Tendsto (fun n : ℕ => Real.pi * inverseScale n) atTop (𝓝 (Real.pi * 0)))
  have hcos := (Real.continuous_cos.tendsto 0).comp harg
  change Tendsto (fun n : ℕ => Real.cos (Real.pi * inverseScale n)) atTop (𝓝 1) at hcos
  change Tendsto (fun n : ℕ => 1 - Real.cos (Real.pi * inverseScale n)) atTop (𝓝 0)
  simpa using
    (tendsto_const_nhds.sub hcos :
      Tendsto (fun n : ℕ => 1 - Real.cos (Real.pi * inverseScale n)) atTop (𝓝 (1 - 1)))

/-- Gate 4: the local/global invariant. The local step shrinks, but `n` copies still make one turn. -/
theorem local_global_full_turn {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) * (2 * Real.pi * inverseScale n) = 2 * Real.pi := by
  rw [← angleStep_eq_two_pi_mul_inverseScale]
  exact angleStep_full_turn hn

/-- The finite set of exact complex vertices of the regular `n`-gon. -/
noncomputable def vertexSet (n : ℕ) : Set ℂ :=
  Set.range (vertices n)

/-- Every finite polygon vertex set is finite. -/
theorem vertexSet_finite (n : ℕ) : (vertexSet n).Finite := by
  unfold vertexSet
  exact Set.finite_range _

/-- Gate 5: every finite polygon vertex set has Hausdorff dimension zero,
independently of how large the side count is. -/
theorem vertexSet_dimH_zero (n : ℕ) :
    dimH (vertexSet n) = 0 := by
  exact (vertexSet_finite n).dimH_zero

/-- Gate 5: increasing side count does not by itself increase the Hausdorff dimension
of the finite vertex cloud. -/
theorem vertexSet_dimH_eq (m n : ℕ) :
    dimH (vertexSet m) = dimH (vertexSet n) := by
  rw [vertexSet_dimH_zero, vertexSet_dimH_zero]

end NEckLab
