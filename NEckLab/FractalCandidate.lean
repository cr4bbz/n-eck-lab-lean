import NEckLab.RegularPolygon
import Mathlib.Topology.MetricSpace.HausdorffDimension

namespace NEckLab

open Topology

/-!
Gate 8: a concrete self-similar candidate built from the three triangle corners.
This file deliberately separates finite approximants from the closure chosen as a limit candidate.
-/

/-- The three exact regular-triangle corners already provided by the polygon model. -/
noncomputable def triangleCorner (j : Fin 3) : ℂ :=
  vertex 3 j.1

/-- Contract a point halfway toward one of the triangle corners. -/
noncomputable def triangleContraction (j : Fin 3) (z : ℂ) : ℂ :=
  (z + triangleCorner j) / 2

/-- One finite self-similar refinement step. -/
noncomputable def refineTriangleCloud (s : Finset ℂ) : Finset ℂ := by
  classical
  exact (Finset.univ : Finset (Fin 3)).biUnion fun j =>
    s.image (triangleContraction j)

/-- Finite approximants. We retain earlier points and add the next contracted generation. -/
noncomputable def sierpinskiApprox : ℕ → Finset ℂ
  | 0 => by
      classical
      exact {0}
  | m + 1 => by
      classical
      exact sierpinskiApprox m ∪ refineTriangleCloud (sierpinskiApprox m)

/-- The approximants are nested. -/
theorem sierpinskiApprox_mono (m : ℕ) :
    (sierpinskiApprox m : Set ℂ) ⊆ sierpinskiApprox (m + 1) := by
  classical
  intro z hz
  simp [sierpinskiApprox, hz]

/-- Every finite approximant still has Hausdorff dimension zero. -/
theorem sierpinskiApprox_dimH_zero (m : ℕ) :
    MeasureTheory.dimH ((sierpinskiApprox m : Finset ℂ) : Set ℂ) = 0 := by
  exact (sierpinskiApprox m).dimH_zero

/-- All points ever produced at a finite refinement depth. -/
noncomputable def sierpinskiOrbit : Set ℂ :=
  ⋃ m : ℕ, ((sierpinskiApprox m : Finset ℂ) : Set ℂ)

/-- A geometric limit candidate: close the countable orbit of all finite refinements. -/
noncomputable def sierpinskiCandidate : Set ℂ :=
  closure sierpinskiOrbit

/-- The countable union of finite stages remains Hausdorff-dimension zero.
Any positive-dimensional behaviour must therefore enter through the closure/limit operation,
not through any single finite stage. -/
theorem sierpinskiOrbit_dimH_zero :
    MeasureTheory.dimH sierpinskiOrbit = 0 := by
  unfold sierpinskiOrbit
  rw [MeasureTheory.dimH_iUnion]
  simp [sierpinskiApprox_dimH_zero]

/-- The finite orbit is contained in its chosen closure candidate. -/
theorem sierpinskiOrbit_subset_candidate :
    sierpinskiOrbit ⊆ sierpinskiCandidate := by
  exact subset_closure

end NEckLab
