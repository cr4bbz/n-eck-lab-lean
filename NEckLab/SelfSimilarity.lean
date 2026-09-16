import NEckLab.ClosureDimension
import Mathlib.Topology.Continuous

namespace NEckLab

open Topology

/-!
Gate 12: exact self-similar dynamics of the triangle contraction system.

Gate 8 built finite clouds from the three maps

  z ↦ (z + cⱼ) / 2.

Here we prove that these maps really are half-scale similarities and that the finite-stage orbit,
as well as its closure candidate, is forward invariant under every branch of the system.

This deliberately stops short of asserting the full Hutchinson fixed-point equation or the
Hausdorff dimension `log 3 / log 2`; those require a stronger attractor theorem than forward
invariance alone.
-/

/-- Each triangle branch is continuous. -/
theorem triangleContraction_continuous (j : Fin 3) :
    Continuous (triangleContraction j) := by
  unfold triangleContraction
  fun_prop

/-- Gate 12 metric core: every branch scales all distances by exactly one half. -/
theorem triangleContraction_dist (j : Fin 3) (z w : ℂ) :
    dist (triangleContraction j z) (triangleContraction j w) = dist z w / 2 := by
  rw [dist_eq_norm, dist_eq_norm]
  have h :
      triangleContraction j z - triangleContraction j w = (z - w) / 2 := by
    unfold triangleContraction
    ring
  rw [h, norm_div]
  norm_num

/-- Each branch fixes the triangle corner toward which it contracts. -/
theorem triangleContraction_fixed_corner (j : Fin 3) :
    triangleContraction j (triangleCorner j) = triangleCorner j := by
  unfold triangleContraction
  ring

/-- Applying one branch to a point from stage `m` places it in stage `m+1`. -/
theorem triangleContraction_mem_next (j : Fin 3) {m : ℕ} {z : ℂ}
    (hz : z ∈ sierpinskiApprox m) :
    triangleContraction j z ∈ sierpinskiApprox (m + 1) := by
  classical
  have hrefine :
      triangleContraction j z ∈ refineTriangleCloud (sierpinskiApprox m) := by
    unfold refineTriangleCloud
    rw [Finset.mem_biUnion]
    exact ⟨j, Finset.mem_univ _, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  change triangleContraction j z ∈
    sierpinskiApprox m ∪ refineTriangleCloud (sierpinskiApprox m)
  exact Finset.mem_union.mpr (Or.inr hrefine)

/-- The countable finite-stage orbit is forward invariant under every contraction branch. -/
theorem triangleContraction_maps_orbit (j : Fin 3) :
    Set.MapsTo (triangleContraction j) sierpinskiOrbit sierpinskiOrbit := by
  intro z hz
  unfold sierpinskiOrbit at hz ⊢
  rcases Set.mem_iUnion.mp hz with ⟨m, hm⟩
  apply Set.mem_iUnion.mpr
  exact ⟨m + 1, triangleContraction_mem_next j hm⟩

/-- The three-branch set operator associated with the triangle contractions. -/
noncomputable def triangleIFS (s : Set ℂ) : Set ℂ :=
  ⋃ j : Fin 3, triangleContraction j '' s

/-- One IFS step cannot leave the finite-stage orbit. -/
theorem triangleIFS_orbit_subset :
    triangleIFS sierpinskiOrbit ⊆ sierpinskiOrbit := by
  intro z hz
  unfold triangleIFS at hz
  rcases Set.mem_iUnion.mp hz with ⟨j, hj⟩
  rcases hj with ⟨w, hw, rfl⟩
  exact triangleContraction_maps_orbit j hw

/-- Continuity upgrades finite-stage forward invariance to the closure candidate. -/
theorem triangleContraction_maps_candidate (j : Fin 3) :
    Set.MapsTo (triangleContraction j) sierpinskiCandidate sierpinskiCandidate := by
  intro z hz
  unfold sierpinskiCandidate at hz ⊢
  have hzImage :
      triangleContraction j z ∈ triangleContraction j '' closure sierpinskiOrbit :=
    ⟨z, hz, rfl⟩
  have hzClosure :
      triangleContraction j z ∈ closure (triangleContraction j '' sierpinskiOrbit) :=
    image_closure_subset_closure_image (triangleContraction_continuous j) hzImage
  apply (closure_mono ?_) hzClosure
  rintro y ⟨x, hx, rfl⟩
  exact triangleContraction_maps_orbit j hx

/-- Gate 12 structural result: the entire closure candidate is forward invariant under the
three-map IFS. This is one half of the fixed-point equation expected of a true attractor. -/
theorem triangleIFS_candidate_subset :
    triangleIFS sierpinskiCandidate ⊆ sierpinskiCandidate := by
  intro z hz
  unfold triangleIFS at hz
  rcases Set.mem_iUnion.mp hz with ⟨j, hj⟩
  rcases hj with ⟨w, hw, rfl⟩
  exact triangleContraction_maps_candidate j hw

end NEckLab
