import NEckLab.ClosureDimension
import Mathlib.Topology.Continuous

namespace NEckLab

open Topology

noncomputable section

/-!
Gate 12: exact self-similar dynamics of the triangle contraction system.

Gate 8 built finite clouds from the three maps

  z ↦ (z + cⱼ) / 2.

Here we prove that these maps really are half-scale similarities and that the finite-stage orbit,
as well as its closure candidate, is forward invariant under every branch of the system.

A key distinction is made explicit: a set may be merely pre-fixed under the IFS operator
(`triangleIFS s ⊆ s`) without being a genuine fixed point (`triangleIFS s = s`). The cumulative
Gate 8 candidate is proved pre-fixed; identifying a genuine attractor remains a stronger target.
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

private def halfNNReal : NNReal :=
  ⟨(1 : ℝ) / 2, by norm_num⟩

/-- The exact half-scale identity packages each branch as a `1/2`-Lipschitz contraction. -/
theorem triangleContraction_lipschitz (j : Fin 3) :
    LipschitzWith halfNNReal (triangleContraction j) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro z w
  rw [triangleContraction_dist]
  change dist z w / 2 ≤ ((1 : ℝ) / 2) * dist z w
  ring_nf
  exact le_rfl

/-- Conversely, no branch collapses distances beyond its exact half-scale factor. -/
theorem triangleContraction_antilipschitz (j : Fin 3) :
    AntilipschitzWith 2 (triangleContraction j) := by
  refine AntilipschitzWith.of_le_mul_dist ?_
  intro z w
  rw [triangleContraction_dist]
  change dist z w ≤ (2 : ℝ) * (dist z w / 2)
  ring_nf
  exact le_rfl

/-- Each contraction branch is globally injective. -/
theorem triangleContraction_injective (j : Fin 3) :
    Function.Injective (triangleContraction j) := by
  exact (triangleContraction_antilipschitz j).injective

/-- Exact similarities preserve Hausdorff dimension even though they shrink metric distances. -/
theorem triangleContraction_dimH_image (j : Fin 3) (s : Set ℂ) :
    dimH (triangleContraction j '' s) = dimH s := by
  apply le_antisymm
  · exact (triangleContraction_lipschitz j).dimH_image_le s
  · exact (triangleContraction_antilipschitz j).le_dimH_image s

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
def triangleIFS (s : Set ℂ) : Set ℂ :=
  ⋃ j : Fin 3, triangleContraction j '' s

/-- A pre-fixed point of the triangle IFS only needs to contain all three contracted copies. -/
def IsTriangleIFSPreFixed (s : Set ℂ) : Prop :=
  triangleIFS s ⊆ s

/-- A genuine fixed point is exactly reconstructed from its three contracted copies. -/
def IsTriangleIFSFixedPoint (s : Set ℂ) : Prop :=
  triangleIFS s = s

/-- Every genuine IFS fixed point is automatically pre-fixed. -/
theorem IsTriangleIFSFixedPoint.preFixed {s : Set ℂ}
    (h : IsTriangleIFSFixedPoint s) : IsTriangleIFSPreFixed s := by
  unfold IsTriangleIFSFixedPoint IsTriangleIFSPreFixed at h ⊢
  rw [h]

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

/-- The existing cumulative closure candidate is therefore formally a pre-fixed point. -/
theorem sierpinskiCandidate_preFixed :
    IsTriangleIFSPreFixed sierpinskiCandidate := by
  exact triangleIFS_candidate_subset

/-- To upgrade the current candidate to a genuine attractor, only the reverse inclusion remains. -/
theorem sierpinskiCandidate_fixedPoint_iff_reverse :
    IsTriangleIFSFixedPoint sierpinskiCandidate ↔
      sierpinskiCandidate ⊆ triangleIFS sierpinskiCandidate := by
  unfold IsTriangleIFSFixedPoint
  constructor
  · intro h
    rw [h]
  · intro h
    exact Set.Subset.antisymm triangleIFS_candidate_subset h

end

end NEckLab
