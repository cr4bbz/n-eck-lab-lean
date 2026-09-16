import NEckLab.IFSAddress
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.MetricSpace.Contracting

namespace NEckLab

open Set Topology Metric TopologicalSpace
open scoped Topology

noncomputable section

/-!
Gate 13: Hutchinson-style attractor on the Hausdorff hyperspace.

The point-level triangle maps are exact half-scale similarities. Here we lift the three-map
operator to `NonemptyCompacts ℂ`, whose metric is the Hausdorff distance, and prove that the lifted
IFS is itself a strict contraction with factor `1/2`. Banach's fixed-point theorem then gives a
unique nonempty compact fixed point.
-/

private def halfScale : NNReal :=
  ⟨(1 : ℝ) / 2, by norm_num⟩

/-- The triangle IFS sends a nonempty compact set to the union of its three compact images. -/
def triangleCompactIFS (K : NonemptyCompacts ℂ) : NonemptyCompacts ℂ := by
  refine ⟨⟨triangleIFS (K : Set ℂ), ?_⟩, ?_⟩
  · unfold triangleIFS
    exact isCompact_iUnion fun j => K.isCompact.image (triangleContraction_continuous j)
  · rcases K.nonempty with ⟨z, hz⟩
    unfold triangleIFS
    apply Set.mem_iUnion.mpr
    exact ⟨0, ⟨z, hz, rfl⟩⟩

@[simp]
theorem coe_triangleCompactIFS (K : NonemptyCompacts ℂ) :
    (triangleCompactIFS K : Set ℂ) = triangleIFS (K : Set ℂ) := rfl

/-- The lifted triangle IFS contracts Hausdorff distance by at least the same factor `1/2`. -/
theorem triangleCompactIFS_dist_le (K L : NonemptyCompacts ℂ) :
    dist (triangleCompactIFS K) (triangleCompactIFS L) ≤ dist K L / 2 := by
  change hausdorffDist (triangleIFS (K : Set ℂ)) (triangleIFS (L : Set ℂ)) ≤ dist K L / 2
  refine hausdorffDist_le_of_mem_dist (by positivity) ?_ ?_
  · intro x hx
    unfold triangleIFS at hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    rcases hj with ⟨a, ha, rfl⟩
    obtain ⟨b, hb, habest⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty a
    refine ⟨triangleContraction j b, ?_, ?_⟩
    · unfold triangleIFS
      apply Set.mem_iUnion.mpr
      exact ⟨j, ⟨b, hb, rfl⟩⟩
    · rw [triangleContraction_dist]
      have hfin : hausdorffEDist (K : Set ℂ) (L : Set ℂ) ≠ ⊤ :=
        hausdorffEDist_ne_top_of_nonempty_of_bounded
          K.nonempty L.nonempty K.isCompact.isBounded L.isCompact.isBounded
      have hle : infDist a (L : Set ℂ) ≤ dist K L := by
        rw [NonemptyCompacts.dist_eq]
        exact infDist_le_hausdorffDist_of_mem ha hfin
      rw [habest] at hle
      exact div_le_div_of_nonneg_right hle (by norm_num)
  · intro x hx
    unfold triangleIFS at hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    rcases hj with ⟨b, hb, rfl⟩
    obtain ⟨a, ha, hbest⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty b
    refine ⟨triangleContraction j a, ?_, ?_⟩
    · unfold triangleIFS
      apply Set.mem_iUnion.mpr
      exact ⟨j, ⟨a, ha, rfl⟩⟩
    · rw [triangleContraction_dist]
      have hfin : hausdorffEDist (L : Set ℂ) (K : Set ℂ) ≠ ⊤ :=
        hausdorffEDist_ne_top_of_nonempty_of_bounded
          L.nonempty K.nonempty L.isCompact.isBounded K.isCompact.isBounded
      have hle : infDist b (K : Set ℂ) ≤ dist K L := by
        have h' := infDist_le_hausdorffDist_of_mem hb hfin
        rw [← NonemptyCompacts.dist_eq] at h'
        simpa [dist_comm] using h'
      rw [hbest] at hle
      exact div_le_div_of_nonneg_right hle (by norm_num)

/-- The Hausdorff IFS is `1/2`-Lipschitz. -/
theorem triangleCompactIFS_lipschitz :
    LipschitzWith halfScale triangleCompactIFS := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro K L
  have h := triangleCompactIFS_dist_le K L
  change dist (triangleCompactIFS K) (triangleCompactIFS L) ≤
    ((1 : ℝ) / 2) * dist K L
  simpa [div_eq_mul_inv, mul_comm] using h

/-- Hence the Hausdorff IFS is a strict contraction. -/
theorem triangleCompactIFS_contracting :
    ContractingWith halfScale triangleCompactIFS := by
  constructor
  · norm_num [halfScale]
  · exact triangleCompactIFS_lipschitz

/-- Gate 13 existence: there is a nonempty compact fixed point of the three-map IFS. -/
theorem exists_triangleCompactAttractor :
    ∃ F : NonemptyCompacts ℂ, Function.IsFixedPt triangleCompactIFS F := by
  let K₀ : NonemptyCompacts ℂ := {0}
  obtain ⟨F, hF, -, -⟩ :=
    triangleCompactIFS_contracting.exists_fixedPoint K₀ (edist_ne_top _ _)
  exact ⟨F, hF⟩

/-- Gate 13 uniqueness: the compact IFS fixed point is unique. -/
theorem triangleCompactAttractor_unique
    {F G : NonemptyCompacts ℂ}
    (hF : Function.IsFixedPt triangleCompactIFS F)
    (hG : Function.IsFixedPt triangleCompactIFS G) :
    F = G := by
  rcases triangleCompactIFS_contracting.eq_or_edist_eq_top_of_fixedPoints hF hG with h | h
  · exact h
  · exact False.elim ((edist_ne_top F G) h)

/-- The unique fixed point can be selected canonically. -/
def triangleCompactAttractor : NonemptyCompacts ℂ :=
  Classical.choose exists_triangleCompactAttractor

/-- The selected attractor is exactly reconstructed from its three half-scale copies. -/
theorem triangleCompactAttractor_fixed :
    triangleCompactIFS triangleCompactAttractor = triangleCompactAttractor :=
  (Classical.choose_spec exists_triangleCompactAttractor).eq

/-- Set-level form of the Hutchinson fixed-point equation. -/
theorem triangleCompactAttractor_set_fixed :
    triangleIFS (triangleCompactAttractor : Set ℂ) =
      (triangleCompactAttractor : Set ℂ) := by
  have h := congrArg (fun K : NonemptyCompacts ℂ => (K : Set ℂ)) triangleCompactAttractor_fixed
  simpa using h

end

end NEckLab
