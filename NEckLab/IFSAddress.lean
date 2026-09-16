import NEckLab.SelfSimilarity
import Mathlib.Data.Set.Finite.List

namespace NEckLab

/-!
Gate 12 continuation: symbolic addresses for the triangle IFS.

The cumulative `sierpinskiApprox` construction intentionally retains old points. For exact IFS
dynamics we also need a pure generation model. Finite words over `Fin 3` provide that model:
prepending one symbol corresponds to one new application of the corresponding contraction.
-/

/-- Apply a finite IFS address to a starting point. -/
noncomputable def applyTriangleAddress : List (Fin 3) → ℂ → ℂ
  | [], z => z
  | j :: a, z => triangleContraction j (applyTriangleAddress a z)

@[simp]
theorem applyTriangleAddress_nil (z : ℂ) :
    applyTriangleAddress [] z = z := rfl

@[simp]
theorem applyTriangleAddress_cons (j : Fin 3) (a : List (Fin 3)) (z : ℂ) :
    applyTriangleAddress (j :: a) z =
      triangleContraction j (applyTriangleAddress a z) := rfl

/-- A word of length `m` scales all distances by exactly `2⁻ᵐ`. -/
theorem applyTriangleAddress_dist (a : List (Fin 3)) (z w : ℂ) :
    dist (applyTriangleAddress a z) (applyTriangleAddress a w) =
      dist z w / (2 : ℝ) ^ a.length := by
  induction a with
  | nil => simp
  | cons j a ih =>
      rw [applyTriangleAddress_cons, applyTriangleAddress_cons,
        triangleContraction_dist, ih, List.length_cons, pow_succ]
      ring

/-- The pure generation of depth `m`: exactly the endpoints produced by words of length `m`. -/
noncomputable def triangleWordCloud (m : ℕ) : Set ℂ :=
  {z | ∃ a : List (Fin 3), a.length = m ∧ applyTriangleAddress a 0 = z}

/-- Depth zero contains exactly the chosen seed. -/
theorem triangleWordCloud_zero :
    triangleWordCloud 0 = ({0} : Set ℂ) := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    have : a = [] := List.eq_nil_of_length_eq_zero ha
    subst a
    simp
  · intro hz
    have hz0 : z = 0 := by simpa using hz
    subst z
    exact ⟨[], rfl, rfl⟩

/-- Pure IFS generations satisfy the exact recursion `Gₘ₊₁ = IFS(Gₘ)`. -/
theorem triangleWordCloud_succ (m : ℕ) :
    triangleWordCloud (m + 1) = triangleIFS (triangleWordCloud m) := by
  ext z
  constructor
  · rintro ⟨a, ha, hza⟩
    cases a with
    | nil => simp at ha
    | cons j a =>
        have hlen : a.length = m := by
          simpa using Nat.succ.inj ha
        unfold triangleIFS
        apply Set.mem_iUnion.mpr
        refine ⟨j, ?_⟩
        refine ⟨applyTriangleAddress a 0, ?_, ?_⟩
        · exact ⟨a, hlen, rfl⟩
        · simpa [applyTriangleAddress] using hza
  · intro hz
    unfold triangleIFS at hz
    rcases Set.mem_iUnion.mp hz with ⟨j, hj⟩
    rcases hj with ⟨w, hw, rfl⟩
    rcases hw with ⟨a, ha, rfl⟩
    refine ⟨j :: a, ?_, rfl⟩
    simp [ha]

/-- Every pure generation is finite in the set-theoretic sense. -/
theorem triangleWordCloud_finite (m : ℕ) :
    (triangleWordCloud m).Finite := by
  have hwords : {a : List (Fin 3) | a.length = m}.Finite :=
    List.finite_length_eq (Fin 3) m
  have himage :
      ((fun a : List (Fin 3) => applyTriangleAddress a 0) ''
        {a : List (Fin 3) | a.length = m}).Finite :=
    hwords.image _
  apply himage.subset
  rintro z ⟨a, ha, rfl⟩
  exact ⟨a, ha, rfl⟩

/-- Consequently every exact finite generation still has Hausdorff dimension zero. -/
theorem triangleWordCloud_dimH_zero (m : ℕ) :
    dimH (triangleWordCloud m) = 0 := by
  exact (triangleWordCloud_finite m).countable.dimH_zero

end NEckLab
