import NEckLab.Foundations
import Mathlib

namespace NEckLab

/-- Cumulative central angle after `k` regular steps in an `n`-gon. -/
noncomputable def centralAngle (n k : ℕ) : ℝ :=
  (k : ℝ) * angleStep n

/-- The `k`-th vertex of a regular `n`-gon on the complex unit circle. -/
noncomputable def vertex (n k : ℕ) : ℂ :=
  Complex.exp (Complex.I * (centralAngle n k : ℂ))

/-- One fixed complex rotation advances a regular `n`-gon by one vertex. -/
noncomputable def rotator (n : ℕ) : ℂ :=
  Complex.exp (Complex.I * (angleStep n : ℂ))

/-- Vertices indexed by `Fin n`, so the index is intrinsically in range. -/
noncomputable def vertices (n : ℕ) : Fin n → ℂ :=
  fun k => vertex n k.1

@[simp] theorem centralAngle_zero (n : ℕ) :
    centralAngle n 0 = 0 := by
  simp [centralAngle]

@[simp] theorem centralAngle_one (n : ℕ) :
    centralAngle n 1 = angleStep n := by
  simp [centralAngle]

@[simp] theorem vertex_zero (n : ℕ) :
    vertex n 0 = 1 := by
  simp [vertex, centralAngle]

/-- Moving to the next vertex adds exactly one angular step. -/
theorem centralAngle_succ (n k : ℕ) :
    centralAngle n (k + 1) = centralAngle n k + angleStep n := by
  simp [centralAngle]
  ring

/-- Successive vertices differ by multiplication with the same complex rotator. -/
theorem vertex_succ (n k : ℕ) :
    vertex n (k + 1) = rotator n * vertex n k := by
  unfold vertex rotator
  rw [centralAngle_succ]
  rw [show Complex.I * ((centralAngle n k + angleStep n : ℝ) : ℂ) =
      Complex.I * (angleStep n : ℂ) + Complex.I * (centralAngle n k : ℂ) by
        push_cast
        ring]
  exact Complex.exp_add _ _

/-- Repeated application of the fixed rotator reconstructs the `k`-th vertex. -/
theorem vertex_eq_rotator_pow (n k : ℕ) :
    vertex n k = rotator n ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_eq_add_one, vertex_succ, ih, pow_succ]
      ring

/-- `n` copies of the reciprocal angle step recover one complete turn. -/
theorem angleStep_full_turn {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) * angleStep n = 2 * Real.pi := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  unfold angleStep
  field_simp [hnR]

/-- After exactly `n` applications, the regular `n`-gon rotator returns to `1`. -/
theorem rotator_pow_sideCount {n : ℕ} (hn : n ≠ 0) :
    rotator n ^ n = 1 := by
  rw [rotator, ← Complex.exp_nat_mul]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [show (n : ℂ) * (Complex.I * (angleStep n : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I by
        unfold angleStep
        push_cast
        field_simp [hnC]
        ring]
  exact Complex.exp_two_pi_mul_I

/-- In particular, the vertex reached after `n` steps is the starting vertex. -/
theorem vertex_sideCount {n : ℕ} (hn : n ≠ 0) :
    vertex n n = 1 := by
  rw [vertex_eq_rotator_pow]
  exact rotator_pow_sideCount hn

/-- Minimal certified data for a regular polygon stage. -/
structure RegularPolygonData where
  n : ℕ
  hpolygon : IsPolygonStage n

noncomputable def vertexMap (P : RegularPolygonData) : Fin P.n → ℂ :=
  vertices P.n

/-- Every certified polygon closes after exactly its side count many rotations. -/
theorem RegularPolygonData.rotator_closes (P : RegularPolygonData) :
    rotator P.n ^ P.n = 1 := by
  exact rotator_pow_sideCount (polygonStage_ne_zero P.hpolygon)

/-- Every certified polygon returns to its initial vertex after one full cycle. -/
theorem RegularPolygonData.vertex_closes (P : RegularPolygonData) :
    vertex P.n P.n = 1 := by
  exact vertex_sideCount (polygonStage_ne_zero P.hpolygon)

def triangle : RegularPolygonData :=
  ⟨3, isPolygonStage_three⟩

def square : RegularPolygonData :=
  ⟨4, by simp [IsPolygonStage]⟩

@[simp] theorem triangle_n : triangle.n = 3 := rfl
@[simp] theorem square_n : square.n = 4 := rfl

theorem triangle_angleStep :
    angleStep triangle.n = 2 * Real.pi / 3 := by
  rfl

theorem square_angleStep :
    angleStep square.n = 2 * Real.pi / 4 := by
  rfl

end NEckLab
