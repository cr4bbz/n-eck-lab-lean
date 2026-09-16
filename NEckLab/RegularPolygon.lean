import NEckLab.Foundations
import Mathlib

namespace NEckLab

/-- Cumulative central angle after `k` regular steps in an `n`-gon. -/
noncomputable def centralAngle (n k : ℕ) : ℝ :=
  (k : ℝ) * angleStep n

/-- The `k`-th vertex of a regular `n`-gon on the complex unit circle. -/
noncomputable def vertex (n k : ℕ) : ℂ :=
  Complex.exp (Complex.I * (centralAngle n k : ℂ))

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

/-- Minimal certified data for a regular polygon stage. -/
structure RegularPolygonData where
  n : ℕ
  hpolygon : IsPolygonStage n

noncomputable def vertexMap (P : RegularPolygonData) : Fin P.n → ℂ :=
  vertices P.n

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
