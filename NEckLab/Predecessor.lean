import NEckLab.Foundations

namespace NEckLab

/-!
Gates 6–7: predecessor underdetermination and transition-law classification.
-/

/-- The fiber of all possible predecessors that a transition sends to `y`. -/
def predecessors {α β : Type*} (T : α → β) (y : β) : Set α :=
  {x | T x = y}

/-- Gate 6: if the transition is injective, a target can have at most one predecessor. -/
theorem predecessor_unique_of_injective {α β : Type*}
    {T : α → β} (hT : Function.Injective T) {a b : α} {y : β}
    (ha : T a = y) (hb : T b = y) : a = b := by
  apply hT
  exact ha.trans hb.symm

/-- Injectivity makes every predecessor fiber subsingleton. -/
theorem predecessors_subsingleton_of_injective {α β : Type*}
    {T : α → β} (hT : Function.Injective T) (y : β) :
    (predecessors T y).Subsingleton := by
  intro a ha b hb
  exact predecessor_unique_of_injective hT ha hb

/-- Gate 6: changing stage 2 arbitrarily leaves stage 3 unchanged.
Thus stage 3 alone cannot identify a unique predecessor. -/
theorem stage_three_cannot_identify_stage_two {α : Type*}
    (F : ℕ → Set α) {A B : Set α} (hAB : A ≠ B) :
    replaceStage F 2 A 3 = replaceStage F 2 B 3 ∧
      replaceStage F 2 A 2 ≠ replaceStage F 2 B 2 := by
  constructor
  · simp [replaceStage]
  · simpa [replaceStage] using hAB

/-- A named transition object, kept deliberately more general than polygon geometry. -/
structure TransitionLaw (α β : Type*) where
  toFun : α → β

instance {α β : Type*} : CoeFun (TransitionLaw α β) (fun _ => α → β) :=
  ⟨TransitionLaw.toFun⟩

namespace TransitionLaw

variable {α β γ : Type*}

/-- A transition is information-preserving at the predecessor level when it is injective. -/
def IsRefinementFaithful (T : TransitionLaw α β) : Prop :=
  Function.Injective T

/-- A transition is coarse-graining when distinct fine states can collapse to one coarse state. -/
def IsCoarseGraining (T : TransitionLaw α β) : Prop :=
  ¬ Function.Injective T

/-- Composition of faithful transitions remains faithful. -/
theorem faithful_comp {T : TransitionLaw α β} {U : TransitionLaw β γ}
    (hT : T.IsRefinementFaithful) (hU : U.IsRefinementFaithful) :
    (TransitionLaw.mk (U ∘ T)).IsRefinementFaithful := by
  exact hU.comp hT

/-- Gate 7: a witnessed collision is enough to certify coarse-graining. -/
theorem coarseGraining_of_collision (T : TransitionLaw α β) {a b : α}
    (hab : a ≠ b) (hcollapse : T a = T b) : T.IsCoarseGraining := by
  intro hInjective
  exact hab (hInjective hcollapse)

/-- A left inverse certifies that no predecessor information was lost. -/
theorem faithful_of_leftInverse (T : TransitionLaw α β) (R : β → α)
    (h : Function.LeftInverse R T) : T.IsRefinementFaithful := by
  exact h.injective

end TransitionLaw

end NEckLab
