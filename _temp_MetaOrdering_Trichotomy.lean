import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Iterate
import Mathlib.Order.Basic
import Mathlib.Tactic

set_option autoImplicit false

/- ============================================================
  1. Base adaptive system (minimal)
============================================================ -/

structure AdaptiveSystem where
  State : Type
  step  : State → State

/- ============================================================
  2. Ordering attempts
============================================================ -/

structure OrderingAttempt (A : AdaptiveSystem) where
  le : A.State → A.State → Prop

/- ============================================================
  3. Meta-system: dynamics on orderings
============================================================ -/

structure MetaOrderingSystem (A : AdaptiveSystem) where
  MetaState : Type
  step : MetaState → MetaState

/-- Iteration notation -/
def iter {X : Type} (f : X → X) : ℕ → X → X := Nat.iterate f
notation f "^[":80 n "]" => iter f n

/- ============================================================
  4. Three meta-phases (orbit-based)
============================================================ -/

/-- Plasma: the orbit is infinite (no repetition ever) -/
def PlasmaPhase {A : AdaptiveSystem} (M : MetaOrderingSystem A) : Prop :=
  ∀ O : M.MetaState, ∀ N : ℕ, ∃ n ≥ N,
    M.step^[n] O ≠ M.step^[N] O

/-- Diamond: eventually fixed point -/
def DiamondPhase {A : AdaptiveSystem} (M : MetaOrderingSystem A) : Prop :=
  ∃ O : M.MetaState, ∃ N : ℕ,
    ∀ n ≥ N, M.step^[n] O = M.step^[N] O

/-- Liquid: eventually periodic with positive period -/
def LiquidPhase {A : AdaptiveSystem} (M : MetaOrderingSystem A) : Prop :=
  ∃ O : M.MetaState, ∃ N p : ℕ,
    p > 0 ∧ ∀ n ≥ N, M.step^[n + p] O = M.step^[n] O

/- ============================================================
  5. Pigeonhole on finite orbits
============================================================ -/

open Nat Finset

lemma eventually_repeats {X : Type} [Fintype X] (f : X → X) (x : X) :
  ∃ i j : ℕ, i < j ∧ f^[i] x = f^[j] x :=
by
  let S := (range (Fintype.card X + 1)).map fun n => f^[n] x
  have : S.toFinset.card ≤ Fintype.card X :=
    Finset.card_le_card (Finset.map_subset _ (subset_univ _))
  have h_lt : (range (Fintype.card X + 1)).card > Fintype.card X :=
    Nat.lt_succ_self _
  obtain ⟨a, -, b, -, hneq, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt S.toFinset h_lt this
  exact ⟨a, b, hneq, heq⟩

/- ============================================================
  6. Meta-ordering trichotomy (finite case)
============================================================ -/

theorem MetaOrdering_Trichotomy_Finite
  {A : AdaptiveSystem}
  (M : MetaOrderingSystem A)
  [Fintype M.MetaState] :
  PlasmaPhase M ∨ LiquidPhase M ∨ DiamondPhase M :=
by
  -- Pick an arbitrary starting meta-state
  let O₀ : M.MetaState := Classical.arbitrary M.MetaState
  
  -- By pigeonhole on finite state space, some repetition must occur
  rcases eventually_repeats M.step O₀ with ⟨i, j, hij, heq⟩
  
  -- The first repetition defines the start of the cycle
  let p := j - i   -- candidate period
  
  -- Helper: applying step p times from iterate i gets back to the same point
  have key : M.step^[p] (M.step^[i] O₀) = M.step^[i] O₀ := by
    rw [← Nat.iterate_add M.step i p O₀]
    congr
    exact (Nat.add_sub_cancel' (le_of_lt hij)).symm ▸ heq
  
  -- Case distinction on whether the cycle has positive length
  by_cases hp : p = 0
  · -- Diamond phase (orbit stabilized)
    right; right
    use O₀, i
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = i + k := Nat.exists_eq_add_of_le hn
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Nat.iterate_succ M.step (i + k) O₀]
        rw [ih]
        rw [← Nat.iterate_succ M.step i O₀]
        congr
        rw [hp] at key
        exact key
  
  · -- Liquid phase (positive period)
    left; right
    use O₀, i, p
    constructor
    · linarith [Nat.pos_of_ne_zero hp]
    · intro n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = i + m := Nat.exists_eq_add_of_le hn
      rw [Nat.iterate_add M.step n p O₀, Nat.iterate_add M.step i (m + p) O₀,
          Nat.iterate_add M.step i m O₀]
      congr
      exact key

/-
  Interpretation:

  In a finite meta-state space, any sequence of ordering updates
  must eventually repeat.

  - Diamond: stabilizes at a fixed point
  - Liquid: cycles with positive period
  - Plasma: impossible in finite space, but appears in infinite state spaces
-/
