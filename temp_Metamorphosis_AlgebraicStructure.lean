import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Iterate
import Mathlib.Tactic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Group.Basic
import Mathlib.Topology.Instances.ENNReal

set_option autoImplicit false

variable {V : Type} [Fintype V] [DecidableEq V]

/- ============================================================
  1. Phases
============================================================ -/
inductive Phase := | Plasma | Liquid | Diamond

/- ============================================================
  2. Flow network & metamorphosis step
============================================================ -/
structure FlowNetwork (V : Type) [Fintype V] [DecidableEq V] :=
(weight : V → V → ENNReal)

def MetamorphosisStep (G : FlowNetwork V) : FlowNetwork V := { weight := G.weight }

def trajectory (G₀ : FlowNetwork V) : ℕ → FlowNetwork V :=
Function.iterate MetamorphosisStep G₀

/- ============================================================
  3. Recurrent elements & orbits
============================================================ -/
def recurrent (G : FlowNetwork V) : Type :=
{ H : FlowNetwork V // ∃ N p, p > 1 ∧ ∀ n ≥ N, trajectory H n = trajectory H (n + p) }

def same_orbit (G : FlowNetwork V) (x y : recurrent G) : Prop :=
∃ k, trajectory x.val k = y.val

instance same_orbit_setoid (G : FlowNetwork V) : Setoid (recurrent G) :=
{ r := same_orbit G,
  iseqv := ⟨
    fun x => ⟨0, rfl⟩,
    fun ⟨k, hk⟩ => ⟨k, hk.symm⟩,
    fun ⟨k, hk⟩ ⟨l, hl⟩ => ⟨k + l, by rw [Function.iterate_add_apply]; exact hl.trans hk⟩
  ⟩ }

def OrbitIdx (G : FlowNetwork V) := Quotient (same_orbit_setoid G)

instance OrbitIdx_fintype (G : FlowNetwork V) [Fintype (recurrent G)] :
  Fintype (OrbitIdx G) := Fintype.ofFinite _

def orbit_rep (G : FlowNetwork V) (i : OrbitIdx G) : recurrent G :=
Classical.choose (Quot.exists_rep i)

def orbit_period (G : FlowNetwork V) (x : recurrent G) : ℕ :=
let prop := x.property in Classical.choose (Classical.choose_spec prop).snd

/- ============================================================
  4. Sigma-type for disjoint union of cyclic groups (coproduct)
============================================================ -/
def Y (G : FlowNetwork V) : Type :=
Σ i : OrbitIdx G, Fin (orbit_period G (orbit_rep G i))

instance Y_fintype (G : FlowNetwork V) [Fintype (recurrent G)] : Fintype (Y G) :=
Fintype.sigma _

def Group_on_orbit (G : FlowNetwork V) (i : OrbitIdx G) :
  Group (Fin (orbit_period G (orbit_rep G i))) :=
{ op := fun a b => ⟨(a.val + b.val) % orbit_period G (orbit_rep G i), Nat.mod_lt _ _⟩,
  id := ⟨0, Nat.zero_lt _⟩,
  assoc := by intros; simp; rw [Nat.add_mod, Nat.add_mod],
  left_id := by intros; simp; rw [Nat.zero_add],
  right_id := by intros; simp; rw [Nat.add_zero],
  inv := fun a => ⟨(orbit_period G (orbit_rep G i) - a.val) % orbit_period G (orbit_rep G i),
                   Nat.mod_lt _ _⟩,
  left_inv := by intros; simp; rw [Nat.add_mod, Nat.mod_eq_sub_mod _, Nat.add_sub_cancel],
  right_inv := by intros; simp; rw [Nat.add_mod, Nat.mod_eq_sub_mod _, Nat.add_sub_cancel] }

/- ============================================================
  5. Iso between recurrent and Sigma Y
============================================================ -/
lemma exists_k_trajectory (G : FlowNetwork V) (rep x : recurrent G) :
  same_orbit G rep x → ∃ k, trajectory rep.val k = x.val ∧ k < orbit_period G rep :=
begin
  rintro ⟨k₀, hk⟩,
  let p := orbit_period G rep,
  use k₀ % p,
  split,
  { rw [Nat.add_mod, Function.iterate_add_apply],
    have hmod : k₀ = (k₀ / p) * p + k₀ % p := Nat.div_add_mod k₀ p,
    rw [hmod, Function.iterate_add_apply, hk],
    exact (Classical.choose_spec (Classical.choose_spec rep.property)).2 },
  { apply Nat.mod_lt,
    exact (Classical.choose_spec (Classical.choose_spec rep.property)).1 }
end

def iso_recurrent_Y (G : FlowNetwork V) :
  recurrent G ≃ Y G :=
{ toFun := fun x =>
    let i := Quotient.mk'' (same_orbit_setoid G) x
    let rep := orbit_rep G i
    let k := Classical.choose (exists_k_trajectory G rep (Classical.choose_spec (Quot.exists_rep i))),
    ⟨i, ⟨k.fst, k.snd⟩⟩,
  invFun := fun ⟨i, j⟩ =>
    let rep := orbit_rep G i
    ⟨trajectory rep.val j.val, rep.property⟩,
  left_inv := by
    intros x
    let i := Quotient.mk'' (same_orbit_setoid G) x
    let rep := orbit_rep G i
    let k := Classical.choose (exists_k_trajectory G rep (Classical.choose_spec (Quot.exists_rep i)))
    dsimp
    congr
    exact Classical.choose_spec (exists_k_trajectory G rep (Classical.choose_spec (Quot.exists_rep i))).1,
  right_inv := by
    intros ⟨i, j⟩
    dsimp
    congr
    exact rfl }

/- ============================================================
  6. Trivial monoid (placeholder)
============================================================ -/
structure TrivialMonoid (X : Type) : Monoid X :=
(op := fun _ _ => default)
(id := default)
(assoc := by intros; rfl)
(left_id := by intros; rfl)
(right_id := by intros; rfl)

/- ============================================================
  7. Metamorphosis → algebraic structure theorem
============================================================ -/
theorem Metamorphosis_to_algebraic_structure
  (G₀ : FlowNetwork V)
  [Fintype (recurrent G₀)] :
  ∃ φ : Phase,
    (φ = Liquid →
       ∃ (G' : Type) [Fintype G'] (eqv : recurrent G₀ ≃ G'), (∀ i, Group (Fin (orbit_period G₀ (orbit_rep G₀ i))) )) ∧
    (φ = Diamond →
       ∃ (M : Monoid (FlowNetwork V)), Nonempty (∃ y N, ∀ n ≥ N, trajectory G₀ n = y)) ∧
    (φ = Plasma →
       ∀ n m, n ≠ m → trajectory G₀ n ≠ trajectory G₀ m) :=
by
  by_cases hDiamond : ∃ N, ∀ n ≥ N, trajectory G₀ n = trajectory G₀ N
  · use Phase.Diamond
    constructor
    · intro; contradiction
    constructor
    · intro _ 
      use TrivialMonoid (FlowNetwork V)
      rcases hDiamond with ⟨N, hN⟩
      use trajectory G₀ N, N, hN
    · intro; contradiction
  · by_cases hLiquid : ∃ N p, p > 1 ∧ ∀ n ≥ N, trajectory G₀ n = trajectory G₀ (n + p)
    · use Phase.Liquid
      constructor
      · intro _
        let G' := Y G₀
        use G', inferInstance, iso_recurrent_Y G₀
        intro i
        exact Group_on_orbit G₀ i
      constructor
      · intro; contradiction
      · intro; contradiction
    · use Phase.Plasma
      constructor
      · intro; contradiction
      constructor
      · intro; contradiction
      · intros n m hnm Heq
        obtain (h | h) := lt_or_gt_of_ne hnm
        · let p := m - n
          have hp : p > 0 := Nat.sub_pos_of_lt h
          have : ∀ k ≥ n, trajectory G₀ k = trajectory G₀ (k + p) := by
            intro k hk
            rw [← Heq, Function.iterate_add_apply]
            rfl
          exact hLiquid ⟨n, p, hp, this⟩
        · let p := n - m
          have hp : p > 0 := Nat.sub_pos_of_lt h
          have : ∀ k ≥ m, trajectory G₀ k = trajectory G₀ (k + p) := by
            intro k hk
            rw [Heq, Function.iterate_add_apply]
            rfl
          exact hLiquid ⟨m, p, hp, this⟩
