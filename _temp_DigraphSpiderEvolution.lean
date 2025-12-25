-- temp_DigraphSpiderEvolution.lean
-- 
-- Purpose: Framework for reasoning about discrete dynamical evolution
--          of weighted digraphs via local spider moves (increase/decrease edges)
--          and their effect on global asymmetry.
--          This is meant as a skeleton for abstract math reasoning; not all proofs
--          or extremal optimizations are fully formalized yet.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic

open Finset BigOperators

-- ===================================
-- Basic digraph definitions
-- ===================================
structure Digraph (V : Type) :=
(weight : V → V → ℝ)
(sym_nonneg : ∀ u v, 0 ≤ weight u v)  -- all weights are non-negative

def out_sum {V : Type} (G : Digraph V) (S : Finset V) (v : V) : ℝ :=
  ∑ w in S, G.weight v w

def in_sum {V : Type} (G : Digraph V) (S : Finset V) (v : V) : ℝ :=
  ∑ u in S, G.weight u v

-- local asymmetry per vertex
def local_asymmetry {V : Type} (G : Digraph V) (S : Finset V) (v : V) : ℝ :=
  let outv := out_sum G S v
      inv  := in_sum G S v
      mean := (outv + inv) / 2
  ((outv - mean)^2 + (inv - mean)^2) / 2

-- global asymmetry over a vertex set
def global_asymmetry {V : Type} (G : Digraph V) (S : Finset V) : ℝ :=
  if h : S.card = 0 then 0 else (∑ v in S, local_asymmetry G S v) / (S.card : ℝ)

-- ===================================
-- Spider moves (increment/decrement edges)
-- ===================================
def increment_edge {V : Type} (G : Digraph V) (u v : V) (Δ : ℝ) (hΔ : 0 ≤ Δ) : Digraph V :=
{ weight := fun x y => if (x = u ∧ y = v) then G.weight x y + Δ else G.weight x y,
  sym_nonneg := by
    intros x y
    if h : x = u ∧ y = v then simp [h]; linarith [G.sym_nonneg x y] else exact G.sym_nonneg x y }

def decrement_edge {V : Type} (G : Digraph V) (u v : V) (Δ : ℝ) (hΔ : 0 ≤ Δ) : Digraph V :=
{ weight := fun x y => if x = u ∧ y = v then max 0 (G.weight x y - Δ) else G.weight x y,
  sym_nonneg := by
    intros x y
    if h : x = u ∧ y = v then simp [h]; apply le_max_left else exact G.sym_nonneg x y }

inductive EdgeUpdate (V : Type)
  | inc (u v : V) (Δ : ℝ) (hΔ : 0 ≤ Δ)
  | dec (u v : V) (Δ : ℝ) (hΔ : 0 ≤ Δ)

def apply_update {V : Type} (G : Digraph V) : EdgeUpdate V → Digraph V
  | .inc u v Δ hΔ => increment_edge G u v Δ hΔ
  | .dec u v Δ hΔ => decrement_edge G u v Δ hΔ

-- ===================================
-- Evolution steps: maximize or minimize global asymmetry
-- ===================================
def spider_step_max {V : Type} (G : Digraph V) (S : Finset V) (candidates : List (EdgeUpdate V)) : Digraph V :=
  candidates.foldl (fun best upd =>
    let candidate := apply_update best upd
    if global_asymmetry candidate S ≥ global_asymmetry best S then candidate else best) G

def spider_step_min {V : Type} (G : Digraph V) (S : Finset V) (candidates : List (EdgeUpdate V)) : Digraph V :=
  candidates.foldl (fun best upd =>
    let candidate := apply_update best upd
    if global_asymmetry candidate S ≤ global_asymmetry best S then candidate else best) G

-- recursive evolution (works with #eval)
def evolve_max (G : Digraph V) (S : Finset V) (candidates : List (EdgeUpdate V)) : ℕ → Digraph V
  | 0     => G
  | n + 1 => evolve_max (spider_step_max G S candidates) S candidates n

def evolve_min (G : Digraph V) (S : Finset V) (candidates : List (EdgeUpdate V)) : ℕ → Digraph V
  | 0     => G
  | n + 1 => evolve_min (spider_step_min G S candidates) S candidates n

-- ===================================
-- Simple property: global asymmetry is non-negative
-- ===================================
lemma global_asymmetry_nonneg {V : Type} (G : Digraph V) (S : Finset V) :
    0 ≤ global_asymmetry G S := by
  unfold global_asymmetry
  split_ifs with h
  · norm_num
  · apply div_nonneg
    · apply sum_nonneg; intro v _; unfold local_asymmetry
      have : (out_sum G S v - (out_sum G S v + in_sum G S v)/2)^2 ≥ 0 := sq_nonneg _
      have : (in_sum G S v - (out_sum G S v + in_sum G S v)/2)^2 ≥ 0 := sq_nonneg _
      linarith
    · exact Nat.cast_nonneg _

-- ===================================
-- temp example: 3-node network evolution
-- ===================================
def Three := Fin 3
instance : DecidableEq Three := inferInstance

def all_vertices : Finset Three := Finset.univ

def G0 : Digraph Three :=
{ weight := fun i j => if i = 0 ∧ j = 1 then 1 else 0,
  sym_nonneg := by intros i j; by_cases h : i = 0 ∧ j = 1 <;> simp [h] <;> norm_num }

def candidates : List (EdgeUpdate Three) :=
[ .inc 0 1 2 (by norm_num),
  .inc 1 2 1 (by norm_num) ]

def G_final := evolve_max G0 all_vertices candidates 5

#eval global_asymmetry G_final all_vertices

-- temp: candidate evolution list is fixed for demonstration; can explore dynamic generation
-- temp: could add proofs about monotonicity, convergence, or phase behavior similar to previous files
