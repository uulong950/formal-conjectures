module

public import Mathlib

@[expose] public section

open Polynomial Finset ENNReal
open scoped Nat

namespace Arxiv.«2602.05192»

variable {F : Type} [Field F]

noncomputable def finiteAdditiveConvolution (n : ℕ) (p q : F[X]) : F[X] :=
  let c := fun k => ∑ ij ∈ antidiagonal (k : ℕ),
      ((n - ij.1)! * (n - ij.2)! : F) / (n ! * (n - k)! : F) *
      p.coeff (n - ij.1) * q.coeff (n - ij.2)
  ∑ k ∈ range (n + 1), c k • X^(n - k)

local notation p " (⊞_"n ")" q:65 => finiteAdditiveConvolution n p q

theorem finiteAdditiveConvolution_degree (n : ℕ) (p q : ℝ[X])
    (hp : p.degree = n) (hq : q.degree = n) :
    (p (⊞_n) q).degree = n := by
  sorry

noncomputable def Φ (p : ℝ[X]) : ℝ≥0∞ :=
  if p.roots.Nodup then
    let roots := p.roots.toFinset
    (∑ i ∈ roots, (∑ j ∈ roots.erase i, 1 / (i - j)) ^ 2).toNNReal
  else
    ⊤

def FourProp (p q : ℝ[X]) (n : ℕ) : Prop :=
    p.degree = n → p.roots.card = n → q.degree = n → q.roots.card = n →
    p.Monic → q.Monic →
    1 / Φ p + 1 / Φ q ≤ 1 / Φ (p (⊞_n) q)

theorem four_2 : ∀ (p q : ℝ[X]), FourProp p q 2 := by
  sorry

theorem four_3 : ∀ (p q : ℝ[X]), FourProp p q 3 := by
  sorry

end Arxiv.«2602.05192»

namespace Arxiv.«1609.08688»

def lt₂ {α : Type*} [LT α] (a b : Fin 3 → α) : Prop :=
  ∃ (i j : Fin 3), i ≠ j ∧ a i < b i ∧ a j < b j

def IsIncreasing₂ {α : Type*} [LT α] (s : List (Fin 3 → α)) : Prop :=
  s.Pairwise lt₂

noncomputable def maximalLength (n : ℕ) : ℕ :=
  sSup { List.length s | (s)
    (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n)
    (_ : IsIncreasing₂ s) }

local notation "F" => maximalLength

theorem maximalLength_ge_of_isSquare {n : ℕ} (h : IsSquare n) :
    n.sqrt ^ 3 ≤ F n := by
  sorry

theorem maximalLength_pow {n : ℕ} {e : ℝ} (hn : 1 < n)
    (h : F n = (n : ℝ) ^ e) :
    ∃ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ e ≤ F m := by
  sorry

theorem maximalLength_pow_eventually {n : ℕ} {e : ℝ} (hn : 1 < n)
    (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e) :
    ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m := by
  sorry

end Arxiv.«1609.08688»

-- Palomar submission entry points
@[expose] public section

namespace Palomar
open Polynomial
open Arxiv.«2602.05192» Arxiv.«1609.08688»
local notation p " (⊞_"n ")" q:65 => Arxiv.«2602.05192».finiteAdditiveConvolution n p q
local notation "F" => Arxiv.«1609.08688».maximalLength

theorem finiteAdditiveConvolution_degree (n : ℕ) (p q : ℝ[X])
    (hp : p.degree = n) (hq : q.degree = n) :
    (p (⊞_n) q).degree = n := by
  sorry

theorem four_2 : ∀ (p q : ℝ[X]), FourProp p q 2 := by
  sorry

theorem four_3 : ∀ (p q : ℝ[X]), FourProp p q 3 := by
  sorry

theorem maximalLength_ge_of_isSquare {n : ℕ} (h : IsSquare n) :
    n.sqrt ^ 3 ≤ F n := by
  sorry

theorem maximalLength_pow {n : ℕ} {e : ℝ} (hn : 1 < n)
    (h : F n = (n : ℝ) ^ e) :
    ∃ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ e ≤ F m := by
  sorry

theorem maximalLength_pow_eventually {n : ℕ} {e : ℝ} (hn : 1 < n)
    (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e) :
    ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m := by
  sorry

end Palomar
