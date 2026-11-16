module

public import FormalConjectures.Arxiv.«2602.05192».FirstProof4
public import FormalConjectures.Arxiv.«1609.08688».sIncreasingrTuples

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
  exact Arxiv.«2602.05192».finiteAdditiveConvolution_degree n p q hp hq

theorem four_2 : ∀ (p q : ℝ[X]), FourProp p q 2 := by
  exact Arxiv.«2602.05192».four_2

theorem four_3 : ∀ (p q : ℝ[X]), FourProp p q 3 := by
  exact Arxiv.«2602.05192».four_3

theorem maximalLength_ge_of_isSquare {n : ℕ} (h : IsSquare n) :
    n.sqrt ^ 3 ≤ F n := by
  exact Arxiv.«1609.08688».maximalLength_ge_of_isSquare h

theorem maximalLength_pow {n : ℕ} {e : ℝ} (hn : 1 < n)
    (h : F n = (n : ℝ) ^ e) :
    ∃ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ e ≤ F m := by
  exact Arxiv.«1609.08688».maximalLength_pow hn h

theorem maximalLength_pow_eventually {n : ℕ} {e : ℝ} (hn : 1 < n)
    (h : F n = (n : ℝ) ^ e) {b : ℝ} (hb : b < e) :
    ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m := by
  exact Arxiv.«1609.08688».maximalLength_pow_eventually hn h hb

end Palomar
