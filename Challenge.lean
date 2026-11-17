module

public import Mathlib

/-!
# Selected First Proof Q4 and Gowers--Long results

The six compared declarations are the entry points in namespace `Palomar`.
The mathematical account and proof outlines are in the submission section of
the repository-root README. The definitions and theorem statements below
are preserved from the mechanically verified snapshot c148b4b061db036a99efa56422b6fb54e0581334.

For degree-n polynomials p and q, finite additive convolution uses descending
coefficients a_i and b_j and the factorial weights displayed in its definition.
The degree theorem proves deg(p boxplus_n q) = n whenever deg(p) = deg(q) = n;
it needs neither monicity nor real-rootedness.

For a monic real-rooted polynomial with simple roots lambda_i, Phi is
the sum over i of (sum over j != i of 1/(lambda_i-lambda_j))^2.
At a repeated root Phi is infinity, so its reciprocal is zero.
`four_2` and `four_3` prove 1/Phi(p) + 1/Phi(q) <= 1/Phi(p boxplus_n q)
for n = 2 and n = 3, respectively. They include repeated-root cases.
Real-rootedness is expressed by degree n and real root-multiset cardinality n.

A triple a is 2-less than b if a is strictly smaller in at least two
coordinates. A sequence is 2-increasing when this holds for every earlier
and later pair, rather than only adjacent entries. F(n) is its maximum
length with coordinates in {1,...,n}.
The square-size theorem gives F(m^2) >= m^3 for every natural m.
If n > 1 and F(n) = n^e, the first growth theorem gives F(m) >= m^e
for arbitrarily large m. The second gives F(m) >= m^b for all
sufficiently large m, for each real b < e.
These correspond to Gowers--Long Proposition 1.4 (lower bound), Lemma 1.7,
and the paragraph immediately after Lemma 1.7 in arXiv:1609.08688v2.

The implemented proof routes are a direct leading-coefficient argument,
quadratic root-gap identities, a cubic discriminant/sum-of-squares argument,
and explicit sequence constructions with product amplification.
The targets do not invoke the unfinished general `four` theorem.

Prior work includes the Archon general Q4 development and earlier Gowers--Long
proofs by Wentao Li, weiyangzen, and Daniel Puri, with exact source links in
`related_formalizations`. In particular, the square lower bound is already
registered as PALOMAR-2026-11-13-000015 v1. The present contribution is the
specific proof implementation and its relation to these results; mathematical
priority and first-formalization status are not asserted. Archon uses different
definitions of convolution and reciprocal Phi; no Lean bridge between those
definitions and the definitions below has been constructed in this revision.
-/

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
