/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesUtil

/-!
# First Proof, Theorem 4

*Reference:* [arxiv/2602.05192v2](https://arxiv.org/abs/2602.05192v2)
**First Proof**
by *Mohammed Abouzaid, Andrew J. Blumberg, Martin Hairer, Joe Kileel, Tamara G. Kolda, Paul D. Nelson, Daniel Spielman, Nikhil Srivastava, Rachel Ward, Shmuel Weinberger, Lauren Williams*
-/

@[expose] public section

open Polynomial Finset ENNReal
open scoped Nat


namespace Arxiv.«2602.05192»

variable {F : Type} [Field F]

/--
Define $p \boxplus_n q(x)$ to be the polynomial
$$
(p \boxplus_n q)(x) = \sum_{k=0}^n c_k x^{n-k}
$$
where the coefficients $c_k$ are given by the formula:
$$
c_k = \sum_{i+j=k} \frac{(n-i)! (n-j)!}{n! (n-k)!} a_i b_j
$$
for $k = 0, 1, \dots, n$.
 -/
noncomputable def finiteAdditiveConvolution (n : ℕ) (p q : F[X]) : F[X] :=
  let c := fun k => ∑ ij ∈ antidiagonal (k : ℕ),
      ((n - ij.1)! * (n - ij.2)! : F) / (n ! * (n - k)! : F) *
      p.coeff (n - ij.1) * q.coeff (n - ij.2)
  ∑ k ∈ range (n + 1), c k • X^(n - k)

local notation p " (⊞_"n ")" q:65  => finiteAdditiveConvolution n p q

@[category test, AMS 26]
theorem finiteAdditiveConvolution_comm (n : ℕ) (p q : F[X]) :
    p (⊞_n) q = q (⊞_n) p := by
  show ∑ a ∈_, _= ∑ a ∈_, _
  exact sum_congr rfl fun m hm =>
    (congr_arg₂ _) (sum_equiv (.prodComm _ _) (by simp [add_comm]) fun _ _ => by ring!) rfl

@[category test, AMS 26]
theorem finiteAdditiveConvolution_degree (n : ℕ) (p q : ℝ[X])
    (hp : p.degree = n) (hq : q.degree = n) :
    (p (⊞_n) q).degree = n := by
  have hp1 : p.coeff n ≠ 0 := by
    rw [← natDegree_eq_of_degree_eq_some hp, ← Polynomial.leadingCoeff,
      Polynomial.leadingCoeff_ne_zero]
    rintro rfl
    simp at hp
  have hq1 : q.coeff n ≠ 0 := by
    rw [← natDegree_eq_of_degree_eq_some hq, ← Polynomial.leadingCoeff,
      Polynomial.leadingCoeff_ne_zero]
    rintro rfl
    simp at hq
  have hc0 : ∑ ij ∈ antidiagonal 0, ((n - ij.1)! * (n - ij.2)! : ℝ) / (n ! * (n - 0)! : ℝ) *
      p.coeff (n - ij.1) * q.coeff (n - ij.2) ≠ 0 := by
    rw [Finset.Nat.antidiagonal_zero]
    have h_ne : (n ! : ℝ) ≠ 0 := by positivity
    simp [h_ne, hp1, hq1]
  set r := p (⊞_n) q
  have h : r.coeff n ≠ 0 ∧ r.natDegree ≤ n := by
    constructor
    · change (finiteAdditiveConvolution n p q).coeff n ≠ 0
      simp only [finiteAdditiveConvolution]
      rw [Polynomial.finsetSum_coeff]
      conv_lhs =>
        arg 2; ext k
        rw [Polynomial.coeff_smul, Polynomial.coeff_X_pow]
      simp only [smul_eq_mul]
      rw [Finset.sum_eq_single 0]
      · simp only [Nat.sub_zero, ite_true, mul_one]
        exact hc0
      · intro k hk hk0
        have hk_lt : k < n + 1 := Finset.mem_range.mp hk
        have : n ≠ n - k := by omega
        simp [this]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    · change (finiteAdditiveConvolution n p q).natDegree ≤ n
      simp only [finiteAdditiveConvolution]
      apply (Polynomial.natDegree_sum_le _ _).trans
      apply Finset.sup_le
      intro k _
      apply (Polynomial.natDegree_smul_le _ _).trans
      exact (Polynomial.natDegree_X_pow_le (n - k)).trans (Nat.sub_le n k)
  rcases Nat.eq_or_lt_of_le h.2 with heq | hlt
  · rw [Polynomial.degree_eq_natDegree, heq]
    rintro h0
    exact h.1 (by simp [h0])
  · exfalso
    exact h.1 (Polynomial.coeff_eq_zero_of_natDegree_lt hlt)

@[category test, AMS 26]
theorem finiteAdditiveConvolution_monic' (n : ℕ) (p q : ℝ[X]) (hn : 0 < n)
    (hp_deg : p.degree = n) (hq_deg : q.degree = n) (hp_monic : p.Monic) (hq_monic : q.Monic) :
    (p (⊞_n) q).Monic := by
  have hc0 : ∑ ij ∈ antidiagonal 0, ((n - ij.1)! * (n - ij.2)! : ℝ) / (n ! * (n - 0)! : ℝ) *
      p.coeff (n - ij.1) * q.coeff (n - ij.2) = 1 := by
    rw [Finset.Nat.antidiagonal_zero]
    simp
    have hp1 : p.coeff n = 1 := by
      have : p.natDegree = n := natDegree_eq_of_degree_eq_some hp_deg
      rw [← this]
      exact hp_monic
    have hq1 : q.coeff n = 1 := by
      have : q.natDegree = n := natDegree_eq_of_degree_eq_some hq_deg
      rw [← this]
      exact hq_monic
    rw [hp1, hq1]
    have h_ne : (n ! : ℝ) ≠ 0 := by positivity
    simp [h_ne]
  -- The polynomial is ∑ k ∈ range (n+1), c(k) • X^(n-k).
  -- Show coeff n equals 1 (from the k=0 term) and natDegree ≤ n.
  set r := p (⊞_n) q
  suffices h : r.coeff n = 1 ∧ r.natDegree ≤ n by
    rw [Polynomial.Monic, Polynomial.leadingCoeff]
    rcases Nat.eq_or_lt_of_le h.2 with heq | hlt
    · rw [heq]; exact h.1
    · exfalso; rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt] at h; linarith [h.1]
  constructor
  · -- coeff n of (∑ k ∈ range (n+1), c(k) • X^(n-k)) = c(0) = 1
    change (finiteAdditiveConvolution n p q).coeff n = 1
    simp only [finiteAdditiveConvolution]
    rw [Polynomial.finsetSum_coeff]
    conv_lhs =>
      arg 2; ext k
      rw [Polynomial.coeff_smul, Polynomial.coeff_X_pow]
    simp only [smul_eq_mul]
    -- Now: ∑ k ∈ range (n+1), c(k) * if n = n - k then 1 else 0
    -- Only k=0 contributes (since n = n - k ↔ k = 0 for k ≤ n)
    rw [Finset.sum_eq_single 0]
    · -- The k=0 term: simplify n - 0 = n, if-cond = true, then use hc0
      simp only [Nat.sub_zero, ite_true, mul_one]
      exact hc0
    · -- All other terms are 0
      intro k _ hk0
      have : n ≠ n - k := by omega
      simp [this]
    · -- 0 ∈ range (n+1)
      intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · -- natDegree ≤ n: each term has degree ≤ n since n - k ≤ n
    change (finiteAdditiveConvolution n p q).natDegree ≤ n
    simp only [finiteAdditiveConvolution]
    apply (Polynomial.natDegree_sum_le _ _).trans
    apply Finset.sup_le
    intro k hk
    apply (Polynomial.natDegree_smul_le _ _).trans
    exact (Polynomial.natDegree_X_pow_le (n - k)).trans (Nat.sub_le n k)

/--
For a monic polynomial $p(x)=\prod_{i\le n}(x- \lambda_i)$, define
$$\Phi_n(p):=\sum_{i\le n}(\sum_{j\neq i} \frac1{\lambda_i-\lambda_j})^2$$
and $\Phi_n(p):=\infty$ if $p$ has a multiple root.
-/
noncomputable def Φ (p : ℝ[X]) : ℝ≥0∞ :=
  if p.roots.Nodup then
    let roots := p.roots.toFinset
    (∑ i ∈ roots, (∑ j ∈ roots.erase i, 1 / (i - j)) ^ 2).toNNReal
  else
    ⊤

/--
A predicate that holds if $p(x)$ and $q(x)$ are monic real-rooted polynomials of
degree $n$, then
$$\frac{1}{\Phi_n(p\boxplus_n q)} \ge \frac{1}{\Phi_n(p)}+\frac{1}{\Phi_n(q)}?$$
-/
def FourProp (p q : ℝ[X]) (n : ℕ) : Prop :=
    p.degree = n → p.roots.card = n → q.degree = n  → q.roots.card = n → p.Monic → q.Monic →
    1 / Φ p + 1 / Φ q ≤ 1 / Φ (p (⊞_n) q)

set_option linter.style.formal_proof_palomar false in
/--
Is it true that if $p(x)$ and $q(x)$ are monic real-rooted polynomials of
degree $n$, then
$$\frac{1}{\Phi_n(p\boxplus_n q)} \ge \frac{1}{\Phi_n(p)}+\frac{1}{\Phi_n(q)}?$$

[arxiv/2602.05192v2](https://arxiv.org/abs/2602.05192v2) contains a proof.
-/
@[category research solved, question, AMS 26, formal_proof using lean4 at
"https://github.com/frenzymath/Archon-FirstProof-Results/blob/main/FirstProof/FirstProof4/Problem4.lean"]
theorem four : ∀ (p q : ℝ[X]) (n : ℕ), FourProp p q n := by
  sorry

private lemma mul_X_sub_C_Expanded (a b : ℝ) :
    (X - C a) * (X - C b) = X ^ 2 - C (a + b) * X + C (a * b) := by
  simp only [map_add, map_mul]; ring

private lemma mul_X_sub_C_coeffs (a b : ℝ) :
    ((X - C a) * (X - C b)).coeff 2 = 1 ∧
    ((X - C a) * (X - C b)).coeff 1 = -(a + b) ∧
    ((X - C a) * (X - C b)).coeff 0 = a * b := by
  rw [mul_X_sub_C_Expanded]
  refine ⟨?_, ?_, ?_⟩ <;> simp [coeff_X_pow, coeff_X, coeff_C]

private lemma eq_mul_X_sub_C_of_degree_two (p : ℝ[X]) (hp_deg : p.degree = (2 : ℕ))
    (hp_roots : p.roots.card = 2) (hp_monic : p.Monic) :
    ∃ a b : ℝ, p = (X - C a) * (X - C b) := by
  have hnat : p.natDegree = 2 := natDegree_eq_of_degree_eq_some hp_deg
  have hprod := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (hp_roots.trans hnat.symm)
  rw [hp_monic.leadingCoeff, map_one, one_mul] at hprod
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hp_roots
  exact ⟨a, b, by rw [← hprod, hab]; simp⟩

private lemma finiteAdditiveConvolution_two_mul_X_sub_C (a b c d μ Δ : ℝ)
    (hμ : μ = (a + b + c + d) / 2)
    (hΔ : Δ = Real.sqrt ((a - b) ^ 2 + (c - d) ^ 2) / 2) :
    ((X - C a) * (X - C b)) (⊞_2) ((X - C c) * (X - C d)) =
      (X - C (μ + Δ)) * (X - C (μ - Δ)) := by
  obtain ⟨hp2, hp1, hp0⟩ := mul_X_sub_C_coeffs a b
  obtain ⟨hq2, hq1, hq0⟩ := mul_X_sub_C_coeffs c d
  set p := (X - C a) * (X - C b)
  set q := (X - C c) * (X - C d)
  have hΔ2 : Δ ^ 2 = ((a - b) ^ 2 + (c - d) ^ 2) / 4 := by
    rw [hΔ, div_pow, Real.sq_sqrt (by positivity)]; norm_num
  have hc0 : (∑ ij ∈ antidiagonal 0,
      ((2 - ij.1)! * (2 - ij.2)! : ℝ) / (2! * (2 - 0)! : ℝ) *
      p.coeff (2 - ij.1) * q.coeff (2 - ij.2)) = 1 := by
    rw [show antidiagonal 0 = {(0, 0)} from rfl, Finset.sum_singleton]
    simp only [Nat.sub_zero, hp2, hq2]; norm_num
  have hc1 : (∑ ij ∈ antidiagonal 1,
      ((2 - ij.1)! * (2 - ij.2)! : ℝ) / (2! * (2 - 1)! : ℝ) *
      p.coeff (2 - ij.1) * q.coeff (2 - ij.2)) = -((μ + Δ) + (μ - Δ)) := by
    rw [show antidiagonal 1 = {(0, 1), (1, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [Nat.reduceSub, Nat.factorial, hp2, hp1, hq2, hq1, hμ]; ring
  have hc2 : (∑ ij ∈ antidiagonal 2,
      ((2 - ij.1)! * (2 - ij.2)! : ℝ) / (2! * (2 - 2)! : ℝ) *
      p.coeff (2 - ij.1) * q.coeff (2 - ij.2)) = (μ + Δ) * (μ - Δ) := by
    rw [show antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [Nat.reduceSub, Nat.factorial, hp2, hp1, hp0, hq2, hq1, hq0]
    calc _ = ((a + b + c + d) / 2) ^ 2 - ((a - b) ^ 2 + (c - d) ^ 2) / 4 := by ring
      _ = (μ + Δ) * (μ - Δ) := by rw [← hμ, ← hΔ2]; ring
  unfold finiteAdditiveConvolution
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  dsimp only
  rw [hc0, hc1, hc2, mul_X_sub_C_Expanded (μ + Δ) (μ - Δ)]
  simp only [Nat.reduceSub, pow_zero, pow_one, Polynomial.smul_eq_C_mul, map_one, map_neg]
  ring

private lemma one_div_Phi_mul_X_sub_C (a b : ℝ) :
    1 / Φ ((X - C a) * (X - C b)) = ENNReal.ofReal ((a - b) ^ 2 / 2) := by
  unfold Φ
  have h_ne : (X - C a) * (X - C b) ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)
  have h_roots : ((X - C a) * (X - C b)).roots = a ::ₘ {b} := by
    rw [roots_mul h_ne, roots_X_sub_C, roots_X_sub_C]; rfl
  rw [h_roots]
  by_cases hab : a = b
  · subst hab
    rw [if_neg (by simp)]
    simp
  · rw [if_pos (by simp [hab])]
    dsimp only
    have h_finset : (a ::ₘ ({b} : Multiset ℝ)).toFinset = insert a {b} := by simp
    have h_erase_a : (insert a ({b} : Finset ℝ)).erase a = {b} :=
      Finset.erase_insert (by simp [hab])
    have h_erase_b : (insert a ({b} : Finset ℝ)).erase b = {a} := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hxb, rfl | rfl⟩
        · rfl
        · contradiction
      · rintro rfl
        exact ⟨hab, Or.inl rfl⟩
    have h_sum_val : (∑ i ∈ (a ::ₘ ({b} : Multiset ℝ)).toFinset,
        (∑ j ∈ (a ::ₘ ({b} : Multiset ℝ)).toFinset.erase i, 1 / (i - j)) ^ 2) =
        2 / (a - b) ^ 2 := by
      rw [h_finset, Finset.sum_insert (by simp [hab]), Finset.sum_singleton,
        h_erase_a, h_erase_b, Finset.sum_singleton, Finset.sum_singleton,
        show b - a = -(a - b) by ring, div_neg, neg_sq, div_pow, one_pow,
        ← add_div, one_add_one_eq_two]
    rw [h_sum_val]
    change 1 / ENNReal.ofReal (2 / (a - b) ^ 2) = ENNReal.ofReal ((a - b) ^ 2 / 2)
    have h_pos : 0 < 2 / (a - b) ^ 2 := by
      have : a - b ≠ 0 := sub_ne_zero.mpr hab
      positivity
    rw [one_div, ← ENNReal.ofReal_inv_of_pos h_pos, inv_div]

/--
Is it true that if $p(x)$ and $q(x)$ are monic real-rooted polynomials of
degree $2$, then
$$\frac{1}{\Phi_2(p\boxplus_n q)} \ge \frac{1}{\Phi_2(p)}+\frac{1}{\Phi_2(q)}?$$
-/
@[category research solved, question, AMS 26]
theorem four_2 : ∀ (p q : ℝ[X]), FourProp p q 2 := by
  intro p q hp_deg hp_roots hq_deg hq_roots hp_monic hq_monic
  obtain ⟨a, b, rfl⟩ := eq_mul_X_sub_C_of_degree_two p hp_deg hp_roots hp_monic
  obtain ⟨c, d, rfl⟩ := eq_mul_X_sub_C_of_degree_two q hq_deg hq_roots hq_monic
  set μ := (a + b + c + d) / 2
  set Δ := Real.sqrt ((a - b) ^ 2 + (c - d) ^ 2) / 2
  rw [finiteAdditiveConvolution_two_mul_X_sub_C a b c d μ Δ rfl rfl,
    one_div_Phi_mul_X_sub_C a b, one_div_Phi_mul_X_sub_C c d, one_div_Phi_mul_X_sub_C,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [show (μ + Δ) - (μ - Δ) = Real.sqrt ((a - b) ^ 2 + (c - d) ^ 2) by dsimp [Δ]; ring,
    Real.sq_sqrt (by positivity)]
  linarith

private noncomputable def cubicS (a b c : ℝ) : ℝ :=
  ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 6

private noncomputable def cubicT (a b c : ℝ) : ℝ :=
  let μ := (a + b + c) / 3
  (a - μ) * (b - μ) * (c - μ)

private lemma cubicS_nonneg (a b c : ℝ) : 0 ≤ cubicS a b c := by
  unfold cubicS; positivity

private lemma cubic_disc_eq (a b c : ℝ) :
    4 * (cubicS a b c) ^ 3 - 27 * (cubicT a b c) ^ 2 =
      ((a - b) * (b - c) * (c - a)) ^ 2 := by
  unfold cubicS cubicT; ring

private lemma cubic_disc_nonneg (a b c : ℝ) :
    0 ≤ 4 * (cubicS a b c) ^ 3 - 27 * (cubicT a b c) ^ 2 := by
  rw [cubic_disc_eq]; positivity

private lemma multiset_card_eq_three {s : Multiset ℝ} (hs : s.card = 3) :
    ∃ a b c : ℝ, s = a ::ₘ b ::ₘ {c} := by
  induction s using Multiset.induction_on with
  | empty => simp at hs
  | cons a s _ =>
    simp only [Multiset.card_cons, Nat.succ.injEq] at hs
    obtain ⟨b, c, rfl⟩ := Multiset.card_eq_two.mp hs
    exact ⟨a, b, c, rfl⟩

private lemma eq_mul_X_sub_C_of_degree_three (p : ℝ[X]) (hp_deg : p.degree = (3 : ℕ))
    (hp_roots : p.roots.card = 3) (hp_monic : p.Monic) :
    ∃ a b c : ℝ, p = (X - C a) * (X - C b) * (X - C c) := by
  have hnat : p.natDegree = 3 := natDegree_eq_of_degree_eq_some hp_deg
  have hprod := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (hp_roots.trans hnat.symm)
  rw [hp_monic.leadingCoeff, map_one, one_mul] at hprod
  obtain ⟨a, b, c, habc⟩ := multiset_card_eq_three hp_roots
  exact ⟨a, b, c, by rw [← hprod, habc]; simp; ring⟩

private lemma vieta_cardano_exists_roots (s t : ℝ) (hs : 0 ≤ s)
    (hdisc : 0 ≤ 4 * s ^ 3 - 27 * t ^ 2) :
    ∃ u₁ u₂ u₃ : ℝ,
      u₁ + u₂ + u₃ = 0 ∧
      cubicS u₁ u₂ u₃ = s ∧
      cubicT u₁ u₂ u₃ = t := by
  by_cases hs0 : s = 0
  · subst hs0
    have ht2 : t ^ 2 ≤ 0 := by linarith
    have ht0 : t = 0 := sq_eq_zero_iff.mp (le_antisymm ht2 (sq_nonneg t))
    subst ht0
    refine ⟨0, 0, 0, by ring, ?_, ?_⟩
    · unfold cubicS; ring
    · unfold cubicT; ring
  · have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    set R := Real.sqrt (s / 3)
    have hR2 : R ^ 2 = s / 3 := Real.sq_sqrt (by positivity)
    have hR_pos : 0 < R := Real.sqrt_pos.mpr (by positivity)
    have hR3_pos : 0 < 2 * R ^ 3 := by positivity
    have h_arg_sq : t ^ 2 ≤ (2 * R ^ 3) ^ 2 := by
      have : (2 * R ^ 3) ^ 2 = 4 * (R ^ 2) ^ 3 := by ring
      rw [this, hR2]; linarith
    have hx_sq : (t / (2 * R ^ 3)) ^ 2 ≤ 1 := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      linarith
    have hx_lo : -1 ≤ t / (2 * R ^ 3) := by
      nlinarith [sq_nonneg (t / (2 * R ^ 3) + 1), hx_sq]
    have hx_hi : t / (2 * R ^ 3) ≤ 1 := by
      nlinarith [sq_nonneg (t / (2 * R ^ 3) - 1), hx_sq]
    set θ := Real.arccos (t / (2 * R ^ 3)) / 3
    set c := Real.cos θ
    set sθ := Real.sin θ
    have hcs : c ^ 2 + sθ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
    have hc3 : 4 * c ^ 3 - 3 * c = t / (2 * R ^ 3) := by
      have h3θ : 3 * θ = Real.arccos (t / (2 * R ^ 3)) := by dsimp [θ]; ring
      rw [← Real.cos_three_mul, h3θ, Real.cos_arccos hx_lo hx_hi]
    have hR3_ne : 2 * R ^ 3 ≠ 0 := ne_of_gt hR3_pos
    have ht_eq : 2 * R ^ 3 * (4 * c ^ 3 - 3 * c) = t := by
      rw [hc3, mul_div_cancel₀ _ hR3_ne]
    refine ⟨2 * R * c, R * (-c + Real.sqrt 3 * sθ), R * (-c - Real.sqrt 3 * sθ), by ring, ?_, ?_⟩
    · unfold cubicS
      calc _ = 3 * R ^ 2 * (c ^ 2 + sθ ^ 2) := by
            have : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by positivity)
            linear_combination (R ^ 2 * sθ ^ 2) * this
        _ = s := by rw [hcs, mul_one, hR2]; ring
    · unfold cubicT
      calc _ = 2 * R ^ 3 * (c ^ 3 - 3 * c * sθ ^ 2) := by
            have : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by positivity)
            linear_combination (-2 * R ^ 3 * c * sθ ^ 2) * this
        _ = 2 * R ^ 3 * (4 * c ^ 3 - 3 * c * (c ^ 2 + sθ ^ 2)) := by ring
        _ = t := by rw [hcs, mul_one, ht_eq]

private lemma cubic_stam_sos (sp tp sq tq : ℝ)
    (hsp : 0 ≤ sp) (hsq : 0 ≤ sq)
    (hdp : 0 ≤ 4 * sp ^ 3 - 27 * tp ^ 2)
    (hdq : 0 ≤ 4 * sq ^ 3 - 27 * tq ^ 2) :
    (4 * sp ^ 3 - 27 * tp ^ 2) / (18 * sp ^ 2) +
    (4 * sq ^ 3 - 27 * tq ^ 2) / (18 * sq ^ 2) ≤
    (4 * (sp + sq) ^ 3 - 27 * (tp + tq) ^ 2) / (18 * (sp + sq) ^ 2) := by
  by_cases hsp0 : sp = 0
  · subst hsp0
    have htp2 : tp ^ 2 ≤ 0 := by linarith
    have htp0 : tp = 0 := sq_eq_zero_iff.mp (le_antisymm htp2 (sq_nonneg tp))
    subst htp0
    simp
  · by_cases hsq0 : sq = 0
    · subst hsq0
      have htq2 : tq ^ 2 ≤ 0 := by linarith
      have htq0 : tq = 0 := sq_eq_zero_iff.mp (le_antisymm htq2 (sq_nonneg tq))
      subst htq0
      simp
    · have hsp_pos : 0 < sp := lt_of_le_of_ne hsp (Ne.symm hsp0)
      have hsq_pos : 0 < sq := lt_of_le_of_ne hsq (Ne.symm hsq0)
      have h_rhs_nonneg : 0 ≤ 3 * ((tp * sq ^ 2 - tq * sp ^ 2) ^ 2 +
          2 * sp * sq * (tp ^ 2 * sq ^ 2 + tq ^ 2 * sp ^ 2)) /
          (2 * sp ^ 2 * sq ^ 2 * (sp + sq) ^ 2) := by positivity
      have h_diff : (4 * (sp + sq) ^ 3 - 27 * (tp + tq) ^ 2) / (18 * (sp + sq) ^ 2) -
          ((4 * sp ^ 3 - 27 * tp ^ 2) / (18 * sp ^ 2) +
           (4 * sq ^ 3 - 27 * tq ^ 2) / (18 * sq ^ 2)) =
          3 * ((tp * sq ^ 2 - tq * sp ^ 2) ^ 2 +
            2 * sp * sq * (tp ^ 2 * sq ^ 2 + tq ^ 2 * sp ^ 2)) /
          (2 * sp ^ 2 * sq ^ 2 * (sp + sq) ^ 2) := by
        field_simp
        ring
      linarith

private lemma mul_X_sub_C_three_Expanded (a b c : ℝ) :
    (X - C a) * (X - C b) * (X - C c) =
      X ^ 3 - C (a + b + c) * X ^ 2 + C (a * b + b * c + c * a) * X - C (a * b * c) := by
  simp only [map_add, map_mul]; ring

private lemma mul_X_sub_C_three_coeffs (a b c : ℝ) :
    ((X - C a) * (X - C b) * (X - C c)).coeff 3 = 1 ∧
    ((X - C a) * (X - C b) * (X - C c)).coeff 2 = -(a + b + c) ∧
    ((X - C a) * (X - C b) * (X - C c)).coeff 1 = a * b + b * c + c * a ∧
    ((X - C a) * (X - C b) * (X - C c)).coeff 0 = -(a * b * c) := by
  rw [mul_X_sub_C_three_Expanded]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    { simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]; norm_num }

private lemma finiteAdditiveConvolution_three_mul_X_sub_C
    (a₁ a₂ a₃ b₁ b₂ b₃ r₁ r₂ r₃ : ℝ)
    (hr1 : r₁ + r₂ + r₃ = (a₁ + a₂ + a₃) + (b₁ + b₂ + b₃))
    (hrs : cubicS r₁ r₂ r₃ = cubicS a₁ a₂ a₃ + cubicS b₁ b₂ b₃)
    (hrt : cubicT r₁ r₂ r₃ = cubicT a₁ a₂ a₃ + cubicT b₁ b₂ b₃) :
    ((X - C a₁) * (X - C a₂) * (X - C a₃)) (⊞_3) ((X - C b₁) * (X - C b₂) * (X - C b₃)) =
      (X - C r₁) * (X - C r₂) * (X - C r₃) := by
  obtain ⟨hp3, hp2, hp1, hp0⟩ := mul_X_sub_C_three_coeffs a₁ a₂ a₃
  obtain ⟨hq3, hq2, hq1, hq0⟩ := mul_X_sub_C_three_coeffs b₁ b₂ b₃
  set p := (X - C a₁) * (X - C a₂) * (X - C a₃)
  set q := (X - C b₁) * (X - C b₂) * (X - C b₃)
  have esymm2 (x y z : ℝ) :
      x * y + y * z + z * x = (x + y + z) ^ 2 / 3 - cubicS x y z := by
    unfold cubicS; ring
  have esymm3 (x y z : ℝ) :
      x * y * z = (x + y + z) ^ 3 / 27 - (x + y + z) * cubicS x y z / 3 + cubicT x y z := by
    unfold cubicS cubicT; ring
  have hc0 : (∑ ij ∈ antidiagonal 0,
      ((3 - ij.1)! * (3 - ij.2)! : ℝ) / (3! * (3 - 0)! : ℝ) *
      p.coeff (3 - ij.1) * q.coeff (3 - ij.2)) = 1 := by
    rw [show antidiagonal 0 = {(0, 0)} from rfl, Finset.sum_singleton]
    simp only [Nat.sub_zero, hp3, hq3]; norm_num
  have hc1 : (∑ ij ∈ antidiagonal 1,
      ((3 - ij.1)! * (3 - ij.2)! : ℝ) / (3! * (3 - 1)! : ℝ) *
      p.coeff (3 - ij.1) * q.coeff (3 - ij.2)) = -(r₁ + r₂ + r₃) := by
    rw [show antidiagonal 1 = {(0, 1), (1, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [Nat.reduceSub, Nat.factorial, hp3, hp2, hq3, hq2, hr1]; ring
  have hc2 : (∑ ij ∈ antidiagonal 2,
      ((3 - ij.1)! * (3 - ij.2)! : ℝ) / (3! * (3 - 2)! : ℝ) *
      p.coeff (3 - ij.1) * q.coeff (3 - ij.2)) = r₁ * r₂ + r₂ * r₃ + r₃ * r₁ := by
    rw [show antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [Nat.reduceSub, Nat.factorial, hp3, hp2, hp1, hq3, hq2, hq1]
    rw [esymm2 r₁ r₂ r₃, hr1, hrs]
    unfold cubicS; ring
  have hc3 : (∑ ij ∈ antidiagonal 3,
      ((3 - ij.1)! * (3 - ij.2)! : ℝ) / (3! * (3 - 3)! : ℝ) *
      p.coeff (3 - ij.1) * q.coeff (3 - ij.2)) = -(r₁ * r₂ * r₃) := by
    rw [show antidiagonal 3 = {(0, 3), (1, 2), (2, 1), (3, 0)} from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [Nat.reduceSub, Nat.factorial, hp3, hp2, hp1, hp0, hq3, hq2, hq1, hq0]
    rw [esymm3 r₁ r₂ r₃, hr1, hrs, hrt]
    unfold cubicS cubicT; ring
  unfold finiteAdditiveConvolution
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  dsimp only
  rw [hc0, hc1, hc2, hc3, mul_X_sub_C_three_Expanded r₁ r₂ r₃]
  simp only [Nat.reduceSub, pow_zero, pow_one, Polynomial.smul_eq_C_mul, map_one, map_neg]
  ring

private lemma one_div_Phi_cubic (a b c : ℝ) :
    1 / Φ ((X - C a) * (X - C b) * (X - C c)) =
      ENNReal.ofReal ((4 * (cubicS a b c) ^ 3 - 27 * (cubicT a b c) ^ 2) /
        (18 * (cubicS a b c) ^ 2)) := by
  unfold Φ
  have h_ne12 : (X - C a) * (X - C b) ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero a) (X_sub_C_ne_zero b)
  have h_ne : (X - C a) * (X - C b) * (X - C c) ≠ 0 :=
    mul_ne_zero h_ne12 (X_sub_C_ne_zero c)
  have h_roots : ((X - C a) * (X - C b) * (X - C c)).roots = a ::ₘ b ::ₘ {c} := by
    rw [roots_mul h_ne, roots_mul h_ne12, roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]; rfl
  rw [h_roots]
  by_cases h_nodup : (a ::ₘ b ::ₘ ({c} : Multiset ℝ)).Nodup
  · rw [if_pos h_nodup]
    dsimp only
    have h_nodup' := h_nodup
    simp only [Multiset.nodup_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or,
      Multiset.nodup_singleton, and_true] at h_nodup'
    obtain ⟨⟨hab, hac⟩, hbc⟩ := h_nodup'
    have h_finset : (a ::ₘ b ::ₘ ({c} : Multiset ℝ)).toFinset = insert a (insert b {c}) := by simp
    have h_mem_a : a ∉ insert b ({c} : Finset ℝ) := by simp [hab, hac]
    have h_mem_b : b ∉ ({c} : Finset ℝ) := by simp [hbc]
    have h_erase_a : (insert a (insert b ({c} : Finset ℝ))).erase a = insert b {c} :=
      Finset.erase_insert h_mem_a
    have h_erase_b : (insert a (insert b ({c} : Finset ℝ))).erase b = insert a {c} := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hxb, rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · contradiction
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨hab, Or.inl rfl⟩
        · exact ⟨Ne.symm hbc, Or.inr (Or.inr rfl)⟩
    have h_erase_c : (insert a (insert b ({c} : Finset ℝ))).erase c = insert a {b} := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hxc, rfl | rfl | rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · contradiction
      · rintro (rfl | rfl)
        · exact ⟨hac, Or.inl rfl⟩
        · exact ⟨hbc, Or.inr (Or.inl rfl)⟩
    have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hac' : a - c ≠ 0 := sub_ne_zero.mpr hac
    have hbc' : b - c ≠ 0 := sub_ne_zero.mpr hbc
    have hba' : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have hca' : c - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hac)
    have hcb' : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
    have h_sum_val : (∑ i ∈ (a ::ₘ b ::ₘ ({c} : Multiset ℝ)).toFinset,
        (∑ j ∈ (a ::ₘ b ::ₘ ({c} : Multiset ℝ)).toFinset.erase i, 1 / (i - j)) ^ 2) =
        18 * (cubicS a b c) ^ 2 / (4 * (cubicS a b c) ^ 3 - 27 * (cubicT a b c) ^ 2) := by
      rw [h_finset, Finset.sum_insert h_mem_a, Finset.sum_insert h_mem_b, Finset.sum_singleton,
        h_erase_a, h_erase_b, h_erase_c,
        Finset.sum_insert h_mem_b, Finset.sum_singleton,
        Finset.sum_insert (by simp [hac]), Finset.sum_singleton,
        Finset.sum_insert (by simp [hab]), Finset.sum_singleton,
        cubic_disc_eq]
      unfold cubicS
      field_simp
      ring
    rw [h_sum_val]
    change 1 / ENNReal.ofReal (18 * (cubicS a b c) ^ 2 /
      (4 * (cubicS a b c) ^ 3 - 27 * (cubicT a b c) ^ 2)) = _
    have hs_pos : 0 < cubicS a b c := by
      unfold cubicS
      have : 0 < (a - b) ^ 2 := sq_pos_of_ne_zero hab'
      positivity
    have hdisc_pos : 0 < 4 * (cubicS a b c) ^ 3 - 27 * (cubicT a b c) ^ 2 := by
      rw [cubic_disc_eq]; positivity
    have h_pos : 0 < 18 * (cubicS a b c) ^ 2 /
        (4 * (cubicS a b c) ^ 3 - 27 * (cubicT a b c) ^ 2) := by positivity
    rw [one_div, ← ENNReal.ofReal_inv_of_pos h_pos, inv_div]
  · have h_deg : a = b ∨ b = c ∨ c = a := by
      by_contra! h
      exact h_nodup (by simp [h.1, h.2.1, Ne.symm h.2.2])
    have h_disc0 : 4 * (cubicS a b c) ^ 3 - 27 * (cubicT a b c) ^ 2 = 0 := by
      rw [cubic_disc_eq]
      rcases h_deg with rfl | rfl | rfl <;> ring
    rw [if_neg h_nodup, h_disc0, zero_div, ENNReal.ofReal_zero]
    simp

/--
Is it true that if $p(x)$ and $q(x)$ are monic real-rooted polynomials of
degree $3$, then
$$\frac{1}{\Phi_3(p\boxplus_n q)} \ge \frac{1}{\Phi_3(p)}+\frac{1}{\Phi_3(q)}?$$
-/
@[category research solved, question, AMS 26]
theorem four_3 : ∀ (p q : ℝ[X]), FourProp p q 3 := by
  intro p q hp_deg hp_roots hq_deg hq_roots hp_monic hq_monic
  obtain ⟨a₁, a₂, a₃, rfl⟩ := eq_mul_X_sub_C_of_degree_three p hp_deg hp_roots hp_monic
  obtain ⟨b₁, b₂, b₃, rfl⟩ := eq_mul_X_sub_C_of_degree_three q hq_deg hq_roots hq_monic
  set sp := cubicS a₁ a₂ a₃
  set tp := cubicT a₁ a₂ a₃
  set sq := cubicS b₁ b₂ b₃
  set tq := cubicT b₁ b₂ b₃
  have hsp : 0 ≤ sp := cubicS_nonneg a₁ a₂ a₃
  have hsq : 0 ≤ sq := cubicS_nonneg b₁ b₂ b₃
  have hdp : 0 ≤ 4 * sp ^ 3 - 27 * tp ^ 2 := cubic_disc_nonneg a₁ a₂ a₃
  have hdq : 0 ≤ 4 * sq ^ 3 - 27 * tq ^ 2 := cubic_disc_nonneg b₁ b₂ b₃
  have hsos := cubic_stam_sos sp tp sq tq hsp hsq hdp hdq
  have hdr : 0 ≤ 4 * (sp + sq) ^ 3 - 27 * (tp + tq) ^ 2 := by
    by_cases h_sum0 : sp + sq = 0
    · have hsp0 : sp = 0 := by linarith
      have hsq0 : sq = 0 := by linarith
      rw [hsp0] at hdp
      rw [hsq0] at hdq
      have htp0 : tp = 0 := sq_eq_zero_iff.mp (le_antisymm (by linarith) (sq_nonneg tp))
      have htq0 : tq = 0 := sq_eq_zero_iff.mp (le_antisymm (by linarith) (sq_nonneg tq))
      rw [h_sum0, htp0, htq0]; norm_num
    · have h_sum_pos : 0 < sp + sq := lt_of_le_of_ne (by linarith) (Ne.symm h_sum0)
      have h_lhs_nonneg : 0 ≤ (4 * sp ^ 3 - 27 * tp ^ 2) / (18 * sp ^ 2) +
          (4 * sq ^ 3 - 27 * tq ^ 2) / (18 * sq ^ 2) := by positivity
      have h_rhs_nonneg : 0 ≤ (4 * (sp + sq) ^ 3 - 27 * (tp + tq) ^ 2) /
          (18 * (sp + sq) ^ 2) := le_trans h_lhs_nonneg hsos
      exact (div_nonneg_iff.mp h_rhs_nonneg).resolve_right
        (not_and_of_not_right _ (not_le_of_gt (by positivity))) |>.1
  obtain ⟨u₁, u₂, u₃, _, hu_s, hu_t⟩ :=
    vieta_cardano_exists_roots (sp + sq) (tp + tq) (by linarith) hdr
  set μ := (a₁ + a₂ + a₃ + b₁ + b₂ + b₃) / 3
  set r₁ := u₁ + μ
  set r₂ := u₂ + μ
  set r₃ := u₃ + μ
  have hr_sum : r₁ + r₂ + r₃ = (a₁ + a₂ + a₃) + (b₁ + b₂ + b₃) := by
    dsimp [r₁, r₂, r₃, μ]; linarith
  have hr_s : cubicS r₁ r₂ r₃ = sp + sq := by
    have : cubicS r₁ r₂ r₃ = cubicS u₁ u₂ u₃ := by unfold cubicS; dsimp [r₁, r₂, r₃]; ring
    rw [this, hu_s]
  have hr_t : cubicT r₁ r₂ r₃ = tp + tq := by
    have : cubicT r₁ r₂ r₃ = cubicT u₁ u₂ u₃ := by unfold cubicT; dsimp [r₁, r₂, r₃]; ring
    rw [this, hu_t]
  rw [finiteAdditiveConvolution_three_mul_X_sub_C a₁ a₂ a₃ b₁ b₂ b₃ r₁ r₂ r₃ hr_sum hr_s hr_t,
    one_div_Phi_cubic a₁ a₂ a₃, one_div_Phi_cubic b₁ b₂ b₃, one_div_Phi_cubic r₁ r₂ r₃,
    hr_s, hr_t, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal hsos

end Arxiv.«2602.05192»
