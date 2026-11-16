/-
Copyright 2025 The Formal Conjectures Authors.

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

public import Mathlib
public meta import FormalConjecturesUtil.Attributes.Basic
public import FormalConjecturesForMathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The length of an $s$-increasing sequence of $r$-tuples

This file contains the formalisation of [GoLo21] up to and
including Conjecture 1.8.

*References:*
- [arxiv/1609.08688](https://arxiv.org/abs/1609.08688)
  **The length of an $s$-increasing sequence of $r$-tuples** by *W. T. Gowers, J. Long*
- [GoLo21](https://www.cambridge.org/core/journals/combinatorics-probability-and-computing/article/abs/length-of-an-sincreasing-sequence-of-rtuples/7301418D47DB1ECD6BE71C20E8A98D0A)
  **The length of an $s$-increasing sequence of $r$-tuples**
  by *W. T. Gowers, J. Long*, Combinatorics, Probability and Computing (2021), 686-721
-/

@[expose] public section

namespace Arxiv.«1609.08688»

/--
Let $a = (a_1, a_2, a_3)$ and $b = (b_1, b_2, b_3)$ be two triples of integers.
Say that $a$ is $2$-less than $b$, or $a <_2 b$, if $a_i < b_i$ for at least
two coordinates $i$.
-/
def lt₂ {α : Type*} [LT α] (a b : Fin 3 → α) : Prop :=
  ∃ (i j : Fin 3), i ≠ j ∧ a i < b i ∧ a j < b j

local infix:50 " <₂ " => lt₂

@[simp, category API, AMS 5]
theorem not_lt₂ {α : Type*} [LinearOrder α] {a b : Fin 3 → α} :
    ¬a <₂ b ↔ ∀ i j, i ≠ j → a i < b i → b j ≤ a j := by simp [lt₂]

@[category API, AMS 5]
theorem not_lt₂_of_forall_le {α : Type*} [LinearOrder α] {a b : Fin 3 → α}
    (h : ∀ i, b i ≤ a i) : ¬a <₂ b := not_lt₂.2 fun _ _ _ _ => h _

@[category API, AMS 5]
theorem not_lt₂_of_exists {α : Type*} [LinearOrder α] {a b : Fin 3 → α}
    (i j : Fin 3) (hij : i ≠ j) (hi : b i ≤ a i) (hj : b j ≤ a j) :
    ¬a <₂ b := by
  refine not_lt₂.2 fun k l hkl h => ?_
  have : k ≠ i := fun hk => not_lt.2 hi (hk ▸ h)
  have : k ≠ j := fun hk => not_lt.2 hj (hk ▸ h)
  have : l = i ∨ l = j := by omega
  rcases this with (rfl | rfl); exact hi; exact hj

@[category API, AMS 5]
theorem not_lt₂_self {α : Type*} [LinearOrder α] (a : Fin 3 → α) : ¬a <₂ a := by
  simp

/-- For example, $(3, 3, 9) <_2 (5, 6, 1)$. -/
@[category test, AMS 5]
theorem lt₂_example_1 : ![3, 3, 9] <₂ ![5, 6, 1] := ⟨0, 1, zero_ne_one, by simp⟩

/-- $(5, 6, 1) <_2 (7, 7, 7)$ -/
@[category test, AMS 5]
theorem lt₂_example_2 : ![5, 6, 1] <₂ ![7, 7, 7] := ⟨0, 2, by simp, by simp⟩

/-- $(7, 7, 7) <_2 (7, 8, 9)$ -/
@[category test, AMS 5]
theorem lt₂_example_3 : ![7, 7, 7] <₂ ![7, 8, 9] := ⟨1, 2, by simp, by simp⟩

/-- but $(1, 2, 3)$ is not $2$-less than $(1, 2, 4)$. -/
@[category test, AMS 5]
theorem not_lt₂_example : ¬![1, 2, 3] <₂ ![1, 2, 4] := not_lt₂_of_exists 0 1 zero_ne_one (by simp) (by simp)

/-- The $2$-less relation is not transitive on the naturals. -/
@[category API, AMS 5]
theorem not_trans_lt₂_nat : ∃ (a b c : Fin 3 → ℕ),
    a <₂ b ∧ b <₂ c ∧ ¬a <₂ c :=
  ⟨![1, 2, 3], ![2, 3, 1], ![3, 1, 2], ⟨0, 1, zero_ne_one, by simp⟩,
     ⟨0, 2, by simp, by simp⟩, not_lt₂_of_exists 1 2 (by simp) (by simp) (by simp)⟩

/--
Since the $2$-less relation is not transitive, we make a further definition to
specify transivity.
-/
def IsIncreasing₂ {α : Type*} [LT α] (s : List (Fin 3 → α)) : Prop := s.Pairwise lt₂

@[simp, category API, AMS 5]
theorem isIncreasing₂_nil {α : Type*} [LT α] : IsIncreasing₂ (α := α) [] := by
  simp [IsIncreasing₂]

@[simp, category API, AMS 5]
theorem isIncreasing₂_singleton {α : Type*} [LT α] (a : Fin 3 → α) : IsIncreasing₂ [a] := by
  simp [IsIncreasing₂]

@[category API, AMS 5]
theorem isIncreasing₂_const_length {α : Type*} [LinearOrder α] {val : α} {s : List (Fin 3 → α)}
    (h : IsIncreasing₂ s)
    (h_const : ∀ a ∈ s, ∀ j, a j = val) : s.length < 2 := by
  by_contra!
  obtain ⟨i, j, -, hi, -⟩ :=
    List.pairwise_iff_getElem.1 h 0 1 (by linarith) (by linarith) zero_lt_one
  rw [h_const _ (List.getElem_mem _) i, h_const _ (List.getElem_mem _) i] at hi
  exact lt_irrefl _ hi

/--
Let $F(n)$ be the maximal length of a $2$-increasing sequence of triples with each coordinate
belong to $[n]$ ($= \{1, 2, ..., n\}$).
-/
noncomputable def maximalLength (n : ℕ) : ℕ :=
  sSup { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) }

local notation "F" => maximalLength

@[category test, AMS 5]
theorem maximalLength_zero : maximalLength 0 = 0 := by
  have (x : ℕ) (s : List (Fin 3 → ℕ)) :
      IsIncreasing₂ s ∧ (∀ a, a ∉ s) ∧ s.length = x ↔ s = [] ∧ x = 0 := by
    refine ⟨fun ⟨ha₁, ha₂, rfl⟩ => ?_, fun ⟨h₁, h₂⟩ => by simp [h₁, h₂]⟩
    simp only [List.length_eq_zero_iff, and_self]
    refine List.eq_nil_of_subset_nil fun ai hai => ?_
    simpa using ha₂ ai hai
  simp [maximalLength, fun x => exists_congr (this x)]

@[category test, AMS 5]
theorem maximalLength_one : maximalLength 1 = 1 := by
  classical
  have (x : ℕ) (s : List (Fin 3 → ℕ)) :
      IsIncreasing₂ s ∧ (∀ a ∈ s, ∀ i, a i = 1) ∧ s.length = x ↔
        s = [fun _ => 1] ∧ x = 1 ∨ s = [] ∧ x = 0 := by
    refine ⟨fun ⟨hs₁, hs₂, hx⟩ => ?_, fun h => by aesop⟩
    have := hx ▸ isIncreasing₂_const_length hs₁ hs₂
    interval_cases x; simp [List.length_eq_zero_iff.1 hx]; simp
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hx
    simp at hs₂
    rw [show a = fun _ => 1 from funext fun i => by simp [hs₂ i]]
  simp [maximalLength, fun x => exists_congr (this x)]
  rw [Nat.sSup_def ⟨1, by aesop⟩, Nat.find_eq_iff]
  refine ⟨by aesop, fun n hn => ?_⟩
  simp [Nat.lt_one_iff.1 hn]
  exact ⟨1, ⟨[fun _ => 1], by simp⟩, one_ne_zero⟩

@[category test, AMS 5]
theorem maximalLength_four : maximalLength 4 = 8 := by
  sorry

/-- In a set of more than $n^2$ triples with coordinates from $\{1, ..., n\}$ we must
have two triples that are equal in their first two coordinates. -/
@[category API, AMS 5]
lemma exists_pair_of_mem_Icc {s : List (Fin 3 → ℕ)} {n : ℕ} (_hn : 2 ≤ n)
    (hs₁ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (hs₂ : s.length > n ^ 2) :
    ∃ (i j : Fin s.length), i ≠ j ∧ s[i] 0 = s[j] 0 ∧ s[i] 1 = s[j] 1 := by
  classical
  let f : Fin s.length → ℕ × ℕ := fun k => (s[k] 0, s[k] 1)
  let t : Finset (ℕ × ℕ) := Finset.Icc 1 n ×ˢ Finset.Icc 1 n
  have ht_card : t.card < (Finset.univ : Finset (Fin s.length)).card := by
    simp only [t, Finset.card_univ, Fintype.card_fin, Finset.card_product,
      Nat.card_Icc, Nat.add_sub_cancel, ← sq]
    exact hs₂
  have hf : ∀ k ∈ (Finset.univ : Finset (Fin s.length)), f k ∈ t := by
    intro k _
    have hmem : s[k] ∈ s := List.getElem_mem k.isLt
    have h0 := hs₁ _ hmem ⟨0, rfl⟩
    have h1 := hs₁ _ hmem ⟨1, rfl⟩
    rw [Set.mem_Icc] at h0 h1
    simp only [t, f, Finset.mem_product, Finset.mem_Icc]
    exact ⟨h0, h1⟩
  obtain ⟨i, _, j, _, hij, hfij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to ht_card hf
  exact ⟨i, j, hij, congrArg Prod.fst hfij, congrArg Prod.snd hfij⟩

/--
For all $n$ we have $F(n) \leq n^2$.

This is the upper bound in [GoLo21, Proposition 1.4], proved by applying the
pigeonhole principle to the first two coordinates.
-/
@[category research solved, AMS 5]
theorem maximalLength_le (n : ℕ) : F n ≤ n ^ 2 := by
  by_cases hn : 2 ≤ n
  · rw [maximalLength]
    refine csSup_le ?_ ?_
    · exact ⟨0, ⟨[], by simp, isIncreasing₂_nil, rfl⟩⟩
    · intro _ hm
      rcases hm with ⟨s, hs_range, hs_inc, rfl⟩
      by_contra hle
      have hs_length : n ^ 2 < s.length := Nat.lt_of_not_ge hle
      obtain ⟨i, j, hij, h0, h1⟩ :=
        exists_pair_of_mem_Icc hn hs_range hs_length
      have hp : s.Pairwise lt₂ := hs_inc
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact (not_lt₂_of_exists 0 1 zero_ne_one h0.ge h1.ge)
          (List.pairwise_iff_get.1 hp i j hij)
      · exact (not_lt₂_of_exists 0 1 zero_ne_one h0.le h1.le)
          (List.pairwise_iff_get.1 hp j i hji)
  · cases n with
    | zero => simp [maximalLength_zero]
    | succ n =>
      cases n with
      | zero => simp [maximalLength_one]
      | succ n =>
        exact (hn (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))).elim

private def sqTriple (m t : ℕ) : Fin 3 → ℕ :=
  let i := (t / m) / m
  let j := (t / m) % m
  let k := t % m
  ![m * i + j + 1, m * i + k + 1, m * j + k + 1]

private lemma sqTriple_lt₂ {m x y : ℕ} (hm : 0 < m) (hxy : x < y) :
    sqTriple m x <₂ sqTriple m y := by
  set qx := x / m
  set qy := y / m
  set ix := qx / m
  set jx := qx % m
  set kx := x % m
  set iy := qy / m
  set jy := qy % m
  set ky := y % m
  have h0x : sqTriple m x 0 = m * ix + jx + 1 := rfl
  have h1x : sqTriple m x 1 = m * ix + kx + 1 := rfl
  have h2x : sqTriple m x 2 = m * jx + kx + 1 := rfl
  have h0y : sqTriple m y 0 = m * iy + jy + 1 := rfl
  have h1y : sqTriple m y 1 = m * iy + ky + 1 := rfl
  have h2y : sqTriple m y 2 = m * jy + ky + 1 := rfl
  have hjx : jx < m := Nat.mod_lt qx hm
  have hkx : kx < m := Nat.mod_lt x hm
  have hjy : jy < m := Nat.mod_lt qy hm
  have hky : ky < m := Nat.mod_lt y hm
  have hqx_eq : m * ix + jx = qx := Nat.div_add_mod qx m
  have hqy_eq : m * iy + jy = qy := Nat.div_add_mod qy m
  have hx_eq : m * qx + kx = x := Nat.div_add_mod x m
  have hy_eq : m * qy + ky = y := Nat.div_add_mod y m
  have hq_le : qx ≤ qy := Nat.div_le_div_right (le_of_lt hxy)
  have hi_le : ix ≤ iy := Nat.div_le_div_right hq_le
  rcases lt_or_eq_of_le hi_le with hi_lt | hi_eq
  · have hm_ilt : m * ix + m ≤ m * iy := by
      calc m * ix + m = m * (ix + 1) := by ring
        _ ≤ m * iy := Nat.mul_le_mul_left m hi_lt
    refine ⟨0, 1, by decide, ?_, ?_⟩
    · rw [h0x, h0y]; omega
    · rw [h1x, h1y]; omega
  · have hm_ieq : m * ix = m * iy := by rw [hi_eq]
    rcases lt_or_eq_of_le hq_le with hq_lt | hq_eq
    · have hj_lt : jx < jy := by omega
      have hm_jlt : m * jx + m ≤ m * jy := by
        calc m * jx + m = m * (jx + 1) := by ring
          _ ≤ m * jy := Nat.mul_le_mul_left m hj_lt
      refine ⟨0, 2, by decide, ?_, ?_⟩
      · rw [h0x, h0y]; omega
      · rw [h2x, h2y]; omega
    · have hm_qeq : m * qx = m * qy := by rw [hq_eq]
      have hj_eq : jx = jy := by omega
      have hm_jeq : m * jx = m * jy := by rw [hj_eq]
      have hk_lt : kx < ky := by omega
      refine ⟨1, 2, by decide, ?_, ?_⟩
      · rw [h1x, h1y]; omega
      · rw [h2x, h2y]; omega

/-- Moreover, whenever $n$ is a perfect square we have $F(n) \geq n^{3/2}$. -/
@[category research solved, AMS 5]
theorem maximalLength_ge_of_isSquare {n : ℕ} (h : IsSquare n) :
    n.sqrt ^ 3 ≤ F n := by
  rcases h with ⟨m, rfl⟩
  rw [Nat.sqrt_eq]
  rcases m with _ | m
  · simp
  · rcases m with _ | m
    · simp [maximalLength_one]
    · set M := m + 2
      have hM : 2 ≤ M := by omega
      have hM_pos : 0 < M := by omega
      have hMM : 2 ≤ M * M := by nlinarith
      rw [maximalLength]
      refine le_csSup ?_ ?_
      · refine ⟨(M * M) ^ 2, ?_⟩
        rintro _ ⟨s, hs_range, hs_inc, rfl⟩
        by_contra hle
        have hs_length : (M * M) ^ 2 < s.length := Nat.lt_of_not_ge hle
        obtain ⟨i, j, hij, h0, h1⟩ :=
          exists_pair_of_mem_Icc hMM hs_range hs_length
        have hp : s.Pairwise lt₂ := hs_inc
        rcases lt_or_gt_of_ne hij with hij | hji
        · exact (not_lt₂_of_exists 0 1 zero_ne_one h0.ge h1.ge)
            (List.pairwise_iff_get.1 hp i j hij)
        · exact (not_lt₂_of_exists 0 1 zero_ne_one h0.le h1.le)
            (List.pairwise_iff_get.1 hp j i hji)
      · refine ⟨(List.range (M ^ 3)).map (sqTriple M), ?_, ?_, by simp⟩
        · intro a ha
          rcases List.mem_map.mp ha with ⟨t, ht, rfl⟩
          have ht_lt : t < M ^ 3 := List.mem_range.mp ht
          rintro _ ⟨idx, rfl⟩
          set q := t / M
          set i := q / M
          set j := q % M
          set k := t % M
          have hj : j < M := Nat.mod_lt q hM_pos
          have hk : k < M := Nat.mod_lt t hM_pos
          have hq_lt : q < M * M :=
            Nat.div_lt_of_lt_mul (by linarith [ht_lt, show M ^ 3 = M * (M * M) by ring])
          have hi : i < M := Nat.div_lt_of_lt_mul hq_lt
          have him : M * i + M ≤ M * M := by
            calc M * i + M = M * (i + 1) := by ring
              _ ≤ M * M := Nat.mul_le_mul_left M hi
          have hjm : M * j + M ≤ M * M := by
            calc M * j + M = M * (j + 1) := by ring
              _ ≤ M * M := Nat.mul_le_mul_left M hj
          rw [Set.mem_Icc]
          fin_cases idx
          · change 1 ≤ M * i + j + 1 ∧ M * i + j + 1 ≤ M * M; omega
          · change 1 ≤ M * i + k + 1 ∧ M * i + k + 1 ≤ M * M; omega
          · change 1 ≤ M * j + k + 1 ∧ M * j + k + 1 ≤ M * M; omega
        · rw [IsIncreasing₂, List.pairwise_map]
          exact List.Pairwise.imp (sqTriple_lt₂ hM_pos) List.pairwise_lt_range


/-- Two triples $t_1$ and $t_2$ are $2$-comparable if one of them is $2$-less
than the other. -/
def IsComparable₂ {α : Type*} [LT α] (t₁ t₂ : Fin 3 → α) : Prop :=
  t₁ <₂ t₂ ∨ t₂ <₂ t₁

/-- A set of triples is $2$-comparable if any two distinct members of it are $2$-comparable. -/
def IsComparableSet₂ {α : Type*} [LT α] (s : List (Fin 3 → α)) : Prop :=
  ∀ t₁ ∈ s, ∀ t₂ ∈ s, t₁ ≠ t₂ → IsComparable₂ t₁ t₂

open Filter in
/-- $F(n) \leq n^2 / \exp(\Omega(\log^*(n)))$, i.e. there is a constant $c > 0$ such that
$F(n) \leq n^2 / \exp(c \log^*(n))$ for all sufficiently large $n$. -/
@[category research solved, AMS 5]
theorem maximalLength_le_isBigO : ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    (F n : ℝ) ≤ (n : ℝ) ^ 2 / Real.exp (c * (Real.iteratedLog n : ℝ)) := by
  sorry

/-- We define the product of two triples $(a, b, c)$ and $(d, e, f)$ by
$((a, d), (b, e), (c, f))$, where the pairs are ordered lexicographically. -/
def tripleProduct {α : Type*} (a b : Fin 3 → α) : Fin 3 → α ×ₗ α :=
  fun i => toLex (a i, b i)

@[simp, category API, AMS 5]
theorem tripleProduct_const {α : Type*} (a : α) :
    tripleProduct (fun _ ↦ a) (fun _ ↦ a) = fun _ ↦ toLex (a, a) :=
  rfl

@[simp, category API, AMS 5]
theorem tripleProduct_vecConst_const {α : Type*} (a : α) :
    tripleProduct ![a, a, a] ![a, a, a] = ![toLex (a, a), toLex (a, a), toLex (a, a)] := by
  ext i
  fin_cases i <;> rfl

/-- We define the product $\otimes$ of two sequences $(a_i, b_i, c_i)$ and
$(d_i, e_i, f_i)$ by the sequence $((a_i, d_j), (b_i, e_j), (c_i, f_j))$, where
the indices $(i, j)$ are arranged lexicographically, and the pairs are also
ordered lexicographically. -/
def sequenceProduct {α : Type*} (s t : List (Fin 3 → α)) : List (Fin 3 → α ×ₗ α) :=
  s.flatMap (fun a => List.map (tripleProduct a) t)

local infix:100 " ⊗₂ " => sequenceProduct

@[category test, AMS 5]
theorem sequenceProduct_example :
    [![1, 1, 1]] ⊗₂ [![1, 1, 1]] = [![toLex (1, 1), toLex (1, 1), toLex (1, 1)]] := by
  simp [sequenceProduct]

/-- The product of two $2$-increasing sequences is $2$-increasing; this is the point of
ordering the pairs lexicographically. -/
@[category test, AMS 5]
theorem isIncreasing₂_sequenceProduct_example :
    IsIncreasing₂ ([![1, 1, 1], ![2, 2, 2]] ⊗₂ [![1, 1, 1], ![2, 2, 2]]) := by
  unfold IsIncreasing₂ sequenceProduct tripleProduct lt₂
  decide

private lemma length_le_of_isIncreasing₂ {n : ℕ} {s : List (Fin 3 → ℕ)}
    (hs₁ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (hs₂ : IsIncreasing₂ s) :
    s.length ≤ (max n 2) ^ 2 := by
  by_contra hle
  have hs_len : (max n 2) ^ 2 < s.length := Nat.lt_of_not_ge hle
  have hs₁' : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 (max n 2) := fun a ha =>
    (hs₁ a ha).trans (Set.Icc_subset_Icc_right (le_max_left n 2))
  obtain ⟨i, j, hij, h0, h1⟩ := exists_pair_of_mem_Icc (le_max_right n 2) hs₁' hs_len
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (not_lt₂_of_exists 0 1 zero_ne_one h0.ge h1.ge)
      (List.pairwise_iff_get.1 hs₂ i j hij)
  · exact (not_lt₂_of_exists 0 1 zero_ne_one h0.le h1.le)
      (List.pairwise_iff_get.1 hs₂ j i hji)

private lemma bddAbove_maximalLength (n : ℕ) :
    BddAbove { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) } := by
  refine ⟨(max n 2) ^ 2, ?_⟩
  rintro _ ⟨s, hs₁, hs₂, rfl⟩
  exact length_le_of_isIncreasing₂ hs₁ hs₂

private lemma exists_list_maximalLength (n : ℕ) :
    ∃ s : List (Fin 3 → ℕ),
      (∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) ∧ IsIncreasing₂ s ∧ s.length = F n := by
  have hne : { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) }.Nonempty :=
    ⟨0, [], by simp, isIncreasing₂_nil, rfl⟩
  rcases Nat.sSup_mem hne (bddAbove_maximalLength n) with ⟨s, hs₁, hs₂, hlen⟩
  exact ⟨s, hs₁, hs₂, hlen⟩

private lemma maximalLength_mono {m n : ℕ} (hmn : m ≤ n) : F m ≤ F n := by
  obtain ⟨s, hs₁, hs₂, hlen⟩ := exists_list_maximalLength m
  rw [← hlen, maximalLength]
  refine le_csSup (bddAbove_maximalLength n) ⟨s, ?_, hs₂, rfl⟩
  intro a ha
  exact (hs₁ a ha).trans (Set.Icc_subset_Icc_right hmn)

private def prodTriple (n : ℕ) (a b : Fin 3 → ℕ) : Fin 3 → ℕ :=
  fun i => n * (a i - 1) + b i

private lemma prodTriple_mem_Icc {m n : ℕ} {a b : Fin 3 → ℕ}
    (ha : Set.range a ⊆ Set.Icc 1 m) (hb : Set.range b ⊆ Set.Icc 1 n) :
    Set.range (prodTriple n a b) ⊆ Set.Icc 1 (m * n) := by
  rintro _ ⟨i, rfl⟩
  have hai := Set.mem_Icc.mp (ha ⟨i, rfl⟩)
  have hbi := Set.mem_Icc.mp (hb ⟨i, rfl⟩)
  rw [Set.mem_Icc]
  refine ⟨by dsimp [prodTriple]; omega, ?_⟩
  dsimp [prodTriple]
  calc n * (a i - 1) + b i ≤ n * (a i - 1) + n := Nat.add_le_add_left hbi.2 _
    _ = n * (a i - 1 + 1) := by ring
    _ = n * a i := by rw [Nat.sub_add_cancel hai.1]
    _ ≤ n * m := Nat.mul_le_mul_left n hai.2
    _ = m * n := Nat.mul_comm n m

private lemma prodTriple_lt₂_right (n : ℕ) (a : Fin 3 → ℕ) {b₁ b₂ : Fin 3 → ℕ}
    (hb : b₁ <₂ b₂) : prodTriple n a b₁ <₂ prodTriple n a b₂ := by
  rcases hb with ⟨i, j, hij, hi, hj⟩
  exact ⟨i, j, hij, Nat.add_lt_add_left hi _, Nat.add_lt_add_left hj _⟩

private lemma prodTriple_lt₂_left {m n : ℕ} {a₁ a₂ b₁ b₂ : Fin 3 → ℕ}
    (ha₁ : Set.range a₁ ⊆ Set.Icc 1 m)
    (hb₁ : Set.range b₁ ⊆ Set.Icc 1 n) (hb₂ : Set.range b₂ ⊆ Set.Icc 1 n)
    (ha : a₁ <₂ a₂) : prodTriple n a₁ b₁ <₂ prodTriple n a₂ b₂ := by
  have coord_lt {k : Fin 3} (hk : a₁ k < a₂ k) :
      prodTriple n a₁ b₁ k < prodTriple n a₂ b₂ k := by
    have ha1k := (Set.mem_Icc.mp (ha₁ ⟨k, rfl⟩)).1
    have hb1k := (Set.mem_Icc.mp (hb₁ ⟨k, rfl⟩)).2
    have hb2k := (Set.mem_Icc.mp (hb₂ ⟨k, rfl⟩)).1
    dsimp [prodTriple]
    calc n * (a₁ k - 1) + b₁ k ≤ n * (a₁ k - 1) + n := Nat.add_le_add_left hb1k _
      _ = n * (a₁ k - 1 + 1) := by ring
      _ = n * a₁ k := by rw [Nat.sub_add_cancel ha1k]
      _ ≤ n * (a₂ k - 1) := Nat.mul_le_mul_left n (Nat.le_sub_one_of_lt hk)
      _ < n * (a₂ k - 1) + b₂ k := Nat.lt_add_of_pos_right hb2k
  rcases ha with ⟨i, j, hij, hi, hj⟩
  exact ⟨i, j, hij, coord_lt hi, coord_lt hj⟩

private def prodSeq (n : ℕ) : List (Fin 3 → ℕ) → List (Fin 3 → ℕ) → List (Fin 3 → ℕ)
  | [], _ => []
  | a :: s, t => t.map (prodTriple n a) ++ prodSeq n s t

private lemma prodSeq_length (n : ℕ) (s t : List (Fin 3 → ℕ)) :
    (prodSeq n s t).length = s.length * t.length := by
  induction s with
  | nil => simp [prodSeq]
  | cons a s ih =>
    simp only [prodSeq, List.length_append, List.length_map, List.length_cons, ih]
    ring

private lemma mem_prodSeq {n : ℕ} {s t : List (Fin 3 → ℕ)} {x : Fin 3 → ℕ} :
    x ∈ prodSeq n s t ↔ ∃ a ∈ s, ∃ b ∈ t, prodTriple n a b = x := by
  induction s with
  | nil => simp [prodSeq]
  | cons a s ih =>
    simp only [prodSeq, List.mem_append, List.mem_map, ih, List.mem_cons]
    constructor
    · rintro (⟨b, hb, hbx⟩ | ⟨a', ha', b, hb, hbx⟩)
      · exact ⟨a, Or.inl rfl, b, hb, hbx⟩
      · exact ⟨a', Or.inr ha', b, hb, hbx⟩
    · rintro ⟨a', rfl | ha', b, hb, hbx⟩
      · exact Or.inl ⟨b, hb, hbx⟩
      · exact Or.inr ⟨a', ha', b, hb, hbx⟩

private lemma prodSeq_isIncreasing₂ {m n : ℕ} {s t : List (Fin 3 → ℕ)}
    (hs₁ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 m) (hs₂ : IsIncreasing₂ s)
    (ht₁ : ∀ b ∈ t, Set.range b ⊆ Set.Icc 1 n) (ht₂ : IsIncreasing₂ t) :
    IsIncreasing₂ (prodSeq n s t) := by
  induction s with
  | nil => simp [prodSeq]
  | cons a s ih =>
    rw [IsIncreasing₂] at hs₂ ⊢
    rw [List.pairwise_cons] at hs₂
    rw [prodSeq, List.pairwise_append]
    refine ⟨?_, ih (fun a' ha' => hs₁ a' (List.mem_cons_of_mem a ha')) hs₂.2, ?_⟩
    · rw [List.pairwise_map]
      exact List.Pairwise.imp (fun h => prodTriple_lt₂_right n a h) ht₂
    · intro x hx y hy
      rcases List.mem_map.mp hx with ⟨b₁, hb₁, rfl⟩
      rcases mem_prodSeq.mp hy with ⟨a₂, ha₂, b₂, hb₂, rfl⟩
      exact prodTriple_lt₂_left (hs₁ a List.mem_cons_self)
        (ht₁ b₁ hb₁) (ht₁ b₂ hb₂) (hs₂.1 a₂ ha₂)

private lemma maximalLength_mul_ge (m n : ℕ) : F m * F n ≤ F (m * n) := by
  obtain ⟨s, hs₁, hs₂, hs_len⟩ := exists_list_maximalLength m
  obtain ⟨t, ht₁, ht₂, ht_len⟩ := exists_list_maximalLength n
  rw [← hs_len, ← ht_len, ← prodSeq_length n s t, maximalLength]
  refine le_csSup (bddAbove_maximalLength (m * n)) ⟨prodSeq n s t, ?_, ?_, rfl⟩
  · intro x hx
    rcases mem_prodSeq.mp hx with ⟨a, ha, b, hb, rfl⟩
    exact prodTriple_mem_Icc (hs₁ a ha) (ht₁ b hb)
  · exact prodSeq_isIncreasing₂ hs₁ hs₂ ht₁ ht₂

private lemma maximalLength_pow_ge (n k : ℕ) : (F n) ^ k ≤ F (n ^ k) := by
  induction k with
  | zero => simp [maximalLength_one]
  | succ k ih =>
    calc (F n) ^ (k + 1) = (F n) ^ k * F n := by ring
      _ ≤ F (n ^ k) * F n := Nat.mul_le_mul_right (F n) ih
      _ ≤ F (n ^ k * n) := maximalLength_mul_ge (n ^ k) n
      _ = F (n ^ (k + 1)) := by rw [show n ^ k * n = n ^ (k + 1) by ring]

private lemma rpow_pow_le_maximalLength {n : ℕ} {e : ℝ} (h : F n = (n : ℝ) ^ e) (k : ℕ) :
    ((n ^ k : ℕ) : ℝ) ^ e ≤ F (n ^ k) := by
  have h_eq : ((n ^ k : ℕ) : ℝ) ^ e = ((F n : ℝ)) ^ k := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n),
      mul_comm (k : ℝ) e, Real.rpow_mul (Nat.cast_nonneg n), Real.rpow_natCast, ← h]
  rw [h_eq, ← Nat.cast_pow]
  exact Nat.cast_le.mpr (maximalLength_pow_ge n k)

private lemma le_pow_self {n : ℕ} (hn : 1 < n) : ∀ k : ℕ, k ≤ n ^ k
  | 0 => by simp
  | k + 1 => by
    have ih := le_pow_self hn k
    have hpos : 1 ≤ n ^ k := Nat.one_le_pow k n (by omega)
    calc k + 1 ≤ n ^ k + n ^ k := by omega
      _ = n ^ k * 2 := by ring
      _ ≤ n ^ k * n := Nat.mul_le_mul_left (n ^ k) hn
      _ = n ^ (k + 1) := by ring

private lemma exists_pow_le_and_lt {n : ℕ} (hn : 1 < n) :
    ∀ m : ℕ, 1 ≤ m → ∃ k : ℕ, n ^ k ≤ m ∧ m < n ^ (k + 1)
  | 0, hm => by omega
  | 1, _ => ⟨0, by simp, by simpa using hn⟩
  | m + 2, _ => by
    obtain ⟨k, hk1, hk2⟩ := exists_pow_le_and_lt hn (m + 1) (by omega)
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hk2) with hlt | heq
    · exact ⟨k, by omega, hlt⟩
    · refine ⟨k + 1, by omega, ?_⟩
      have hpos : 0 < n ^ (k + 1) := by positivity
      calc m + 2 = n ^ (k + 1) * 1 := by omega
        _ < n ^ (k + 1) * n := Nat.mul_lt_mul_of_pos_left hn hpos
        _ = n ^ (k + 2) := by ring

/-- Suppose that for some $n$ we have $F(n) = n ^ {\alpha}$. Then there are arbitrarily
large $m$ such that $F(m) \geq m^{\alpha}$. -/
@[category research solved, AMS 5]
theorem maximalLength_pow {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e) :
    ∃ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ e ≤ F m := by
  rw [Filter.frequently_atTop]
  intro N
  exact ⟨n ^ N, le_pow_self hn N, rpow_pow_le_maximalLength h N⟩

/-- Moreover, for every $\beta < \alpha$ and all sufficiently large $m$ we have
$F(m) \geq m^{\beta}$. -/
@[category research solved, AMS 5]
theorem maximalLength_pow_eventually {n : ℕ} {e : ℝ} (hn : 1 < n) (h : F n = (n : ℝ) ^ e)
    {b : ℝ} (hb : b < e) :
    ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ b ≤ F m := by
  have he_nonneg : 0 ≤ e := by
    by_contra! he_neg
    have h1_le_Fn : (1 : ℝ) ≤ (F n : ℝ) := by
      have : 1 ≤ F n := by
        rw [← maximalLength_one]
        exact maximalLength_mono (by omega)
      exact_mod_cast this
    have hn_gt1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h_lt1 : (n : ℝ) ^ e < 1 := by
      simpa using Real.rpow_lt_rpow_of_exponent_lt hn_gt1 he_neg
    linarith [h]
  have heb_pos : 0 < e - b := sub_pos.mpr hb
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hne_pos : 0 < (n : ℝ) ^ e := Real.rpow_pos_of_pos hn_pos e
  rw [Filter.eventually_atTop]
  refine ⟨max 1 (Nat.ceil (((n : ℝ) ^ e) ^ (1 / (e - b)))), ?_⟩
  intro m hm
  have hm1 : 1 ≤ m := le_trans (le_max_left _ _) hm
  have hm_pos : 0 < (m : ℝ) := by exact_mod_cast hm1
  have hm_thresh : ((n : ℝ) ^ e) ^ (1 / (e - b)) ≤ (m : ℝ) := by
    have : Nat.ceil (((n : ℝ) ^ e) ^ (1 / (e - b))) ≤ m := le_trans (le_max_right _ _) hm
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
  have h_ne_le : (n : ℝ) ^ e ≤ (m : ℝ) ^ (e - b) := by
    calc (n : ℝ) ^ e = ((n : ℝ) ^ e) ^ ((1 / (e - b)) * (e - b)) := by
          rw [one_div_mul_cancel (ne_of_gt heb_pos), Real.rpow_one]
      _ = (((n : ℝ) ^ e) ^ (1 / (e - b))) ^ (e - b) :=
          Real.rpow_mul (le_of_lt hne_pos) _ _
      _ ≤ (m : ℝ) ^ (e - b) :=
          Real.rpow_le_rpow (by positivity) hm_thresh (le_of_lt heb_pos)
  obtain ⟨k, hk_le, hk_lt⟩ := exists_pow_le_and_lt hn m hm1
  have hm_le_pow : (m : ℝ) ≤ ((n ^ k : ℕ) : ℝ) * (n : ℝ) := by
    have : m ≤ n ^ k * n := by
      calc m ≤ n ^ (k + 1) := le_of_lt hk_lt
        _ = n ^ k * n := by ring
    exact_mod_cast this
  have h_mul_ineq : (m : ℝ) ^ b * (n : ℝ) ^ e ≤ (F m : ℝ) * (n : ℝ) ^ e := by
    calc (m : ℝ) ^ b * (n : ℝ) ^ e ≤ (m : ℝ) ^ b * (m : ℝ) ^ (e - b) :=
          mul_le_mul_of_nonneg_left h_ne_le (by positivity)
      _ = (m : ℝ) ^ (b + (e - b)) := (Real.rpow_add hm_pos b (e - b)).symm
      _ = (m : ℝ) ^ e := by ring_nf
      _ ≤ (((n ^ k : ℕ) : ℝ) * (n : ℝ)) ^ e :=
          Real.rpow_le_rpow (by positivity) hm_le_pow he_nonneg
      _ = ((n ^ k : ℕ) : ℝ) ^ e * (n : ℝ) ^ e :=
          Real.mul_rpow (by positivity) (by positivity)
      _ ≤ (F (n ^ k) : ℝ) * (n : ℝ) ^ e :=
          mul_le_mul_of_nonneg_right (rpow_pow_le_maximalLength h k) (by positivity)
      _ ≤ (F m : ℝ) * (n : ℝ) ^ e := by
          have : (F (n ^ k) : ℝ) ≤ (F m : ℝ) :=
            Nat.cast_le.mpr (maximalLength_mono hk_le)
          exact mul_le_mul_of_nonneg_right this (by positivity)
  exact le_of_mul_le_mul_right h_mul_ineq hne_pos

/-- $F(n) \leq n^{3/2}$. -/
@[category research open, AMS 5]
theorem maximalLength_le_strong (n : ℕ) : F n ≤ Real.sqrt n ^ 3 := by
  sorry

end Arxiv.«1609.08688»
