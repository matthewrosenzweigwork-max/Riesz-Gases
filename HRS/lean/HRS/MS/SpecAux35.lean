import Mathlib

/-!
# S8P: eigenvectors of `T(1)` of a symmetric positive semigroup are eigenvectors of every `T(t)` (S8.7, packet b4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_semigroup_pow_eig`: if `T` is a semigroup on `[0,∞)`, strongly continuous,
symmetric for the coercive form `⟨x, B y⟩`, and `T 1 x = μ x` with `μ > 0`, then `T t x = μ^t x` for all `t ≥ 0`.

Proof: with `S = T(1/n)` (symmetric, and positive since `T(s) = T(s/2)²`) and `c = μ^{1/n}`, `y = S x - c x` satisfies
`∑_{k<n} c^{n-1-k} S^k y = S^n x - c^n x = 0`; pairing with `y` and positivity of every `⟨y, B S^k y⟩` gives `⟨y, B y⟩ ≤ 0`, so
`y = 0`.  Then `T(m/n) x = μ^{m/n} x` and continuity.
-/

noncomputable section

open Filter Topology Set
open scoped RealInnerProductSpace

namespace HRS.MS.Spec

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem s8p_psd_of_symm (T : ℝ → E →L[ℝ] E) (B : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, B x⟫)
    (hsymm : ∀ t, 0 ≤ t → ∀ x y, ⟪T t x, B y⟫ = ⟪x, B (T t y)⟫)
    (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → T (a + b) = T a * T b) {s : ℝ} (hs : 0 ≤ s) (y : E) :
    0 ≤ ⟪y, B (T s y)⟫ := by
  have h2 : T s = T (s / 2) * T (s / 2) := by
    have := hadd (s / 2) (s / 2) (by linarith) (by linarith)
    rwa [add_halves] at this
  have : ⟪y, B (T s y)⟫ = ⟪T (s / 2) y, B (T (s / 2) y)⟫ := by
    rw [hsymm (s / 2) (by linarith) y (T (s / 2) y), h2]; rfl
  rw [this]
  exact le_trans (mul_nonneg hc.le (sq_nonneg _)) (hlow _)

theorem s8p_root_eig (T : ℝ → E →L[ℝ] E) (B : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, B x⟫)
    (hsymm : ∀ t, 0 ≤ t → ∀ x y, ⟪T t x, B y⟫ = ⟪x, B (T t y)⟫)
    (hT0 : T 0 = 1) (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → T (a + b) = T a * T b)
    {μ : ℝ} (hμ : 0 < μ) {x : E} (hx : T 1 x = μ • x) {n : ℕ} (hn : 0 < n) :
    T (1 / (n : ℝ)) x = (μ ^ (1 / (n : ℝ))) • x := by
  set a : ℝ := 1 / (n : ℝ) with ha
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have ha0 : 0 < a := by positivity
  set cc : ℝ := μ ^ a with hcc
  have hcc0 : 0 < cc := Real.rpow_pos_of_pos hμ a
  have hccn : cc ^ n = μ := by
    rw [hcc, ← Real.rpow_natCast, ← Real.rpow_mul hμ.le, ha]
    have : 1 / (n : ℝ) * n = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hna : (n : ℝ) * a = 1 := by rw [ha]; field_simp
  set y : E := T a x - cc • x with hy
  -- the shift identity
  have hshift : ∀ k : ℕ, T ((k : ℝ) * a) y = T (((k + 1 : ℕ) : ℝ) * a) x - cc • T ((k : ℝ) * a) x := by
    intro k
    have h1 := hadd ((k : ℝ) * a) a (by positivity) ha0.le
    have h2 : (k : ℝ) * a + a = ((k + 1 : ℕ) : ℝ) * a := by push_cast; ring
    rw [h2] at h1
    rw [hy, map_sub, map_smul, h1]
    rfl
  set g : ℕ → E := fun k => cc ^ (n - k) • T ((k : ℝ) * a) x with hg
  have hterm : ∀ k ∈ Finset.range n, cc ^ (n - 1 - k) • T ((k : ℝ) * a) y = g (k + 1) - g k := by
    intro k hk
    have hk' : k < n := Finset.mem_range.1 hk
    have e1 : n - k = (n - 1 - k) + 1 := by omega
    have e2 : n - (k + 1) = n - 1 - k := by omega
    have e3 : cc ^ (n - k) = cc ^ (n - 1 - k) * cc := by rw [e1, pow_succ]
    have e4 : cc ^ (n - (k + 1)) = cc ^ (n - 1 - k) := by rw [e2]
    rw [hshift k]
    simp only [hg]
    rw [e3, e4, smul_sub, smul_smul]
  have hsum : ∑ k ∈ Finset.range n, cc ^ (n - 1 - k) • T ((k : ℝ) * a) y = 0 := by
    rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub]
    have hgn : g n = μ • x := by
      rw [hg]; simp only [Nat.sub_self, pow_zero, one_smul]
      rw [hna, hx]
    have hg0 : g 0 = μ • x := by
      rw [hg]; simp only [Nat.sub_zero, Nat.cast_zero, zero_mul, hT0, ContinuousLinearMap.one_apply, hccn]
    rw [hgn, hg0, sub_self]
  have hpos : ∀ k ∈ Finset.range n, 0 ≤ cc ^ (n - 1 - k) * ⟪y, B (T ((k : ℝ) * a) y)⟫ := fun k _ =>
    mul_nonneg (pow_nonneg hcc0.le _)
      (s8p_psd_of_symm T B hc hlow hsymm hadd (by positivity) y)
  have hinner : ∑ k ∈ Finset.range n, cc ^ (n - 1 - k) * ⟪y, B (T ((k : ℝ) * a) y)⟫ = 0 := by
    have : ⟪y, B (∑ k ∈ Finset.range n, cc ^ (n - 1 - k) • T ((k : ℝ) * a) y)⟫ = 0 := by
      rw [hsum]; simp
    rw [map_sum, inner_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, real_inner_smul_right]
  have h0 := Finset.single_le_sum hpos (Finset.mem_range.2 hn)
  rw [hinner] at h0
  simp only [Nat.cast_zero, zero_mul, hT0, ContinuousLinearMap.one_apply] at h0
  have hpowpos : 0 < cc ^ (n - 1 - 0) := pow_pos hcc0 _
  have hyy : ⟪y, B y⟫ ≤ 0 := by
    by_contra hne
    push Not at hne
    nlinarith [mul_pos hpowpos hne]
  have : ‖y‖ ^ 2 ≤ 0 := by
    by_contra hne
    push Not at hne
    nlinarith [hlow y]
  have hy0 : y = 0 := norm_eq_zero.1 (by nlinarith [norm_nonneg y])
  exact sub_eq_zero.1 hy0

theorem s8p_semigroup_pow_eig (T : ℝ → E →L[ℝ] E) (B : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, B x⟫)
    (hsymm : ∀ t, 0 ≤ t → ∀ x y, ⟪T t x, B y⟫ = ⟪x, B (T t y)⟫)
    (hT0 : T 0 = 1) (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → T (a + b) = T a * T b)
    (hTc : ∀ x, ContinuousOn (fun t => T t x) (Ici 0))
    {μ : ℝ} (hμ : 0 < μ) {x : E} (hx : T 1 x = μ • x) :
    ∀ t : ℝ, 0 ≤ t → T t x = (μ ^ t) • x := by
  -- rational times
  have hrat : ∀ (m n : ℕ), 0 < n → T ((m : ℝ) / n) x = (μ ^ ((m : ℝ) / n)) • x := by
    intro m n hn
    have hroot := s8p_root_eig T B hc hlow hsymm hT0 hadd hμ hx hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    set a : ℝ := 1 / (n : ℝ) with ha
    have ha0 : 0 < a := by positivity
    have hmn : (m : ℝ) / n = (m : ℝ) * a := by rw [ha]; ring
    rw [hmn]
    clear hmn
    induction m with
    | zero =>
        simp [hT0]
    | succ m ih =>
        have h1 := hadd ((m : ℝ) * a) a (by positivity) ha0.le
        have h2 : (m : ℝ) * a + a = ((m + 1 : ℕ) : ℝ) * a := by push_cast; ring
        rw [h2] at h1
        rw [h1, ContinuousLinearMap.mul_apply, hroot, map_smul, ih]
        rw [smul_smul, ← Real.rpow_add hμ]
        congr 2
        push_cast; ring
  -- density
  set s : Set ℝ := {t | ∃ m n : ℕ, 0 < n ∧ t = (m : ℝ) / n} with hs
  have hsub : s ⊆ Ici 0 := by
    rintro t ⟨m, n, hn, rfl⟩
    show (0 : ℝ) ≤ (m : ℝ) / (n : ℝ)
    positivity
  have hcl : Ici (0 : ℝ) ⊆ closure s := by
    intro r hr
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨(⌊r * ((n + 1 : ℕ) : ℝ)⌋₊ : ℝ) / ((n + 1 : ℕ) : ℝ), ⟨_, n + 1, Nat.succ_pos n, rfl⟩, ?_⟩
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hr0 : 0 ≤ r * ((n + 1 : ℕ) : ℝ) := mul_nonneg hr hn1.le
    have f1 := Nat.floor_le hr0
    have f2 := Nat.lt_floor_add_one (r * ((n + 1 : ℕ) : ℝ))
    rw [Real.dist_eq, abs_lt]
    constructor
    · have : r - (⌊r * ((n + 1 : ℕ) : ℝ)⌋₊ : ℝ) / ((n + 1 : ℕ) : ℝ) ≥ 0 := by
        rw [ge_iff_le, sub_nonneg, div_le_iff₀ hn1]; linarith
      have h3 : 0 < ε := hε
      linarith
    · have : r - (⌊r * ((n + 1 : ℕ) : ℝ)⌋₊ : ℝ) / ((n + 1 : ℕ) : ℝ) < 1 / ((n + 1 : ℕ) : ℝ) := by
        rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hn1]; linarith
      have h4 : 1 / ((n + 1 : ℕ) : ℝ) < ε := by
        push_cast
        exact hn
      linarith
  have hfc : ContinuousOn (fun t => T t x) (Ici 0) := hTc x
  have hgc : ContinuousOn (fun t : ℝ => (μ ^ t) • x) (Ici 0) :=
    (Real.continuous_const_rpow hμ.ne').smul continuous_const |>.continuousOn
  have heq : EqOn (fun t => T t x) (fun t : ℝ => (μ ^ t) • x) s := by
    rintro t ⟨m, n, hn, rfl⟩
    exact hrat m n hn
  intro t ht
  exact heq.of_subset_closure hfc hgc hsub hcl ht

end HRS.MS.Spec
