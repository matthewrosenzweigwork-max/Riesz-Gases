import HRS.MS.S21G2_W01
import HRS.MP.RdInit

/-!
# S21K2 W03A -- cutoff derivative bounds for the spatial cutoff packet (R26-T3.W03)

Pointwise estimate for the derivatives of `(chi_n - 1) * f`, `chi_n x = chi (x / (n+1))`:
`(partialDeriv idx ((chi_n - 1) f) x)^2 <= 1_{|x| >= n+1} * K * F x`, with `F x` the sum of all squared
ordered partial derivatives of order `<= r` of `f`.  No exact Leibniz formula is needed: the norm form
`norm_iteratedFDeriv_mul_le` plus `mri_norm_sq_le` suffice.  Helper prefix `s21k2_w03_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s21k2_w03_cutoff (d : ℕ) : ∃ χ : HRS.Euc d → ℝ, (∀ k : ℕ, ContDiff ℝ k χ) ∧
    (∀ x, ‖x‖ ≤ 1 → χ x = 1) ∧ ∀ x, 2 ≤ ‖x‖ → χ x = 0 := by
  let b : ContDiffBump (0 : HRS.Euc d) := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨b, fun k => b.contDiff, fun x hx => b.one_of_mem_closedBall (by simpa using hx),
    fun x hx => b.zero_of_le_dist (by simpa using hx)⟩

/-- `chi_n x - 1` with `chi_n x = chi (x / (n+1))`. -/
def s21k2_w03_g {d : ℕ} (χ : HRS.Euc d → ℝ) (n : ℕ) (x : HRS.Euc d) : ℝ :=
  χ (((n : ℝ) + 1)⁻¹ • x) - 1

theorem s21k2_w03_tilde_bound {d : ℕ} {χ : HRS.Euc d → ℝ} (hχ : ∀ k : ℕ, ContDiff ℝ k χ)
    (h2 : ∀ x, 2 ≤ ‖x‖ → χ x = 0) (k : ℕ) :
    ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ k (fun y => χ y - 1) y‖ ≤ C := by
  have hcs : HasCompactSupport χ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : HRS.Euc d) 2) fun x hx => h2 x ?_
    exact (by simpa using hx : 2 < ‖x‖).le
  cases k with
  | zero =>
    obtain ⟨C, hC⟩ := (hχ 0).continuous.bounded_above_of_compact_support hcs
    refine ⟨C + 1, fun y => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    calc ‖χ y - 1‖ ≤ ‖χ y‖ + ‖(1 : ℝ)‖ := norm_sub_le _ _
      _ ≤ C + 1 := by simpa using hC y
  | succ k =>
    obtain ⟨C, hC⟩ := ((hχ (k + 1)).continuous_iteratedFDeriv (by exact_mod_cast le_rfl)).bounded_above_of_compact_support
      (hcs.iteratedFDeriv (k + 1))
    refine ⟨C, fun y => ?_⟩
    have : iteratedFDeriv ℝ (k + 1) (fun y => χ y - 1) y = iteratedFDeriv ℝ (k + 1) χ y := by
      have e : (fun y => χ y - 1) = χ - fun _ => (1 : ℝ) := rfl
      rw [e, iteratedFDeriv_sub_apply ((hχ (k + 1)).contDiffAt) contDiffAt_const,
        iteratedFDeriv_succ_const]
      simp
    rw [this]; exact hC y

theorem s21k2_w03_g_bound {d : ℕ} {χ : HRS.Euc d → ℝ} (hχ : ∀ k : ℕ, ContDiff ℝ k χ)
    (h2 : ∀ x, 2 ≤ ‖x‖ → χ x = 0) (m : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k (s21k2_w03_g χ n) x‖ ≤ M := by
  choose C hC using s21k2_w03_tilde_bound hχ h2
  refine ⟨∑ i ∈ Finset.range (m + 1), |C i|, Finset.sum_nonneg fun i _ => abs_nonneg _,
    fun n k hk x => ?_⟩
  set L : HRS.Euc d →L[ℝ] HRS.Euc d := (((n : ℝ) + 1)⁻¹) • ContinuousLinearMap.id ℝ (HRS.Euc d) with hLdef
  have hg : s21k2_w03_g χ n = (fun y => χ y - 1) ∘ L := by
    funext y; simp [s21k2_w03_g, L]
  have hct : ContDiff ℝ k (fun y => χ y - 1) := (hχ k).sub contDiff_const
  rw [hg, L.iteratedFDeriv_comp_right hct x le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hL : ‖L‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    have h1 : ‖((n : ℝ) + 1)⁻¹‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    calc ‖((n : ℝ) + 1)⁻¹‖ * ‖ContinuousLinearMap.id ℝ (HRS.Euc d)‖ ≤ 1 * 1 :=
          mul_le_mul h1 ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hp : ∏ _i : Fin k, ‖L‖ ≤ 1 := Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => hL
  calc ‖iteratedFDeriv ℝ k (fun y => χ y - 1) (L x)‖ * ∏ _i : Fin k, ‖L‖
      ≤ ‖iteratedFDeriv ℝ k (fun y => χ y - 1) (L x)‖ * 1 :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ ≤ C k := by rw [mul_one]; exact hC k _
    _ ≤ |C k| := le_abs_self _
    _ ≤ ∑ i ∈ Finset.range (m + 1), |C i| :=
        Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _)
          (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

theorem s21k2_w03_g_vanish {d : ℕ} {χ : HRS.Euc d → ℝ} (h1 : ∀ x, ‖x‖ ≤ 1 → χ x = 1) (n k : ℕ)
    {x : HRS.Euc d} (hx : ‖x‖ < (n : ℝ) + 1) : iteratedFDeriv ℝ k (s21k2_w03_g χ n) x = 0 := by
  have hev : s21k2_w03_g χ n =ᶠ[𝓝 x] 0 := by
    have hn : Metric.ball (0 : HRS.Euc d) ((n : ℝ) + 1) ∈ 𝓝 x :=
      Metric.isOpen_ball.mem_nhds (by simpa using hx)
    filter_upwards [hn] with y hy
    have hy' : ‖y‖ < (n : ℝ) + 1 := by simpa using hy
    have hle : ‖((n : ℝ) + 1)⁻¹ • y‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), inv_mul_le_iff₀ (by positivity)]
      linarith
    simp [s21k2_w03_g, h1 _ hle]
  by_contra hne
  exact (notMem_tsupport_iff_eventuallyEq.2 hev)
    (support_iteratedFDeriv_subset (𝕜 := ℝ) k (Function.mem_support.2 hne))

theorem s21k2_w03_leibniz {d : ℕ} {χ : HRS.Euc d → ℝ} (hχ : ∀ k : ℕ, ContDiff ℝ k χ)
    (h1 : ∀ x, ‖x‖ ≤ 1 → χ x = 1) {M : ℝ} (hM0 : 0 ≤ M) (m : ℕ)
    (hM : ∀ n : ℕ, ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k (s21k2_w03_g χ n) x‖ ≤ M)
    {f : HRS.Euc d → ℝ} (hf : ContDiff ℝ m f) (n : ℕ) {j : ℕ} (hj : j ≤ m) (x : HRS.Euc d) :
    ‖iteratedFDeriv ℝ j (fun y => s21k2_w03_g χ n y * f y) x‖ ^ 2 ≤
      {y : HRS.Euc d | (n : ℝ) + 1 ≤ ‖y‖}.indicator
        (fun y => ((m + 1 : ℕ) : ℝ) * 4 ^ m * M ^ 2 * HRS.MP.RdInit.mriG m f y) x := by
  have hgm : ContDiff ℝ m (s21k2_w03_g χ n) := by
    have : ContDiff ℝ m (fun x : HRS.Euc d => χ (((n : ℝ) + 1)⁻¹ • x)) :=
      (hχ m).comp (contDiff_const_smul _)
    exact this.sub contDiff_const
  have hle := norm_iteratedFDeriv_mul_le hgm hf x (n := j) (by exact_mod_cast hj)
  by_cases hx : x ∈ {y : HRS.Euc d | (n : ℝ) + 1 ≤ ‖y‖}
  · rw [Set.indicator_of_mem hx]
    have hb : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (s21k2_w03_g χ n) x‖ *
        ‖iteratedFDeriv ℝ (j - i) f x‖ ≤ (2 : ℝ) ^ j * M * ‖iteratedFDeriv ℝ (j - i) f x‖ := by
      intro i hi
      have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      have h1' := hM n i (hi'.trans hj) x
      have h2 : (j.choose i : ℝ) ≤ 2 ^ j := by exact_mod_cast Nat.choose_le_two_pow j i
      have : (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (s21k2_w03_g χ n) x‖ ≤ 2 ^ j * M :=
        mul_le_mul h2 h1' (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have h3 := hle.trans (Finset.sum_le_sum hb)
    have h4 : ‖iteratedFDeriv ℝ j (fun y => s21k2_w03_g χ n y * f y) x‖ ^ 2 ≤
        (∑ i ∈ Finset.range (j + 1), (2 : ℝ) ^ j * M * ‖iteratedFDeriv ℝ (j - i) f x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h3 2
    refine h4.trans ?_
    refine (sq_sum_le_card_mul_sum_sq).trans ?_
    rw [Finset.card_range]
    have h5 : ∑ i ∈ Finset.range (j + 1), ((2 : ℝ) ^ j * M * ‖iteratedFDeriv ℝ (j - i) f x‖) ^ 2 ≤
        4 ^ m * M ^ 2 * HRS.MP.RdInit.mriG m f x := by
      have : ∀ i ∈ Finset.range (j + 1), ((2 : ℝ) ^ j * M * ‖iteratedFDeriv ℝ (j - i) f x‖) ^ 2 =
          (4 : ℝ) ^ j * M ^ 2 * ‖iteratedFDeriv ℝ (j - i) f x‖ ^ 2 := by
        intro i _
        rw [show (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
        ring
      have hrefl : ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) f x‖ ^ 2 =
          ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i f x‖ ^ 2 := by
        have := Finset.sum_range_reflect (fun i => ‖iteratedFDeriv ℝ i f x‖ ^ 2) (j + 1)
        simpa using this
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hrefl]
      have h6 : ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ i f x‖ ^ 2 ≤ HRS.MP.RdInit.mriG m f x := by
        unfold HRS.MP.RdInit.mriG
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (by omega)) fun i _ _ => sq_nonneg _
      have h7 : (4 : ℝ) ^ j ≤ 4 ^ m := pow_le_pow_right₀ (by norm_num) hj
      exact mul_le_mul (mul_le_mul_of_nonneg_right h7 (sq_nonneg _)) h6
        (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity)
    have h8 : ((j + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hj
    exact le_trans (mul_le_mul h8 h5 (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity))
      (le_of_eq (by ring))
  · rw [Set.indicator_of_notMem hx]
    have hx' : ‖x‖ < (n : ℝ) + 1 := by simpa using hx
    have hb : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (s21k2_w03_g χ n) x‖ *
        ‖iteratedFDeriv ℝ (j - i) f x‖ ≤ 0 := by
      intro i hi
      rw [s21k2_w03_g_vanish h1 n i hx']
      simp
    have h3 := hle.trans (Finset.sum_nonpos hb)
    have : ‖iteratedFDeriv ℝ j (fun y => s21k2_w03_g χ n y * f y) x‖ = 0 := le_antisymm h3 (norm_nonneg _)
    rw [this]; simp

/-- the sum of the squared ordered partial derivatives of order `<= r` -/
def s21k2_w03_F {d : ℕ} (r : ℕ) (f : HRS.Euc d → ℝ) (x : HRS.Euc d) : ℝ :=
  ∑ i ∈ Finset.range (r + 1), ∑ idx : Fin i → Fin d, (HRS.Whole.partialDeriv idx f x) ^ 2

theorem s21k2_w03_mriG_le {d : ℕ} (r : ℕ) (f : HRS.Euc d → ℝ) (x : HRS.Euc d) :
    HRS.MP.RdInit.mriG r f x ≤ ((d : ℝ) + 1) ^ r * s21k2_w03_F r f x := by
  unfold HRS.MP.RdInit.mriG s21k2_w03_F
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have h := HRS.MP.RdInit.mri_norm_sq_le (iteratedFDeriv ℝ i f x)
  have hir : i ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hd : (d : ℝ) ^ i ≤ ((d : ℝ) + 1) ^ r :=
    (pow_le_pow_left₀ (by positivity) (by linarith) i).trans
      (pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) hir)
  refine h.trans (mul_le_mul hd le_rfl (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity))

theorem s21k2_w03_pointwise {d : ℕ} {χ : HRS.Euc d → ℝ} (hχ : ∀ k : ℕ, ContDiff ℝ k χ)
    (h1 : ∀ x, ‖x‖ ≤ 1 → χ x = 1) {M : ℝ} (hM0 : 0 ≤ M) (r : ℕ)
    (hM : ∀ n : ℕ, ∀ k ≤ r, ∀ x, ‖iteratedFDeriv ℝ k (s21k2_w03_g χ n) x‖ ≤ M)
    {f : HRS.Euc d → ℝ} (hf : ContDiff ℝ r f) (n : ℕ) {j : ℕ} (hj : j ≤ r) (idx : Fin j → Fin d)
    (x : HRS.Euc d) :
    (HRS.Whole.partialDeriv idx (fun y => s21k2_w03_g χ n y * f y) x) ^ 2 ≤
      {y : HRS.Euc d | (n : ℝ) + 1 ≤ ‖y‖}.indicator
        (fun y => ((r + 1 : ℕ) : ℝ) * 4 ^ r * M ^ 2 * ((d : ℝ) + 1) ^ r * s21k2_w03_F r f y) x := by
  have h0 : (HRS.Whole.partialDeriv idx (fun y => s21k2_w03_g χ n y * f y) x) ^ 2 ≤
      ‖iteratedFDeriv ℝ j (fun y => s21k2_w03_g χ n y * f y) x‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (HRS.MP.RdInit.mri_abs_partialDeriv_le idx _ x) 2
  refine h0.trans ((s21k2_w03_leibniz hχ h1 hM0 r hM hf n hj x).trans ?_)
  by_cases hx : x ∈ {y : HRS.Euc d | (n : ℝ) + 1 ≤ ‖y‖}
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    have := s21k2_w03_mriG_le r f x
    have hc : (0 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) * 4 ^ r * M ^ 2 := by positivity
    calc ((r + 1 : ℕ) : ℝ) * 4 ^ r * M ^ 2 * HRS.MP.RdInit.mriG r f x
        ≤ ((r + 1 : ℕ) : ℝ) * 4 ^ r * M ^ 2 * (((d : ℝ) + 1) ^ r * s21k2_w03_F r f x) :=
          mul_le_mul_of_nonneg_left this hc
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

end HRS.MS.R26T3
