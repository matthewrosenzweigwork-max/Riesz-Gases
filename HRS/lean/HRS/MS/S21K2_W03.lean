import HRS.MS.S21K2_W03A

/-!
# S21K2 W03 -- spatial cutoffs approximate every frozen weighted test (R26-T3.W03)

Contract verbatim (qualified names).  `fR n x = chi (x / (n+1)) * f x`; the difference is `(chi_n - 1) f`, whose ordered
partial derivatives are bounded pointwise by `1_{|x| >= n+1} * K * F` (file `S21K2_W03A`), and the tail integral of the
integrable weighted function `F` tends to zero by dominated convergence.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s21k2_w03_tail {d : ℕ} (G : HRS.Euc d → ℝ≥0∞) (hG : Measurable G) (hfin : ∫⁻ x, G x ≠ ∞) :
    Tendsto (fun n : ℕ => ∫⁻ x, {y : HRS.Euc d | (n : ℝ) + 1 ≤ ‖y‖}.indicator G x) atTop (𝓝 0) := by
  have h := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun (n : ℕ) (x : HRS.Euc d) => {y : HRS.Euc d | (n : ℝ) + 1 ≤ ‖y‖}.indicator G x)
    (f := fun _ => 0) G
    (fun n => hG.indicator (isClosed_le continuous_const continuous_norm).measurableSet)
    (fun n => Eventually.of_forall fun x => Set.indicator_le_self _ _ x) hfin ?_
  · simpa using h
  · refine Eventually.of_forall fun x => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [Set.indicator_of_notMem]
    simp only [Set.mem_setOf_eq, not_le]
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith

/-- the weighted sum of all squared ordered partial derivatives, in `ℝ≥0∞` -/
def s21k2_w03_G {d : ℕ} (r : ℕ) (P : ℝ) (f : HRS.Euc d → ℝ) (y : HRS.Euc d) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (r + 1), ∑ i : Fin j → Fin d,
    ENNReal.ofReal (HRS.Whole.jbracket y ^ (-2 * P) * (HRS.Whole.partialDeriv i f y) ^ 2)

theorem s21k2_w03_G_meas {d r : ℕ} (P : ℝ) {f : HRS.Euc d → ℝ} (hf : ContDiff ℝ r f) :
    Measurable (s21k2_w03_G r P f) := by
  have hjb : Continuous (HRS.Whole.jbracket (d := d)) := by unfold HRS.Whole.jbracket; fun_prop
  unfold s21k2_w03_G
  refine Finset.measurable_sum _ fun j hj => Finset.measurable_sum _ fun i _ => ?_
  exact ((hjb.measurable.pow_const _).mul
    ((s21g2_w01_pd_cont hf (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) i).measurable.pow_const _)).ennreal_ofReal

theorem s21k2_w03_G_int {d r : ℕ} (P : ℝ) {f : HRS.Euc d → ℝ} (hf : ContDiff ℝ r f) :
    ∫⁻ y, s21k2_w03_G r P f y = (HRS.Whole.weightedSobolevE r P f) ^ (2 : ℝ) := by
  have hjb : Continuous (HRS.Whole.jbracket (d := d)) := by unfold HRS.Whole.jbracket; fun_prop
  unfold s21k2_w03_G HRS.Whole.weightedSobolevE
  rw [← ENNReal.rpow_mul]
  norm_num
  rw [lintegral_finsetSum _ fun j hj => Finset.measurable_sum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [lintegral_finsetSum _ fun i _ => ?_]
    exact ((hjb.measurable.pow_const _).mul
      ((s21g2_w01_pd_cont hf (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) i).measurable.pow_const _)).ennreal_ofReal
  · exact ((hjb.measurable.pow_const _).mul
      ((s21g2_w01_pd_cont hf (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) i).measurable.pow_const _)).ennreal_ofReal

theorem s21k2_w03_G_eq {d : ℕ} (r : ℕ) (P : ℝ) (f : HRS.Euc d → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (y : HRS.Euc d) :
    ENNReal.ofReal (HRS.Whole.jbracket y ^ (-2 * P) * (K * s21k2_w03_F r f y)) =
      ENNReal.ofReal K * s21k2_w03_G r P f y := by
  have hj : 0 ≤ HRS.Whole.jbracket y ^ (-2 * P) := by unfold HRS.Whole.jbracket; positivity
  unfold s21k2_w03_F s21k2_w03_G
  have e : HRS.Whole.jbracket y ^ (-2 * P) * (K * ∑ i ∈ Finset.range (r + 1), ∑ idx : Fin i → Fin d,
      (HRS.Whole.partialDeriv idx f y) ^ 2) = K * ∑ i ∈ Finset.range (r + 1), ∑ idx : Fin i → Fin d,
      (HRS.Whole.jbracket y ^ (-2 * P) * (HRS.Whole.partialDeriv idx f y) ^ 2) := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun idx _ => by ring
  rw [e, ENNReal.ofReal_mul hK, ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun idx _ => by positivity]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun idx _ => by positivity]

theorem r26t3_weighted_cutoff {d r : ℕ} (P : ℝ) (f : HRS.Euc d → ℝ)
    (hf : HRS.Whole.IsR2WeightedTest r P f) :
    ∃ fR : ℕ → HRS.Euc d → ℝ,
      (∀ n, ContDiff ℝ r (fR n) ∧ HasCompactSupport (fR n)) ∧
      Tendsto (fun n => HRS.Whole.weightedSobolevE r P (fR n - f)) atTop (𝓝 0) := by
  obtain ⟨χ, hχ, h1, h2⟩ := s21k2_w03_cutoff d
  obtain ⟨M, hM0, hM⟩ := s21k2_w03_g_bound hχ h2 r
  have hmul : ∀ n : ℕ, ContDiff ℝ r (fun x : HRS.Euc d => χ (((n : ℝ) + 1)⁻¹ • x) * f x) := fun n =>
    ((hχ r).comp (contDiff_const_smul _)).mul hf.1
  have hdiff : ∀ n : ℕ, (fun x : HRS.Euc d => χ (((n : ℝ) + 1)⁻¹ • x) * f x) - f =
      fun y => s21k2_w03_g χ n y * f y := fun n => by
    funext y; simp only [Pi.sub_apply, s21k2_w03_g]; ring
  refine ⟨fun n x => χ (((n : ℝ) + 1)⁻¹ • x) * f x, fun n => ⟨hmul n, ?_⟩, ?_⟩
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : HRS.Euc d) (2 * ((n : ℝ) + 1))) fun x hx => ?_
    have hx' : 2 * ((n : ℝ) + 1) < ‖x‖ := by simpa using hx
    have : 2 ≤ ‖((n : ℝ) + 1)⁻¹ • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), le_inv_mul_iff₀ (by positivity)]
      linarith
    simp [h2 _ this]
  · set K : ℝ := ((r + 1 : ℕ) : ℝ) * 4 ^ r * M ^ 2 * ((d : ℝ) + 1) ^ r with hK
    have hK0 : 0 ≤ K := by positivity
    have hfin : ∫⁻ y, ENNReal.ofReal K * s21k2_w03_G r P f y ≠ ∞ := by
      rw [lintegral_const_mul _ (s21k2_w03_G_meas P hf.1), s21k2_w03_G_int P hf.1]
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
      refine (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hf.2.ne).ne
    have htail := s21k2_w03_tail (fun y => ENNReal.ofReal K * s21k2_w03_G r P f y)
      ((s21k2_w03_G_meas P hf.1).const_mul _) hfin
    -- termwise bound
    have hterm : ∀ n : ℕ, ∀ j ∈ Finset.range (r + 1), ∀ i : Fin j → Fin d,
        ∫⁻ x, ENNReal.ofReal (HRS.Whole.jbracket x ^ (-2 * P) *
          (HRS.Whole.partialDeriv i (fun y => s21k2_w03_g χ n y * f y) x) ^ 2) ≤
        ∫⁻ x, {y : HRS.Euc d | (n : ℝ) + 1 ≤ ‖y‖}.indicator
          (fun y => ENNReal.ofReal K * s21k2_w03_G r P f y) x := by
      intro n j hj i
      refine lintegral_mono fun x => ?_
      have hjr : j ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hp := s21k2_w03_pointwise hχ h1 hM0 r hM hf.1 n hjr i x
      have hjb : 0 ≤ HRS.Whole.jbracket x ^ (-2 * P) := by unfold HRS.Whole.jbracket; positivity
      by_cases hx : x ∈ {y : HRS.Euc d | (n : ℝ) + 1 ≤ ‖y‖}
      · rw [Set.indicator_of_mem hx]
        rw [Set.indicator_of_mem hx] at hp
        calc _ ≤ ENNReal.ofReal (HRS.Whole.jbracket x ^ (-2 * P) * (K * s21k2_w03_F r f x)) :=
              ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by simpa [hK] using hp) hjb)
          _ = _ := s21k2_w03_G_eq r P f hK0 x
      · rw [Set.indicator_of_notMem hx]
        rw [Set.indicator_of_notMem hx] at hp
        have : (HRS.Whole.partialDeriv i (fun y => s21k2_w03_g χ n y * f y) x) ^ 2 = 0 :=
          le_antisymm hp (sq_nonneg _)
        simp [this]
    have hup : ∀ n : ℕ, HRS.Whole.weightedSobolevE r P (fun x : HRS.Euc d => χ (((n : ℝ) + 1)⁻¹ • x) * f x - f x) ≤
        ((∑ j ∈ Finset.range (r + 1), ∑ _i : Fin j → Fin d, (1 : ℝ≥0∞)) *
          ∫⁻ x, {y : HRS.Euc d | (n : ℝ) + 1 ≤ ‖y‖}.indicator
            (fun y => ENNReal.ofReal K * s21k2_w03_G r P f y) x) ^ (1 / 2 : ℝ) := by
      intro n
      have e : (fun x : HRS.Euc d => χ (((n : ℝ) + 1)⁻¹ • x) * f x - f x) =
          fun y => s21k2_w03_g χ n y * f y := by
        have := hdiff n
        funext y
        have := congrFun this y
        simpa using this
      rw [e]
      unfold HRS.Whole.weightedSobolevE
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => by rw [one_mul]; exact hterm n j hj i
    have hlim : Tendsto (fun n : ℕ => ((∑ j ∈ Finset.range (r + 1), ∑ _i : Fin j → Fin d, (1 : ℝ≥0∞)) *
          ∫⁻ x, {y : HRS.Euc d | (n : ℝ) + 1 ≤ ‖y‖}.indicator
            (fun y => ENNReal.ofReal K * s21k2_w03_G r P f y) x) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have hN : (∑ j ∈ Finset.range (r + 1), ∑ _i : Fin j → Fin d, (1 : ℝ≥0∞)) ≠ ∞ := by
        simp [ENNReal.sum_eq_top]
      have h0 := (ENNReal.Tendsto.const_mul htail (Or.inr hN))
      rw [mul_zero] at h0
      have h1 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h0
      rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) ?_
    intro n
    exact hup n

end HRS.MS.R26T3
