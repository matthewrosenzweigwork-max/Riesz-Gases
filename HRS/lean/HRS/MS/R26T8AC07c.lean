import HRS.MS.R26T8AC07b
import HRS.MS.R26T8AC08

/-!
# S8.2 observed-time layer, packet T8A.C07c: the twofold critical convolution bound as a lintegral

`q(u) ≤ C1 ‖u‖^{-d/2} 1_{‖u‖ ≤ r0} + K` for `u ≠ 0`; expanding `(A+K)(A'+K)` and using `ρ ≤ G`, `∫ρ = 1`, the radial integral
of `A` and the two-centre bound of C07a/b gives `∫⁻ ρ(z) q(x-z) q(z-y) dz ≤ C (1 + |log min(1,‖x-y‖)|)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_c07c_pole_le (d : ℕ) (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ r0 C1 K : ℝ, 0 < r0 ∧ r0 ≤ 1 ∧ 0 ≤ C1 ∧ 0 ≤ K ∧ ∀ u : Euc d, u ≠ 0 →
      q u ≤ C1 * (Set.Ioc 0 r0).indicator (fun r => r ^ (-criticalS d)) ‖u‖ + K := by
  obtain ⟨r0, c1, C1, hr0, hr01, hc1, hnear⟩ := hq.near
  obtain ⟨K, hK0, hK⟩ := r26t8a_c08_bound_outside d q hq hr0
  refine ⟨r0, max C1 0, K, hr0, hr01, le_max_right _ _, hK0, fun u hu => ?_⟩
  have hupos : 0 < ‖u‖ := norm_pos_iff.2 hu
  by_cases h : ‖u‖ ≤ r0
  · rw [indicator_of_mem (show ‖u‖ ∈ Set.Ioc 0 r0 from ⟨hupos, h⟩)]
    have := (hnear u hupos h).2
    have h2 : C1 * ‖u‖ ^ (-criticalS d) ≤ max C1 0 * ‖u‖ ^ (-criticalS d) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hupos.le _)
    linarith
  · push_neg at h
    rw [indicator_of_notMem (fun hh => absurd hh.2 (not_le.2 h)), mul_zero, zero_add]
    exact hK u h.le

theorem r26t8a_c07c_twofold (d : ℕ) (hd : 2 ≤ d) (q : Euc d → ℝ) (hq : ShortRangePole d q)
    (G : ℝ) (hG : 0 < G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, HRS.Whole.IsProbDensity rho → (∀ y, rho y ≤ G) →
      ∀ x y : Euc d, x ≠ y →
      ∫⁻ z, ENNReal.ofReal (rho z) * ENNReal.ofReal (q (x - z) * q (z - y)) ≤
        ENNReal.ofReal (C * (1 + |Real.log (min 1 ‖x - y‖)|)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨r0, C1, K, hr0, hr01, hC1, hK0, hqle⟩ := r26t8a_c07c_pole_le d q hq
  set e : ℝ := (d : ℝ) / 2 with he
  have he0 : 0 < e := by positivity
  have hqle' : ∀ u : Euc d, u ≠ 0 →
      q u ≤ C1 * (Set.Ioc 0 r0).indicator (fun r => r ^ (-e)) ‖u‖ + K := hqle
  set ω : ℝ := r26t8a_c08a_const d with hω
  have hω0 : 0 ≤ ω := r26t8a_c08a_const_nonneg d
  set Ind : ℝ → ℝ := (Set.Ioc 0 r0).indicator (fun r => r ^ (-e)) with hInd
  have hInd0 : ∀ r, 0 ≤ Ind r := fun r =>
    indicator_nonneg (fun r hr => Real.rpow_nonneg hr.1.le _) r
  have hIndle : ∀ r : ℝ, 0 ≤ r → Ind r ≤ r ^ (-e) := fun r hr => by
    by_cases h : r ∈ Set.Ioc 0 r0
    · rw [hInd, indicator_of_mem h]
    · rw [hInd, indicator_of_notMem h]
      exact Real.rpow_nonneg hr _
  set Ap : Euc d → ℝ := fun u => C1 * Ind ‖u‖ with hAp
  have hAp0 : ∀ u, 0 ≤ Ap u := fun u => mul_nonneg hC1 (hInd0 _)
  have hApm : Measurable Ap :=
    measurable_const.mul (((measurable_id.pow_const (-e)).indicator measurableSet_Ioc).comp measurable_norm)
  have hqm : Measurable q := hq.measurable
  -- constants
  refine ⟨G * C1 ^ 2 * ω * (2 / e + 4 ^ d / d + 2 ^ e) + 2 * G * K * C1 * ω * (1 / e) + K ^ 2,
    by positivity, ?_⟩
  intro rho hrho hρG x y hxy
  set D : ℝ := ‖x - y‖ with hD
  have hDpos : 0 < D := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hρm : Measurable rho := hrho.measurable
  have hρ0 : ∀ z, 0 ≤ rho z := hrho.nonneg
  have hρi : Integrable rho := by
    by_contra h
    have := hrho.integral_one
    rw [integral_undef h] at this
    exact zero_ne_one this
  have hmass : ∫⁻ y, ENNReal.ofReal (rho y) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρ0), hrho.integral_one]
    simp
  have hρE : Measurable fun y : Euc d => ENNReal.ofReal (rho y) := ENNReal.measurable_ofReal.comp hρm
  have hnull : ∀ᵐ z ∂(volume : Measure (Euc d)), z ≠ x ∧ z ≠ y := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd1⟩⟩
    have h0 : ∀ᵐ z ∂(volume : Measure (Euc d)), z ≠ x := by rw [ae_iff]; simp
    have h1 : ∀ᵐ z ∂(volume : Measure (Euc d)), z ≠ y := by rw [ae_iff]; simp
    filter_upwards [h0, h1] with z a b using ⟨a, b⟩
  have hqge : ∀ u, 0 ≤ q u := hq.nonneg
  -- functions
  set f1 : Euc d → ℝ≥0∞ := fun z => ENNReal.ofReal (Ap (x - z) * Ap (z - y)) with hf1
  set f2 : Euc d → ℝ≥0∞ := fun z => ENNReal.ofReal (K * Ap (x - z)) with hf2
  set f3 : Euc d → ℝ≥0∞ := fun z => ENNReal.ofReal (K * Ap (z - y)) with hf3
  have hApx : Measurable fun z : Euc d => Ap (x - z) := hApm.comp (measurable_const.sub measurable_id)
  have hApy : Measurable fun z : Euc d => Ap (z - y) := hApm.comp (measurable_id.sub_const y)
  have hf1m : Measurable f1 := ENNReal.measurable_ofReal.comp (hApx.mul hApy)
  have hf2m : Measurable f2 := ENNReal.measurable_ofReal.comp (measurable_const.mul hApx)
  have hf3m : Measurable f3 := ENNReal.measurable_ofReal.comp (measurable_const.mul hApy)
  have hpt : ∀ᵐ z ∂(volume : Measure (Euc d)),
      ENNReal.ofReal (rho z) * ENNReal.ofReal (q (x - z) * q (z - y)) ≤
        ENNReal.ofReal (rho z) * (f1 z + f2 z + f3 z + ENNReal.ofReal (K ^ 2)) := by
    filter_upwards [hnull] with z ⟨hzx, hzy⟩
    refine mul_le_mul' le_rfl ?_
    have h1 : x - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzx)
    have h2 : z - y ≠ 0 := sub_ne_zero.2 hzy
    have e1 := hqle' (x - z) h1
    have e2 := hqle' (z - y) h2
    have hprod : q (x - z) * q (z - y) ≤
        Ap (x - z) * Ap (z - y) + K * Ap (x - z) + K * Ap (z - y) + K ^ 2 := by
      calc q (x - z) * q (z - y) ≤ (Ap (x - z) + K) * (Ap (z - y) + K) :=
            mul_le_mul e1 e2 (hqge _) (add_nonneg (hAp0 _) hK0)
        _ = _ := by ring
    calc ENNReal.ofReal (q (x - z) * q (z - y))
        ≤ ENNReal.ofReal (Ap (x - z) * Ap (z - y) + K * Ap (x - z) + K * Ap (z - y) + K ^ 2) :=
          ENNReal.ofReal_le_ofReal hprod
      _ = f1 z + f2 z + f3 z + ENNReal.ofReal (K ^ 2) := by
          have a1 : 0 ≤ Ap (x - z) * Ap (z - y) := mul_nonneg (hAp0 _) (hAp0 _)
          have a2 : 0 ≤ K * Ap (x - z) := mul_nonneg hK0 (hAp0 _)
          have a3 : 0 ≤ K * Ap (z - y) := mul_nonneg hK0 (hAp0 _)
          rw [ENNReal.ofReal_add (add_nonneg (add_nonneg a1 a2) a3) (sq_nonneg K),
            ENNReal.ofReal_add (add_nonneg a1 a2) a3, ENNReal.ofReal_add a1 a2]
  -- the integration
  have hmeas_rho : ∀ f : Euc d → ℝ≥0∞, Measurable f → Measurable fun z => ENNReal.ofReal (rho z) * f z :=
    fun f hf => hρE.mul hf
  have hexp : ∫⁻ z, ENNReal.ofReal (rho z) * (f1 z + f2 z + f3 z + ENNReal.ofReal (K ^ 2)) =
      (∫⁻ z, ENNReal.ofReal (rho z) * f1 z) + (∫⁻ z, ENNReal.ofReal (rho z) * f2 z) +
        (∫⁻ z, ENNReal.ofReal (rho z) * f3 z) + ∫⁻ z, ENNReal.ofReal (rho z) * ENNReal.ofReal (K ^ 2) := by
    simp only [mul_add]
    rw [lintegral_add_right _ (hmeas_rho _ measurable_const), lintegral_add_right _ (hmeas_rho _ hf3m),
      lintegral_add_right _ (hmeas_rho _ hf2m)]
  have hbd : ∀ f : Euc d → ℝ≥0∞, Measurable f →
      ∫⁻ z, ENNReal.ofReal (rho z) * f z ≤ ENNReal.ofReal G * ∫⁻ z, f z := fun f hf => by
    rw [← lintegral_const_mul _ hf]
    exact lintegral_mono fun z => mul_le_mul' (ENNReal.ofReal_le_ofReal (hρG z)) le_rfl
  -- radial piece
  have hIndm : Measurable fun w : Euc d => ENNReal.ofReal (Ind ‖w‖) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_id.pow_const (-e)).indicator measurableSet_Ioc).comp measurable_norm)
  have hrad0 : ∫⁻ w : Euc d, ENNReal.ofReal (Ind ‖w‖) ≤ ENNReal.ofReal (ω * (1 / e)) := by
    have := r26t8a_c08a_radial d hd1 (p := e) (ε := 0) (δ := r0) le_rfl hr0.le
      (Or.inr (by rw [he]; linarith))
    have hex : (d : ℝ) - 1 - e + 1 = e := by rw [he]; ring
    have hI : ∫ r in (0 : ℝ)..r0, r ^ ((d : ℝ) - 1 - e) = r0 ^ e / e := by
      rw [integral_rpow (Or.inl (by rw [he]; linarith)), hex, Real.zero_rpow he0.ne']; simp
    rw [hI] at this
    refine this.trans_le (ENNReal.ofReal_le_ofReal ?_)
    have : r0 ^ e ≤ 1 := Real.rpow_le_one hr0.le hr01 he0.le
    have h2 : r0 ^ e / e ≤ 1 / e := div_le_div_of_nonneg_right this he0.le
    exact mul_le_mul_of_nonneg_left h2 hω0
  have hAplin : ∀ (c : ℝ), 0 ≤ c → ∫⁻ w : Euc d, ENNReal.ofReal (c * Ap w) ≤
      ENNReal.ofReal (c * C1) * ENNReal.ofReal (ω * (1 / e)) := fun c hc => by
    have : ∀ w : Euc d, ENNReal.ofReal (c * Ap w) = ENNReal.ofReal (c * C1) * ENNReal.ofReal (Ind ‖w‖) :=
      fun w => by
        rw [← ENNReal.ofReal_mul (mul_nonneg hc hC1)]
        congr 1; simp only [hAp]; ring
    simp_rw [this]
    rw [lintegral_const_mul _ hIndm]
    exact mul_le_mul' le_rfl hrad0
  -- term (ii) and (iii)
  have t2 : ∫⁻ z, f2 z ≤ ENNReal.ofReal (K * C1) * ENNReal.ofReal (ω * (1 / e)) := by
    rw [← lintegral_add_left_eq_self f2 x]
    have : ∀ w : Euc d, f2 (x + w) = ENNReal.ofReal (K * Ap w) := fun w => by
      simp only [hf2, hAp]
      rw [show x - (x + w) = -w by abel, norm_neg]
    simp_rw [this]
    exact hAplin K hK0
  have t3 : ∫⁻ z, f3 z ≤ ENNReal.ofReal (K * C1) * ENNReal.ofReal (ω * (1 / e)) := by
    rw [← lintegral_add_left_eq_self f3 y]
    have : ∀ w : Euc d, f3 (y + w) = ENNReal.ofReal (K * Ap w) := fun w => by
      simp only [hf3, hAp]
      rw [show y + w - y = w by abel]
    simp_rw [this]
    exact hAplin K hK0
  -- term (i)
  have t1 : ∫⁻ z, f1 z ≤ ENNReal.ofReal (C1 ^ 2) *
      ENNReal.ofReal (ω * (2 / e + 4 ^ d / d + 2 ^ e * |Real.log (min 1 D)|)) := by
    rw [← lintegral_add_left_eq_self f1 x]
    set e' : Euc d := y - x with he'
    have hnorm : ‖e'‖ = D := by rw [he', hD, norm_sub_rev]
    have hpt1 : ∀ w : Euc d, f1 (x + w) ≤ ENNReal.ofReal (C1 ^ 2) *
        ENNReal.ofReal (Ind ‖w‖ * ‖w - e'‖ ^ (-e)) := fun w => by
      simp only [hf1, hAp]
      rw [show x - (x + w) = -w by abel, norm_neg, show x + w - y = w - e' by rw [he']; abel,
        ← ENNReal.ofReal_mul (sq_nonneg C1)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : Ind ‖w - e'‖ ≤ ‖w - e'‖ ^ (-e) := hIndle _ (norm_nonneg _)
      calc C1 * Ind ‖w‖ * (C1 * Ind ‖w - e'‖) = C1 ^ 2 * (Ind ‖w‖ * Ind ‖w - e'‖) := by ring
        _ ≤ C1 ^ 2 * (Ind ‖w‖ * ‖w - e'‖ ^ (-e)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (hInd0 _)) (sq_nonneg C1)
    have hmeas1 : Measurable fun w : Euc d => ENNReal.ofReal (Ind ‖w‖ * ‖w - e'‖ ^ (-e)) :=
      ENNReal.measurable_ofReal.comp
        ((((measurable_id.pow_const (-e)).indicator measurableSet_Ioc).comp measurable_norm).mul
          (((measurable_id.sub_const e').norm).pow_const (-e)))
    calc ∫⁻ w : Euc d, f1 (x + w) ≤ ∫⁻ w : Euc d, ENNReal.ofReal (C1 ^ 2) *
          ENNReal.ofReal (Ind ‖w‖ * ‖w - e'‖ ^ (-e)) := lintegral_mono hpt1
      _ = ENNReal.ofReal (C1 ^ 2) * ∫⁻ w : Euc d, ENNReal.ofReal (Ind ‖w‖ * ‖w - e'‖ ^ (-e)) :=
          lintegral_const_mul _ hmeas1
      _ ≤ _ := by
          refine mul_le_mul' le_rfl ?_
          refine (r26t8a_c07a_two_center d hd1 (p := e) (p' := e) (R := r0) (D := D)
            he0.le (by rw [he]; linarith) he0.le (by rw [he]; linarith) hDpos e' hnorm).trans ?_
          exact r26t8a_c07b_eval d hd1 hDpos hr01
  -- term (iv)
  have t4 : ∫⁻ z, ENNReal.ofReal (rho z) * ENNReal.ofReal (K ^ 2) = ENNReal.ofReal (K ^ 2) := by
    rw [lintegral_mul_const _ hρE, hmass, one_mul]
  -- assemble
  calc ∫⁻ z, ENNReal.ofReal (rho z) * ENNReal.ofReal (q (x - z) * q (z - y))
      ≤ ∫⁻ z, ENNReal.ofReal (rho z) * (f1 z + f2 z + f3 z + ENNReal.ofReal (K ^ 2)) :=
        lintegral_mono_ae hpt
    _ = _ := hexp
    _ ≤ ENNReal.ofReal G * (ENNReal.ofReal (C1 ^ 2) *
          ENNReal.ofReal (ω * (2 / e + 4 ^ d / d + 2 ^ e * |Real.log (min 1 D)|))) +
        ENNReal.ofReal G * (ENNReal.ofReal (K * C1) * ENNReal.ofReal (ω * (1 / e))) +
        ENNReal.ofReal G * (ENNReal.ofReal (K * C1) * ENNReal.ofReal (ω * (1 / e))) +
        ENNReal.ofReal (K ^ 2) := by
        rw [t4]
        refine add_le_add (add_le_add (add_le_add ((hbd f1 hf1m).trans (mul_le_mul' le_rfl t1))
          ((hbd f2 hf2m).trans (mul_le_mul' le_rfl t2))) ((hbd f3 hf3m).trans (mul_le_mul' le_rfl t3)))
          le_rfl
    _ = ENNReal.ofReal (G * (C1 ^ 2 * (ω * (2 / e + 4 ^ d / d + 2 ^ e * |Real.log (min 1 D)|))) +
          G * (K * C1 * (ω * (1 / e))) + G * (K * C1 * (ω * (1 / e))) + K ^ 2) := by
        have hL : 0 ≤ |Real.log (min 1 D)| := abs_nonneg _
        have p1 : 0 ≤ ω * (2 / e + 4 ^ d / d + 2 ^ e * |Real.log (min 1 D)|) := by positivity
        have p2 : 0 ≤ ω * (1 / e) := by positivity
        rw [← ENNReal.ofReal_mul (sq_nonneg C1), ← ENNReal.ofReal_mul hG.le,
          ← ENNReal.ofReal_mul (mul_nonneg hK0 hC1), ← ENNReal.ofReal_mul hG.le,
          ← ENNReal.ofReal_add (mul_nonneg hG.le (mul_nonneg (sq_nonneg C1) p1))
            (mul_nonneg hG.le (mul_nonneg (mul_nonneg hK0 hC1) p2)),
          ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hG.le (mul_nonneg (sq_nonneg C1) p1))
            (mul_nonneg hG.le (mul_nonneg (mul_nonneg hK0 hC1) p2)))
            (mul_nonneg hG.le (mul_nonneg (mul_nonneg hK0 hC1) p2)),
          ← ENNReal.ofReal_add (by positivity) (sq_nonneg K)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hL : 0 ≤ |Real.log (min 1 D)| := abs_nonneg _
        have hA : 0 ≤ 2 / e + 4 ^ d / d := by positivity
        have h2e : (0 : ℝ) ≤ 2 ^ e := Real.rpow_nonneg (by norm_num) _
        have hM : 0 ≤ G * C1 ^ 2 * ω := by positivity
        have hN : 0 ≤ 2 * G * K * C1 * ω * (1 / e) := by positivity
        nlinarith [mul_nonneg hM (mul_nonneg hA hL), mul_nonneg hM h2e, mul_nonneg hN hL,
          mul_nonneg (sq_nonneg K) hL]

end HRS.MS.R26T8A
