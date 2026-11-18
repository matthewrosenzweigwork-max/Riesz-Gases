import HRS.MS.R26T8AC07e

/-!
# S8.2 observed-time layer, packet T8A.C07f: outer integral of the threefold critical convolution bound
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_c07f_outer (d : ℕ) (hd : 2 ≤ d) (q : Euc d → ℝ) (hq : ShortRangePole d q)
    (G : ℝ) (hG : 0 < G) :
    ∃ C3 : ℝ, 0 ≤ C3 ∧ ∀ rho : Euc d → ℝ, HRS.Whole.IsProbDensity rho → (∀ y, rho y ≤ G) →
      ∀ x y : Euc d,
      ∫⁻ z, ENNReal.ofReal (rho z) *
        (ENNReal.ofReal (q (x - z)) * ENNReal.ofReal (1 + |Real.log (min 1 ‖z - y‖)|)) ≤
        ENNReal.ofReal C3 := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨r0, C1, K, hr0, hr01, hC1, hK0, hqle⟩ := r26t8a_c07c_pole_le d q hq
  set e : ℝ := (d : ℝ) / 2 with he
  have he0 : 0 < e := by positivity
  set θ : ℝ := (d : ℝ) / 4 with hθ
  have hθ0 : 0 < θ := by positivity
  have hdθ : 0 < (d : ℝ) - θ := by rw [hθ]; linarith
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
  set Lf : Euc d → ℝ := fun u => |Real.log (min 1 ‖u‖)| with hLf
  have hLfm : Measurable Lf :=
    ((Real.measurable_log.comp (measurable_const.min measurable_norm))).abs
  have hLf0 : ∀ u, 0 ≤ Lf u := fun u => abs_nonneg _
  set Cθ : ℝ := 1 / e + 1 / ((d : ℝ) - θ) + 4 ^ d / d + 2 ^ θ * (5 ^ θ / θ) with hCθ
  refine ⟨G * C1 * (ω * (1 / e)) + G * (C1 * (4 / d)) * (ω * Cθ) + K +
    G * (K * (4 / d)) * (ω * (1 / ((d : ℝ) - θ))), by positivity, ?_⟩
  intro rho hrho hρG x y
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
  have hnull : ∀ᵐ z ∂(volume : Measure (Euc d)), z ≠ x := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd1⟩⟩
    rw [ae_iff]; simp
  set g1 : Euc d → ℝ≥0∞ := fun z => ENNReal.ofReal (Ap (x - z)) with hg1
  set g2 : Euc d → ℝ≥0∞ := fun z => ENNReal.ofReal (Ap (x - z) * Lf (z - y)) with hg2
  set g4 : Euc d → ℝ≥0∞ := fun z => ENNReal.ofReal (K * Lf (z - y)) with hg4
  have hApx : Measurable fun z : Euc d => Ap (x - z) := hApm.comp (measurable_const.sub measurable_id)
  have hLy : Measurable fun z : Euc d => Lf (z - y) := hLfm.comp (measurable_id.sub_const y)
  have hg1m : Measurable g1 := ENNReal.measurable_ofReal.comp hApx
  have hg2m : Measurable g2 := ENNReal.measurable_ofReal.comp (hApx.mul hLy)
  have hg4m : Measurable g4 := ENNReal.measurable_ofReal.comp (measurable_const.mul hLy)
  have hpt : ∀ᵐ z ∂(volume : Measure (Euc d)),
      ENNReal.ofReal (rho z) * (ENNReal.ofReal (q (x - z)) * ENNReal.ofReal (1 + |Real.log (min 1 ‖z - y‖)|)) ≤
        ENNReal.ofReal (rho z) * (g1 z + g2 z + ENNReal.ofReal K + g4 z) := by
    filter_upwards [hnull] with z hzx
    refine mul_le_mul' le_rfl ?_
    have h1 : x - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzx)
    have e1 := hqle' (x - z) h1
    have hL := hLf0 (z - y)
    rw [← ENNReal.ofReal_mul (hq.nonneg _)]
    have hprod : q (x - z) * (1 + |Real.log (min 1 ‖z - y‖)|) ≤
        Ap (x - z) + Ap (x - z) * Lf (z - y) + K + K * Lf (z - y) := by
      calc q (x - z) * (1 + |Real.log (min 1 ‖z - y‖)|) ≤ (Ap (x - z) + K) * (1 + Lf (z - y)) :=
            mul_le_mul e1 le_rfl (by positivity) (add_nonneg (hAp0 _) hK0)
        _ = _ := by ring
    calc ENNReal.ofReal (q (x - z) * (1 + |Real.log (min 1 ‖z - y‖)|))
        ≤ ENNReal.ofReal (Ap (x - z) + Ap (x - z) * Lf (z - y) + K + K * Lf (z - y)) :=
          ENNReal.ofReal_le_ofReal hprod
      _ = g1 z + g2 z + ENNReal.ofReal K + g4 z := by
          have a1 := hAp0 (x - z)
          have a2 : 0 ≤ Ap (x - z) * Lf (z - y) := mul_nonneg a1 hL
          have a4 : 0 ≤ K * Lf (z - y) := mul_nonneg hK0 hL
          rw [ENNReal.ofReal_add (add_nonneg (add_nonneg a1 a2) hK0) a4,
            ENNReal.ofReal_add (add_nonneg a1 a2) hK0, ENNReal.ofReal_add a1 a2]
  have hmeas_rho : ∀ f : Euc d → ℝ≥0∞, Measurable f → Measurable fun z => ENNReal.ofReal (rho z) * f z :=
    fun f hf => hρE.mul hf
  have hexp : ∫⁻ z, ENNReal.ofReal (rho z) * (g1 z + g2 z + ENNReal.ofReal K + g4 z) =
      (∫⁻ z, ENNReal.ofReal (rho z) * g1 z) + (∫⁻ z, ENNReal.ofReal (rho z) * g2 z) +
        (∫⁻ z, ENNReal.ofReal (rho z) * ENNReal.ofReal K) + ∫⁻ z, ENNReal.ofReal (rho z) * g4 z := by
    simp only [mul_add]
    rw [lintegral_add_right _ (hmeas_rho _ hg4m), lintegral_add_right _ (hmeas_rho _ measurable_const),
      lintegral_add_right _ (hmeas_rho _ hg2m)]
  have hbd : ∀ f : Euc d → ℝ≥0∞, Measurable f →
      ∫⁻ z, ENNReal.ofReal (rho z) * f z ≤ ENNReal.ofReal G * ∫⁻ z, f z := fun f hf => by
    rw [← lintegral_const_mul _ hf]
    exact lintegral_mono fun z => mul_le_mul' (ENNReal.ofReal_le_ofReal (hρG z)) le_rfl
  have hIndm : Measurable fun w : Euc d => ENNReal.ofReal (Ind ‖w‖) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_id.pow_const (-e)).indicator measurableSet_Ioc).comp measurable_norm)
  -- (1)
  have s1 : ∫⁻ z, g1 z ≤ ENNReal.ofReal C1 * ENNReal.ofReal (ω * (1 / e)) := by
    rw [← lintegral_add_left_eq_self g1 x]
    have : ∀ w : Euc d, g1 (x + w) = ENNReal.ofReal C1 * ENNReal.ofReal (Ind ‖w‖) := fun w => by
      simp only [hg1, hAp]
      rw [show x - (x + w) = -w by abel, norm_neg, ← ENNReal.ofReal_mul hC1]
    simp_rw [this]
    rw [lintegral_const_mul _ hIndm]
    exact mul_le_mul' le_rfl (r26t8a_c07e_radialA d hd1 hr0 hr01)
  -- (4)
  have hLθ : Measurable fun w : Euc d => ENNReal.ofReal
      ((Set.Ioc 0 1).indicator (fun r => r ^ (-θ)) ‖w‖) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_id.pow_const (-θ)).indicator measurableSet_Ioc).comp measurable_norm)
  have hLreal : ∀ w : Euc d, |Real.log (min 1 ‖w‖)| ≤
      4 / d * (Set.Ioc 0 1).indicator (fun r => r ^ (-θ)) ‖w‖ := fun w => by
    have hb := r26t8a_c07e_Lbound d hd1 w
    have h0 : 0 ≤ (Set.Ioc 0 1).indicator (fun r : ℝ => r ^ (-θ)) ‖w‖ :=
      indicator_nonneg (fun r hr => Real.rpow_nonneg hr.1.le _) _
    rw [← ENNReal.ofReal_mul (by positivity)] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hb
  have s4 : ∫⁻ z, g4 z ≤ ENNReal.ofReal (K * (4 / d)) * ENNReal.ofReal (ω * (1 / ((d : ℝ) - θ))) := by
    rw [← lintegral_add_left_eq_self g4 y]
    have hpw : ∀ w : Euc d, g4 (y + w) ≤ ENNReal.ofReal (K * (4 / d)) *
        ENNReal.ofReal ((Set.Ioc 0 1).indicator (fun r => r ^ (-θ)) ‖w‖) := fun w => by
      simp only [hg4, hLf]
      rw [show y + w - y = w by abel, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc K * |Real.log (min 1 ‖w‖)| ≤ K * (4 / d * (Set.Ioc 0 1).indicator (fun r => r ^ (-θ)) ‖w‖) :=
            mul_le_mul_of_nonneg_left (hLreal w) hK0
        _ = _ := by ring
    calc ∫⁻ w : Euc d, g4 (y + w) ≤ ∫⁻ w : Euc d, ENNReal.ofReal (K * (4 / d)) *
          ENNReal.ofReal ((Set.Ioc 0 1).indicator (fun r => r ^ (-θ)) ‖w‖) := lintegral_mono hpw
      _ = ENNReal.ofReal (K * (4 / d)) * ∫⁻ w : Euc d, ENNReal.ofReal
          ((Set.Ioc 0 1).indicator (fun r => r ^ (-θ)) ‖w‖) := lintegral_const_mul _ hLθ
      _ ≤ _ := mul_le_mul' le_rfl (r26t8a_c07e_radialL d hd1)
  -- (2)
  set D : ℝ := ‖x - y‖ with hD
  have s2 : ∫⁻ z, g2 z ≤ ENNReal.ofReal (C1 * (4 / d)) * ENNReal.ofReal (ω * Cθ) := by
    by_cases hD2 : 2 ≤ D
    · have : ∀ z : Euc d, g2 z = 0 := fun z => by
        simp only [hg2, hAp, hLf]
        by_cases hz : ‖x - z‖ ≤ r0
        · have h1 : 1 ≤ ‖z - y‖ := by
            have : ‖x - y‖ ≤ ‖x - z‖ + ‖z - y‖ := by
              calc ‖x - y‖ = ‖(x - z) + (z - y)‖ := by congr 1; abel
                _ ≤ _ := norm_add_le _ _
            linarith
          rw [min_eq_left h1, Real.log_one, abs_zero, mul_zero, ENNReal.ofReal_zero]
        · push_neg at hz
          rw [hInd, indicator_of_notMem (fun h => absurd h.2 (not_le.2 hz)), mul_zero, zero_mul,
            ENNReal.ofReal_zero]
      simp_rw [this]; simp
    · push_neg at hD2
      have hCθge : 1 / θ ≤ Cθ := by
        have h1 : 1 / θ ≤ 2 ^ θ * (5 ^ θ / θ) := by
          have a : (1 : ℝ) ≤ 2 ^ θ := Real.one_le_rpow (by norm_num) hθ0.le
          have b : (1 : ℝ) ≤ 5 ^ θ := Real.one_le_rpow (by norm_num) hθ0.le
          calc 1 / θ ≤ 5 ^ θ / θ := div_le_div_of_nonneg_right b hθ0.le
            _ = 1 * (5 ^ θ / θ) := (one_mul _).symm
            _ ≤ 2 ^ θ * (5 ^ θ / θ) := mul_le_mul_of_nonneg_right a (by positivity)
        have h2 : 0 ≤ 1 / e + 1 / ((d : ℝ) - θ) + 4 ^ d / d := by positivity
        rw [hCθ]; linarith
      have hApLf : ∀ w : Euc d, g2 (x + w) ≤ ENNReal.ofReal (C1 * (4 / d)) *
          ENNReal.ofReal (Ind ‖w‖ * ‖w - (y - x)‖ ^ (-θ)) := fun w => by
        simp only [hg2, hAp, hLf]
        rw [show x - (x + w) = -w by abel, norm_neg, show x + w - y = w - (y - x) by abel,
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hb : |Real.log (min 1 ‖w - (y - x)‖)| ≤
            4 / d * (Set.Ioc 0 1).indicator (fun r => r ^ (-θ)) ‖w - (y - x)‖ := hLreal _
        have hb2 : (Set.Ioc 0 1).indicator (fun r : ℝ => r ^ (-θ)) ‖w - (y - x)‖ ≤
            ‖w - (y - x)‖ ^ (-θ) := by
          by_cases h : ‖w - (y - x)‖ ∈ Set.Ioc (0 : ℝ) 1
          · rw [indicator_of_mem h]
          · rw [indicator_of_notMem h]; exact Real.rpow_nonneg (norm_nonneg _) _
        calc C1 * Ind ‖w‖ * |Real.log (min 1 ‖w - (y - x)‖)| ≤
            C1 * Ind ‖w‖ * (4 / d * ‖w - (y - x)‖ ^ (-θ)) :=
              mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hb2 (by positivity)))
                (mul_nonneg hC1 (hInd0 _))
          _ = C1 * (4 / d) * (Ind ‖w‖ * ‖w - (y - x)‖ ^ (-θ)) := by ring
      by_cases hxy : x = y
      · -- coincident centres: radial integral of `r^{-(d/2 + d/4)}`
        subst hxy
        have hpw : ∀ᵐ w ∂(volume : Measure (Euc d)), g2 (x + w) ≤ ENNReal.ofReal (C1 * (4 / d)) *
            ENNReal.ofReal ((Set.Ioc 0 r0).indicator (fun r => r ^ (-(e + θ))) ‖w‖) := by
          have h0 : ∀ᵐ w ∂(volume : Measure (Euc d)), w ≠ 0 := by
            haveI : Nonempty (Fin d) := ⟨⟨0, hd1⟩⟩
            rw [ae_iff]; simp
          filter_upwards [h0] with w hw
          refine (hApLf w).trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_))
          have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
          rw [sub_self, sub_zero]
          by_cases h : ‖w‖ ≤ r0
          · rw [hInd, indicator_of_mem (show ‖w‖ ∈ Set.Ioc 0 r0 from ⟨hwpos, h⟩),
              indicator_of_mem (show ‖w‖ ∈ Set.Ioc 0 r0 from ⟨hwpos, h⟩), ← Real.rpow_add hwpos]
            apply le_of_eq; congr 1; ring
          · push_neg at h
            rw [hInd, indicator_of_notMem (fun hh => absurd hh.2 (not_le.2 h)), zero_mul]
            exact indicator_nonneg (fun r hr => Real.rpow_nonneg hr.1.le _) _
        have hIndp : Measurable fun w : Euc d => ENNReal.ofReal
            ((Set.Ioc 0 r0).indicator (fun r => r ^ (-(e + θ))) ‖w‖) :=
          ENNReal.measurable_ofReal.comp
            (((measurable_id.pow_const (-(e + θ))).indicator measurableSet_Ioc).comp measurable_norm)
        have hrp := r26t8a_c08a_radial d hd1 (p := e + θ) (ε := 0) (δ := r0) le_rfl hr0.le
          (Or.inr (by rw [he, hθ]; linarith))
        have hex : (d : ℝ) - 1 - (e + θ) + 1 = θ := by rw [he, hθ]; ring
        have hI : ∫ r in (0 : ℝ)..r0, r ^ ((d : ℝ) - 1 - (e + θ)) = r0 ^ θ / θ := by
          rw [integral_rpow (Or.inl (by rw [he, hθ]; linarith)), hex, Real.zero_rpow hθ0.ne']; simp
        rw [hI] at hrp
        rw [← lintegral_add_left_eq_self g2 x]
        calc ∫⁻ w : Euc d, g2 (x + w) ≤ ∫⁻ w : Euc d, ENNReal.ofReal (C1 * (4 / d)) *
              ENNReal.ofReal ((Set.Ioc 0 r0).indicator (fun r => r ^ (-(e + θ))) ‖w‖) := lintegral_mono_ae hpw
          _ = ENNReal.ofReal (C1 * (4 / d)) * ∫⁻ w : Euc d, ENNReal.ofReal
              ((Set.Ioc 0 r0).indicator (fun r => r ^ (-(e + θ))) ‖w‖) := lintegral_const_mul _ hIndp
          _ ≤ ENNReal.ofReal (C1 * (4 / d)) * ENNReal.ofReal (ω * Cθ) := by
              refine mul_le_mul' le_rfl (hrp.le.trans (ENNReal.ofReal_le_ofReal ?_))
              have h1 : r0 ^ θ ≤ 1 := Real.rpow_le_one hr0.le hr01 hθ0.le
              calc ω * (r0 ^ θ / θ) ≤ ω * (1 / θ) :=
                    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 hθ0.le) hω0
                _ ≤ ω * Cθ := mul_le_mul_of_nonneg_left hCθge hω0
      · have hDpos : 0 < D := norm_pos_iff.2 (sub_ne_zero.2 hxy)
        set e' : Euc d := y - x with he'
        have hnorm : ‖e'‖ = D := by rw [he', hD, norm_sub_rev]
        have hmeas2 : Measurable fun w : Euc d => ENNReal.ofReal (Ind ‖w‖ * ‖w - e'‖ ^ (-θ)) :=
          ENNReal.measurable_ofReal.comp
            ((((measurable_id.pow_const (-e)).indicator measurableSet_Ioc).comp measurable_norm).mul
              (((measurable_id.sub_const e').norm).pow_const (-θ)))
        rw [← lintegral_add_left_eq_self g2 x]
        calc ∫⁻ w : Euc d, g2 (x + w) ≤ ∫⁻ w : Euc d, ENNReal.ofReal (C1 * (4 / d)) *
              ENNReal.ofReal (Ind ‖w‖ * ‖w - e'‖ ^ (-θ)) := lintegral_mono hApLf
          _ = ENNReal.ofReal (C1 * (4 / d)) * ∫⁻ w : Euc d, ENNReal.ofReal (Ind ‖w‖ * ‖w - e'‖ ^ (-θ)) :=
              lintegral_const_mul _ hmeas2
          _ ≤ _ := by
              refine mul_le_mul' le_rfl ?_
              refine (r26t8a_c07a_two_center d hd1 (p := e) (p' := θ) (R := r0) (D := D)
                he0.le (by rw [he]; linarith) hθ0.le (by rw [hθ]; linarith) hDpos e' hnorm).trans ?_
              exact r26t8a_c07d_eval d hd1 hDpos hD2 hr01
  -- assemble
  calc ∫⁻ z, ENNReal.ofReal (rho z) *
        (ENNReal.ofReal (q (x - z)) * ENNReal.ofReal (1 + |Real.log (min 1 ‖z - y‖)|))
      ≤ ∫⁻ z, ENNReal.ofReal (rho z) * (g1 z + g2 z + ENNReal.ofReal K + g4 z) := lintegral_mono_ae hpt
    _ = _ := hexp
    _ ≤ ENNReal.ofReal G * (ENNReal.ofReal C1 * ENNReal.ofReal (ω * (1 / e))) +
        ENNReal.ofReal G * (ENNReal.ofReal (C1 * (4 / d)) * ENNReal.ofReal (ω * Cθ)) +
        ENNReal.ofReal K +
        ENNReal.ofReal G * (ENNReal.ofReal (K * (4 / d)) * ENNReal.ofReal (ω * (1 / ((d : ℝ) - θ)))) := by
        have h3 : ∫⁻ z, ENNReal.ofReal (rho z) * ENNReal.ofReal K = ENNReal.ofReal K := by
          rw [lintegral_mul_const _ hρE, hmass, one_mul]
        rw [h3]
        exact add_le_add (add_le_add (add_le_add ((hbd g1 hg1m).trans (mul_le_mul' le_rfl s1))
          ((hbd g2 hg2m).trans (mul_le_mul' le_rfl s2))) le_rfl)
          ((hbd g4 hg4m).trans (mul_le_mul' le_rfl s4))
    _ = ENNReal.ofReal (G * (C1 * (ω * (1 / e))) + G * (C1 * (4 / d) * (ω * Cθ)) + K +
          G * (K * (4 / d) * (ω * (1 / ((d : ℝ) - θ))))) := by
        have p1 : 0 ≤ ω * (1 / e) := by positivity
        have p2 : 0 ≤ ω * Cθ := by rw [hCθ]; positivity
        have p3 : 0 ≤ ω * (1 / ((d : ℝ) - θ)) := by positivity
        rw [← ENNReal.ofReal_mul hC1, ← ENNReal.ofReal_mul hG.le,
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ C1 * (4 / (d : ℝ))), ← ENNReal.ofReal_mul hG.le,
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ K * (4 / (d : ℝ))), ← ENNReal.ofReal_mul hG.le,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) hK0,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = _ := by congr 1; ring

end HRS.MS.R26T8A
