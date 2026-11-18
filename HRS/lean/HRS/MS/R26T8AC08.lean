import HRS.MS.R26T8AC08a
import HRS.MS.S82P2Mom
import HRS.MS.R26T8AO00d

/-!
# S8.2 observed-time layer, packet T8A.C08: capped critical row for cavity differentiation

Split `y` according to `‖x - y‖ < r0` (the radius of the two-sided power bound of the pole `q ≈ ‖z‖^{-d/2}`) and its
complement.  Outside, `q ≤ K` and the integrand is at most `t K (1+K)` against the probability measure `rho dy`.
Inside, `q ≤ C‖z‖^{-s}` and `q min(1, t(1+q)) ≤ C‖z‖^{-s} 1_{‖z‖ ≤ r*} + t C ‖z‖^{-s} + t C² ‖z‖^{-d} 1_{r* < ‖z‖}` with
`r* = min(r0, t^{2/d})`; the three radial integrals (C08a) are `≲ t`, `t` and `t log(e+1/t)` and `ρ ≤ G`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_c08_bound_outside (d : ℕ) (q : Euc d → ℝ) (hq : ShortRangePole d q) {r0 : ℝ}
    (hr0 : 0 < r0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : Euc d, r0 ≤ ‖z‖ → q z ≤ K := by
  obtain ⟨rf, cf, Cf, hrf, hcf, hfar⟩ := hq.far
  set R := max rf r0 with hR
  have hS : IsCompact (Metric.closedBall (0 : Euc d) R ∩ {z : Euc d | r0 ≤ ‖z‖}) :=
    (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_norm)
  have hcont : ContinuousOn q (Metric.closedBall (0 : Euc d) R ∩ {z : Euc d | r0 ≤ ‖z‖}) :=
    hq.smooth.continuousOn.mono fun z hz => by
      have : 0 < ‖z‖ := lt_of_lt_of_le hr0 hz.2
      exact norm_pos_iff.1 this
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hcont
  refine ⟨max (max C Cf) 0, le_max_right _ _, fun z hz => ?_⟩
  by_cases hzR : ‖z‖ ≤ R
  · have := hC z ⟨by simpa using hzR, hz⟩
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans (this.trans ((le_max_left _ _).trans (le_max_left _ _)))
  · have hrfz : rf ≤ ‖z‖ := (le_max_left rf r0).trans (not_le.1 hzR).le
    have h1 := hfar z hrfz
    have h2 : Real.exp (-cf * ‖z‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [norm_nonneg z])
    have h3 : Cf * Real.exp (-cf * ‖z‖ ^ 2) ≤ max Cf 0 := by
      rcases le_total 0 Cf with h | h
      · calc Cf * Real.exp (-cf * ‖z‖ ^ 2) ≤ Cf * 1 := mul_le_mul_of_nonneg_left h2 h
          _ = Cf := mul_one _
          _ ≤ max Cf 0 := le_max_left _ _
      · calc Cf * Real.exp (-cf * ‖z‖ ^ 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (Real.exp_pos _).le
          _ ≤ max Cf 0 := le_max_right _ _
    calc q z ≤ max Cf 0 := h1.trans h3
      _ ≤ max (max C Cf) 0 := max_le_max (le_max_right _ _) le_rfl

set_option maxHeartbeats 1600000 in
theorem r26t8a_capped_critical_row (d : ℕ) (hd : 2 ≤ d) (q : Euc d → ℝ)
    (hq : ShortRangePole d q) (G c : ℝ) (hG : 0 < G) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, HRS.Whole.IsProbDensity rho → HRS.Whole.HasR2GaussianUpper G c rho →
      ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x,
        ∫⁻ y, ENNReal.ofReal (q (x-y)*min 1 (t*(1+q (x-y)))) ∂HRS.Whole.withDensityReal rho ≤
          ENNReal.ofReal (C*t*Real.log (Real.exp 1 + t⁻¹)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨r0, c1, C1, hr0, hr01, hc1, hnear⟩ := hq.near
  obtain ⟨K, hK0, hK⟩ := r26t8a_c08_bound_outside d q hq hr0
  set C1' : ℝ := max C1 0 with hC1'
  have hC1'0 : 0 ≤ C1' := le_max_right _ _
  have hs : criticalS d = (d : ℝ) / 2 := rfl
  set e : ℝ := (d : ℝ) / 2 with he
  have he0 : 0 < e := by positivity
  set ω : ℝ := r26t8a_c08a_const d with hω
  have hω0 : 0 ≤ ω := r26t8a_c08a_const_nonneg d
  set L0 : ℝ := Real.log r0⁻¹ with hL0def
  have hL0 : 0 ≤ L0 := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hr0, hr01⟩)
  refine ⟨G * ω * (2 * C1' / e + C1' ^ 2 * (L0 + 2 / d)) + K * (1 + K), by positivity, ?_⟩
  intro rho hrho hG' t ht ht1 x
  set μ := HRS.Whole.withDensityReal rho with hμ
  -- the cut radius
  set rs : ℝ := min r0 (t ^ ((2 : ℝ) / d)) with hrs
  have hts : 0 < t ^ ((2 : ℝ) / d) := Real.rpow_pos_of_pos ht _
  have hrs0 : 0 < rs := lt_min hr0 hts
  have hrsr0 : rs ≤ r0 := min_le_left _ _
  have hrse : rs ^ e ≤ t := by
    calc rs ^ e ≤ (t ^ ((2 : ℝ) / d)) ^ e :=
          Real.rpow_le_rpow hrs0.le (min_le_right _ _) he0.le
      _ = t := by
          rw [← Real.rpow_mul ht.le]
          have : (2 : ℝ) / d * e = 1 := by rw [he]; field_simp
          rw [this, Real.rpow_one]
  have hr0e : r0 ^ e ≤ 1 := Real.rpow_le_one hr0.le hr01 he0.le
  -- density facts
  have hρm : Measurable rho := hrho.measurable
  have hρ0 : ∀ y, 0 ≤ rho y := hrho.nonneg
  have hρG : ∀ y, rho y ≤ G := fun y => by
    have h1 := hG'.2 y
    have h2 : Real.exp (-c * ‖y‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [norm_nonneg y])
    nlinarith [Real.exp_pos (-c * ‖y‖ ^ 2)]
  have hρi : Integrable rho := by
    by_contra h
    have := hrho.integral_one
    rw [integral_undef h] at this
    exact zero_ne_one this
  have hmass : ∫⁻ y, ENNReal.ofReal (rho y) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρ0), hrho.integral_one]
    simp
  have hρE : Measurable fun y : Euc d => ENNReal.ofReal (rho y) := ENNReal.measurable_ofReal.comp hρm
  -- the integrand
  have hum : Measurable fun z : Euc d => q z * min 1 (t * (1 + q z)) :=
    hq.measurable.mul (measurable_const.min (measurable_const.mul (measurable_const.add hq.measurable)))
  -- radial profiles
  set Ia : ℝ → ℝ := (Set.Ioc 0 rs).indicator (fun r => r ^ (-criticalS d)) with hIa
  set Ib : ℝ → ℝ := (Set.Ioc 0 r0).indicator (fun r => r ^ (-criticalS d)) with hIb
  set Ic : ℝ → ℝ := (Set.Ioc rs r0).indicator (fun r => r ^ (-(d : ℝ))) with hIc
  set far : Euc d → ℝ≥0∞ := {z : Euc d | r0 ≤ ‖z‖}.indicator
    (fun _ => ENNReal.ofReal (t * K * (1 + K))) with hfar
  set Bs : Euc d → ℝ≥0∞ := fun z => ENNReal.ofReal C1' * ENNReal.ofReal (Ia ‖z‖) +
    ENNReal.ofReal (t * C1') * ENNReal.ofReal (Ib ‖z‖) +
    ENNReal.ofReal (t * C1' ^ 2) * ENNReal.ofReal (Ic ‖z‖) with hBs
  have hP : ∀ z : Euc d, z ≠ 0 →
      ENNReal.ofReal (q z * min 1 (t * (1 + q z))) ≤ far z + Bs z := by
    intro z hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hq0 := hq.nonneg z
    by_cases hfz : r0 ≤ ‖z‖
    · have hqK := hK z hfz
      have h1 : q z * min 1 (t * (1 + q z)) ≤ t * K * (1 + K) := by
        calc q z * min 1 (t * (1 + q z)) ≤ q z * (t * (1 + q z)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) hq0
          _ ≤ K * (t * (1 + K)) := by
              apply mul_le_mul hqK _ (by positivity) hK0
              exact mul_le_mul_of_nonneg_left (by linarith) ht.le
          _ = t * K * (1 + K) := by ring
      have : far z = ENNReal.ofReal (t * K * (1 + K)) := by
        simp only [hfar]; exact indicator_of_mem (show z ∈ {z : Euc d | r0 ≤ ‖z‖} from hfz) _
      rw [this]
      exact (ENNReal.ofReal_le_ofReal h1).trans le_self_add
    · have hfz' : ‖z‖ < r0 := not_le.1 hfz
      have hqQ : q z ≤ C1' * ‖z‖ ^ (-criticalS d) := by
        have := (hnear z hzpos hfz'.le).2
        calc q z ≤ C1 * ‖z‖ ^ (-criticalS d) := this
          _ ≤ C1' * ‖z‖ ^ (-criticalS d) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hzpos.le _)
      have hfar0 : far z = 0 := by
        simp only [hfar]; exact indicator_of_notMem (show z ∉ {z : Euc d | r0 ≤ ‖z‖} from hfz) _
      rw [hfar0, zero_add]
      set Q : ℝ := C1' * ‖z‖ ^ (-criticalS d) with hQ
      have hQ0 : 0 ≤ Q := mul_nonneg hC1'0 (Real.rpow_nonneg hzpos.le _)
      by_cases hr : ‖z‖ ≤ rs
      · have hIaz : Ia ‖z‖ = ‖z‖ ^ (-criticalS d) := by
          simp only [hIa]; exact indicator_of_mem (show ‖z‖ ∈ Set.Ioc 0 rs from ⟨hzpos, hr⟩) _
        have h1 : q z * min 1 (t * (1 + q z)) ≤ Q := by
          calc q z * min 1 (t * (1 + q z)) ≤ q z * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hq0
            _ ≤ Q := by linarith
        calc ENNReal.ofReal (q z * min 1 (t * (1 + q z))) ≤ ENNReal.ofReal Q := ENNReal.ofReal_le_ofReal h1
          _ = ENNReal.ofReal C1' * ENNReal.ofReal (Ia ‖z‖) := by
              rw [hIaz, ← ENNReal.ofReal_mul hC1'0]
          _ ≤ Bs z := by
              simp only [hBs]
              exact le_self_add.trans le_self_add
      · have hr' : rs < ‖z‖ := not_le.1 hr
        have hIbz : Ib ‖z‖ = ‖z‖ ^ (-criticalS d) := by
          simp only [hIb]; exact indicator_of_mem (show ‖z‖ ∈ Set.Ioc 0 r0 from ⟨hzpos, hfz'.le⟩) _
        have hIcz : Ic ‖z‖ = ‖z‖ ^ (-(d : ℝ)) := by
          simp only [hIc]; exact indicator_of_mem (show ‖z‖ ∈ Set.Ioc rs r0 from ⟨hr', hfz'.le⟩) _
        have hsq : ‖z‖ ^ (-criticalS d) * ‖z‖ ^ (-criticalS d) = ‖z‖ ^ (-(d : ℝ)) := by
          rw [← Real.rpow_add hzpos]
          congr 1; rw [hs]; ring
        have h1 : q z * min 1 (t * (1 + q z)) ≤ t * Q + t * C1' ^ 2 * ‖z‖ ^ (-(d : ℝ)) := by
          have e1 : t * C1' ^ 2 * ‖z‖ ^ (-(d : ℝ)) = t * (Q * Q) := by
            rw [hQ, ← hsq]; ring
          rw [e1]
          calc q z * min 1 (t * (1 + q z)) ≤ q z * (t * (1 + q z)) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) hq0
            _ ≤ Q * (t * (1 + Q)) := by
                apply mul_le_mul hqQ _ (by positivity) hQ0
                exact mul_le_mul_of_nonneg_left (by linarith) ht.le
            _ = t * Q + t * (Q * Q) := by ring
        have hpow0 : 0 ≤ ‖z‖ ^ (-(d : ℝ)) := Real.rpow_nonneg hzpos.le _
        calc ENNReal.ofReal (q z * min 1 (t * (1 + q z)))
            ≤ ENNReal.ofReal (t * Q + t * C1' ^ 2 * ‖z‖ ^ (-(d : ℝ))) := ENNReal.ofReal_le_ofReal h1
          _ = ENNReal.ofReal (t * C1') * ENNReal.ofReal (Ib ‖z‖) +
                ENNReal.ofReal (t * C1' ^ 2) * ENNReal.ofReal (Ic ‖z‖) := by
              rw [hIbz, hIcz, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
                ← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1; rw [hQ]; ring
          _ ≤ Bs z := by
              simp only [hBs]
              exact add_le_add le_add_self le_rfl
  -- measurability
  haveI : Nonempty (Fin d) := ⟨⟨0, hd1⟩⟩
  have hrad : ∀ (S : Set ℝ) (a : ℝ), MeasurableSet S →
      Measurable fun z : Euc d => ENNReal.ofReal (S.indicator (fun r => r ^ a) ‖z‖) := fun S a hS =>
    ENNReal.measurable_ofReal.comp (((measurable_id.pow_const a).indicator hS).comp measurable_norm)
  have hIam := hrad (Set.Ioc 0 rs) (-criticalS d) measurableSet_Ioc
  have hIbm := hrad (Set.Ioc 0 r0) (-criticalS d) measurableSet_Ioc
  have hIcm := hrad (Set.Ioc rs r0) (-(d : ℝ)) measurableSet_Ioc
  have hBsm : Measurable Bs := by
    simp only [hBs]
    exact ((measurable_const.mul hIam).add (measurable_const.mul hIbm)).add (measurable_const.mul hIcm)
  have hfarm : Measurable far :=
    measurable_const.indicator (measurableSet_le measurable_const measurable_norm)
  have hUm : Measurable fun y : Euc d => ENNReal.ofReal (q (x - y) * min 1 (t * (1 + q (x - y)))) :=
    ENNReal.measurable_ofReal.comp (hum.comp (measurable_const.sub measurable_id))
  -- radial integrals
  have hsd : criticalS d < d := by rw [hs]; linarith
  have hex1 : (d : ℝ) - 1 - criticalS d + 1 = e := by rw [hs, he]; ring
  have hI1 : ∫ r in (0 : ℝ)..rs, r ^ ((d : ℝ) - 1 - criticalS d) = rs ^ e / e := by
    rw [integral_rpow (Or.inl (by rw [hs]; linarith)), hex1, Real.zero_rpow he0.ne']; simp
  have hI2 : ∫ r in (0 : ℝ)..r0, r ^ ((d : ℝ) - 1 - criticalS d) = r0 ^ e / e := by
    rw [integral_rpow (Or.inl (by rw [hs]; linarith)), hex1, Real.zero_rpow he0.ne']; simp
  have hI3 : ∫ r in rs..r0, r ^ ((d : ℝ) - 1 - (d : ℝ)) = Real.log (r0 / rs) := by
    have : (fun r : ℝ => r ^ ((d : ℝ) - 1 - (d : ℝ))) = fun r => r⁻¹ := by
      funext r; rw [show (d : ℝ) - 1 - (d : ℝ) = -1 by ring, Real.rpow_neg_one]
    rw [this]
    exact integral_inv_of_pos hrs0 hr0
  have hR1 : ∫⁻ z : Euc d, ENNReal.ofReal (Ia ‖z‖) = ENNReal.ofReal (ω * (rs ^ e / e)) := by
    have := r26t8a_c08a_radial d hd1 (p := criticalS d) (ε := 0) (δ := rs) le_rfl hrs0.le (Or.inr hsd)
    rw [hI1] at this
    exact this
  have hR2 : ∫⁻ z : Euc d, ENNReal.ofReal (Ib ‖z‖) = ENNReal.ofReal (ω * (r0 ^ e / e)) := by
    have := r26t8a_c08a_radial d hd1 (p := criticalS d) (ε := 0) (δ := r0) le_rfl hr0.le (Or.inr hsd)
    rw [hI2] at this
    exact this
  have hR3 : ∫⁻ z : Euc d, ENNReal.ofReal (Ic ‖z‖) = ENNReal.ofReal (ω * Real.log (r0 / rs)) := by
    have := r26t8a_c08a_radial d hd1 (p := (d : ℝ)) (ε := rs) (δ := r0) hrs0.le hrsr0 (Or.inl hrs0)
    rw [hI3] at this
    exact this
  have hBsint : ∫⁻ z : Euc d, Bs z = ENNReal.ofReal C1' * ENNReal.ofReal (ω * (rs ^ e / e)) +
      ENNReal.ofReal (t * C1') * ENNReal.ofReal (ω * (r0 ^ e / e)) +
      ENNReal.ofReal (t * C1' ^ 2) * ENNReal.ofReal (ω * Real.log (r0 / rs)) := by
    have hm1 : Measurable fun z : Euc d => ENNReal.ofReal C1' * ENNReal.ofReal (Ia ‖z‖) :=
      measurable_const.mul hIam
    have hm12 : Measurable fun z : Euc d => ENNReal.ofReal C1' * ENNReal.ofReal (Ia ‖z‖) +
        ENNReal.ofReal (t * C1') * ENNReal.ofReal (Ib ‖z‖) := by
      have := hm1.add (measurable_const.mul hIbm : Measurable fun z : Euc d =>
        ENNReal.ofReal (t * C1') * ENNReal.ofReal (Ib ‖z‖))
      exact this
    have hm2 : Measurable fun z : Euc d => ENNReal.ofReal (t * C1') * ENNReal.ofReal (Ib ‖z‖) :=
      measurable_const.mul hIbm
    have hm3 : Measurable fun z : Euc d => ENNReal.ofReal (t * C1' ^ 2) * ENNReal.ofReal (Ic ‖z‖) :=
      measurable_const.mul hIcm
    simp only [hBs]
    rw [lintegral_add_left hm12, lintegral_add_left hm1, lintegral_const_mul _ hIam,
      lintegral_const_mul _ hIbm, lintegral_const_mul _ hIcm, hR1, hR2, hR3]
  -- the integration
  have hne : ∀ᵐ y ∂(volume : Measure (Euc d)), y ≠ x := by rw [ae_iff]; simp
  have hmain : ∫⁻ y, ENNReal.ofReal (q (x - y) * min 1 (t * (1 + q (x - y)))) ∂μ ≤
      ENNReal.ofReal (t * K * (1 + K)) + ENNReal.ofReal G * ∫⁻ z : Euc d, Bs z := by
    rw [show μ = volume.withDensity (fun y => ENNReal.ofReal (rho y)) from rfl,
      lintegral_withDensity_eq_lintegral_mul volume hρE hUm]
    calc ∫⁻ y, (fun y => ENNReal.ofReal (rho y)) y * ENNReal.ofReal (q (x - y) * min 1 (t * (1 + q (x - y))))
        ≤ ∫⁻ y, (ENNReal.ofReal (rho y) * ENNReal.ofReal (t * K * (1 + K)) +
            ENNReal.ofReal G * Bs (x - y)) := by
          refine lintegral_mono_ae (hne.mono fun y hy => ?_)
          have hz : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
          have h1 := hP (x - y) hz
          have hfar_le : far (x - y) ≤ ENNReal.ofReal (t * K * (1 + K)) :=
            indicator_le (fun _ _ => le_rfl) _
          calc ENNReal.ofReal (rho y) * ENNReal.ofReal (q (x - y) * min 1 (t * (1 + q (x - y))))
              ≤ ENNReal.ofReal (rho y) * (far (x - y) + Bs (x - y)) := by gcongr
            _ = ENNReal.ofReal (rho y) * far (x - y) + ENNReal.ofReal (rho y) * Bs (x - y) :=
                mul_add _ _ _
            _ ≤ _ := by
                gcongr
                exact hρG y
      _ = (∫⁻ y, ENNReal.ofReal (rho y) * ENNReal.ofReal (t * K * (1 + K))) +
            ∫⁻ y, ENNReal.ofReal G * Bs (x - y) :=
          lintegral_add_left (hρE.mul measurable_const) _
      _ = ENNReal.ofReal (t * K * (1 + K)) + ENNReal.ofReal G * ∫⁻ z : Euc d, Bs z := by
          have hBx : Measurable fun y : Euc d => Bs (x - y) :=
            hBsm.comp (measurable_const.sub measurable_id)
          rw [lintegral_mul_const _ hρE, hmass, one_mul, lintegral_const_mul _ hBx,
            lintegral_sub_left_eq_self Bs x]
  refine hmain.trans ?_
  rw [hBsint]
  have hlog0 : 0 ≤ Real.log (r0 / rs) := Real.log_nonneg (by rw [le_div_iff₀ hrs0]; linarith)
  have hΛ1 : 1 ≤ Real.log (Real.exp 1 + t⁻¹) := by
    have : Real.log (Real.exp 1) ≤ Real.log (Real.exp 1 + t⁻¹) :=
      Real.log_le_log (Real.exp_pos _) (by linarith [inv_pos.2 ht])
    simpa using this
  have hΛt : Real.log t⁻¹ ≤ Real.log (Real.exp 1 + t⁻¹) :=
    Real.log_le_log (inv_pos.2 ht) (by linarith [Real.exp_pos 1])
  have hlog : Real.log (r0 / rs) ≤ L0 + 2 / d * Real.log t⁻¹ := by
    have h1 : r0 / rs ≤ r0⁻¹ * (t ^ ((2 : ℝ) / d))⁻¹ := by
      have ha : 1 ≤ r0⁻¹ := one_le_inv_iff₀.2 ⟨hr0, hr01⟩
      have hb : 1 ≤ (t ^ ((2 : ℝ) / d))⁻¹ :=
        one_le_inv_iff₀.2 ⟨hts, Real.rpow_le_one ht.le ht1 (by positivity)⟩
      have h2 : r0 / rs ≤ rs⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_of_le_one_left (inv_pos.2 hrs0).le hr01
      refine h2.trans ?_
      rcases min_choice r0 (t ^ ((2 : ℝ) / d)) with h | h
      · rw [hrs, h]; nlinarith
      · rw [hrs, h]; nlinarith
    refine (Real.log_le_log (div_pos hr0 hrs0) h1).trans ?_
    rw [Real.log_mul (inv_pos.2 hr0).ne' (inv_pos.2 hts).ne', Real.log_inv (t ^ ((2 : ℝ) / d)),
      Real.log_rpow ht, hL0def]
    have : -(2 / (d : ℝ) * Real.log t) = 2 / d * Real.log t⁻¹ := by rw [Real.log_inv]; ring
    linarith
  have hn1 : 0 ≤ ω * (rs ^ e / e) := by positivity
  have hn2 : 0 ≤ ω * (r0 ^ e / e) := by positivity
  have hn3 : 0 ≤ ω * Real.log (r0 / rs) := mul_nonneg hω0 hlog0
  have hKK : 0 ≤ t * K * (1 + K) := by positivity
  have hsumnn : 0 ≤ C1' * (ω * (rs ^ e / e)) + t * C1' * (ω * (r0 ^ e / e)) +
      t * C1' ^ 2 * (ω * Real.log (r0 / rs)) := by positivity
  have hsum : ENNReal.ofReal (t * K * (1 + K)) + ENNReal.ofReal G *
      (ENNReal.ofReal C1' * ENNReal.ofReal (ω * (rs ^ e / e)) +
        ENNReal.ofReal (t * C1') * ENNReal.ofReal (ω * (r0 ^ e / e)) +
        ENNReal.ofReal (t * C1' ^ 2) * ENNReal.ofReal (ω * Real.log (r0 / rs))) =
      ENNReal.ofReal (t * K * (1 + K) + G * (C1' * (ω * (rs ^ e / e)) +
        t * C1' * (ω * (r0 ^ e / e)) + t * C1' ^ 2 * (ω * Real.log (r0 / rs)))) := by
    rw [← ENNReal.ofReal_mul hC1'0, ← ENNReal.ofReal_mul (by positivity : 0 ≤ t * C1'),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ t * C1' ^ 2),
      ← ENNReal.ofReal_add (mul_nonneg hC1'0 hn1) (mul_nonneg (by positivity) hn2),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hC1'0 hn1) (mul_nonneg (by positivity) hn2))
        (mul_nonneg (by positivity) hn3),
      ← ENNReal.ofReal_mul hG.le, ← ENNReal.ofReal_add hKK (mul_nonneg hG.le hsumnn)]
  rw [hsum]
  refine ENNReal.ofReal_le_ofReal ?_
  set Λ := Real.log (Real.exp 1 + t⁻¹) with hΛ
  have hg0 : 0 ≤ G * ω := mul_nonneg hG.le hω0
  have e1 : C1' * (ω * (rs ^ e / e)) ≤ C1' * (ω * (t / e)) := by
    gcongr
  have e2 : t * C1' * (ω * (r0 ^ e / e)) ≤ t * C1' * (ω * (1 / e)) := by
    gcongr
  have e3 : t * C1' ^ 2 * (ω * Real.log (r0 / rs)) ≤
      t * C1' ^ 2 * (ω * (L0 + 2 / d * Λ)) := by
    gcongr
    have hq2 : 2 / (d : ℝ) * Real.log t⁻¹ ≤ 2 / d * Λ := mul_le_mul_of_nonneg_left hΛt (by positivity)
    linarith [hlog, hq2]
  have key : C1' * (ω * (t / e)) + t * C1' * (ω * (1 / e)) + t * C1' ^ 2 * (ω * (L0 + 2 / d * Λ)) ≤
      t * Λ * (ω * (2 * C1' / e + C1' ^ 2 * (L0 + 2 / d))) := by
    have ht0 := ht.le
    have hΛ0 : 0 ≤ Λ := by linarith
    have a1 : C1' * (ω * (t / e)) ≤ t * Λ * (ω * (C1' / e)) := by
      have : C1' * (ω * (t / e)) = t * (ω * (C1' / e)) := by ring
      rw [this]
      have h0 : 0 ≤ ω * (C1' / e) := by positivity
      nlinarith [mul_nonneg ht0 h0]
    have a2 : t * C1' * (ω * (1 / e)) ≤ t * Λ * (ω * (C1' / e)) := by
      have : t * C1' * (ω * (1 / e)) = t * (ω * (C1' / e)) := by ring
      rw [this]
      have h0 : 0 ≤ ω * (C1' / e) := by positivity
      nlinarith [mul_nonneg ht0 h0]
    have a3 : t * C1' ^ 2 * (ω * (L0 + 2 / d * Λ)) ≤ t * Λ * (ω * (C1' ^ 2 * (L0 + 2 / d))) := by
      have h0 : 0 ≤ t * (ω * C1' ^ 2) := by positivity
      have : t * C1' ^ 2 * (ω * (L0 + 2 / d * Λ)) = (t * (ω * C1' ^ 2)) * (L0 + 2 / d * Λ) := by ring
      have h5 : t * Λ * (ω * (C1' ^ 2 * (L0 + 2 / d))) = (t * (ω * C1' ^ 2)) * (Λ * (L0 + 2 / d)) := by ring
      rw [this, h5]
      refine mul_le_mul_of_nonneg_left ?_ h0
      have : 0 ≤ (d : ℝ)⁻¹ := by positivity
      nlinarith [mul_nonneg hL0 (sub_nonneg.2 hΛ1)]
    calc _ ≤ t * Λ * (ω * (C1' / e)) + t * Λ * (ω * (C1' / e)) +
          t * Λ * (ω * (C1' ^ 2 * (L0 + 2 / d))) := by linarith [a1, a2, a3]
      _ = _ := by ring
  have hT : t * K * (1 + K) ≤ t * Λ * (K * (1 + K)) := by
    have : 0 ≤ t * (K * (1 + K)) := by positivity
    nlinarith [mul_nonneg this (sub_nonneg.2 hΛ1)]
  have hin : C1' * (ω * (rs ^ e / e)) + t * C1' * (ω * (r0 ^ e / e)) +
      t * C1' ^ 2 * (ω * Real.log (r0 / rs)) ≤ t * Λ * (ω * (2 * C1' / e + C1' ^ 2 * (L0 + 2 / d))) := by
    linarith [e1, e2, e3, key]
  calc t * K * (1 + K) + G * (C1' * (ω * (rs ^ e / e)) + t * C1' * (ω * (r0 ^ e / e)) +
          t * C1' ^ 2 * (ω * Real.log (r0 / rs)))
      ≤ t * Λ * (K * (1 + K)) + G * (t * Λ * (ω * (2 * C1' / e + C1' ^ 2 * (L0 + 2 / d)))) :=
        add_le_add hT (mul_le_mul_of_nonneg_left hin hG.le)
    _ = (G * ω * (2 * C1' / e + C1' ^ 2 * (L0 + 2 / d)) + K * (1 + K)) * t * Λ := by ring

end HRS.MS.R26T8A
