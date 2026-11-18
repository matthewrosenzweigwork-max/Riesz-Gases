import HRS.MS.PsdHeatAux1
import HRS.MS.PsdAux2

/-!
# PSD-3 (part 2): heat split of the logarithmic kernel (`s = 0`)

Namespace `HRS.MS.Psd`.  For `τ > 0` put `h(r, u) = (e^{-r²u} - e^{-u})/u` (`psd3_h`) and

* `qTauLog d τ x = ½ ∫_{(1/τ,∞)} e^{-u|x|²} du/u`,
* `kTauLog d τ x = ½ ∫_{(0,1/τ]} h(|x|, u) du - ½ ∫_{(1/τ,∞)} e^{-u} du/u`.

`kTauLog` is defined by the right-hand side (the identity displayed in the TeX), not as
`-log|x| - qTauLog x`, because the latter has the junk values `-log 0 = 0` and `qTauLog 0 = 0`
(the integral diverges) at the origin, whereas the displayed formula is finite and continuous
at `0`.  Main results (`0 < τ`):

* `riesz_log_heat_split`: `rieszKernel d 0 x = qTauLog d τ x + kTauLog d τ x` for `x ≠ 0`
  (from Frullani, `psd2_g_val`).
* `qTauLog_nonneg`, `qTauLog_integrable_integral` (`1 ≤ d`): `qTauLog` is integrable with
  `∫ qTauLog = π^{d/2} τ^{d/2} / d`.
* `kTauLog_abs_le`, `kTauLog_abs_le_unit`: `|kTauLog x| ≤ 1/(2τ) + τ/2 + log (2 + |x|)`, and
  `|kTauLog x| ≤ 1/(2τ) + τ/2` for `|x| ≤ 1`; `kTauLog_continuous`.
* `kTauLog_cpd`: for a finite measure `ν`, a measurable `u` (the signed measure `u ν`) with
  `∫ u dν = 0`, `u` integrable and `log (2 + |x|) u(x)` integrable (the log moment), the double
  integral `∫ kTauLog (z.1 - z.2) (u z.1 u z.2) d(ν ⊗ ν)` is `≥ 0`.  The two integrability
  hypotheses are exactly what makes the integrand absolutely integrable (so there is no
  junk-value branch), and the mass-zero hypothesis is necessary.
Helper lemmas carry the prefix `psd3_`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.MS.Psd

open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

/-- The Frullani integrand `(e^{-r²u} - e^{-u})/u`. -/
def psd3_h (r u : ℝ) : ℝ := (Real.exp (-(r ^ 2 * u)) - Real.exp (-u)) / u

/-- `q_τ(x) = ½ ∫_{1/τ}^∞ e^{-u|x|²} du/u`. -/
def qTauLog (d : ℕ) (τ : ℝ) (x : Euc d) : ℝ :=
  (1 / 2) * ∫ u in Ioi (1 / τ), Real.exp (-(‖x‖ ^ 2 * u)) / u

/-- `k_τ(x) = ½ ∫_0^{1/τ} (e^{-u|x|²} - e^{-u}) du/u - ½ ∫_{1/τ}^∞ e^{-u} du/u`. -/
def kTauLog (d : ℕ) (τ : ℝ) (x : Euc d) : ℝ :=
  (1 / 2) * (∫ u in Ioc (0 : ℝ) (1 / τ), psd3_h ‖x‖ u) -
    (1 / 2) * ∫ u in Ioi (1 / τ), Real.exp (-u) / u

/-! ### Elementary estimates on `psd3_h` -/

theorem psd3_exp_diff {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ Real.exp (-a) - Real.exp (-b) ∧ Real.exp (-a) - Real.exp (-b) ≤ b - a := by
  refine ⟨sub_nonneg.2 (Real.exp_le_exp.2 (by linarith)), ?_⟩
  have h1 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 := Real.one_sub_le_exp_neg (b - a)
  have h3 : Real.exp (-a) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have h4 := Real.exp_pos (-a)
  rw [h1]
  nlinarith [mul_nonneg h4.le (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 hab)]

theorem psd3_h_nonneg {r : ℝ} (hr : r ^ 2 ≤ 1) {u : ℝ} (hu : 0 < u) : 0 ≤ psd3_h r u := by
  unfold psd3_h
  refine div_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 ?_)) hu.le
  nlinarith

theorem psd3_h_nonpos {r : ℝ} (hr : 1 ≤ r ^ 2) {u : ℝ} (hu : 0 < u) : psd3_h r u ≤ 0 := by
  unfold psd3_h
  refine div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (Real.exp_le_exp.2 ?_)) hu.le
  nlinarith

theorem psd3_h_abs_le (r : ℝ) {u : ℝ} (hu : 0 < u) : |psd3_h r u| ≤ |r ^ 2 - 1| := by
  unfold psd3_h
  rw [abs_div, abs_of_pos hu, div_le_iff₀ hu]
  rcases le_total (r ^ 2) 1 with h | h
  · have := psd3_exp_diff (a := r ^ 2 * u) (b := u) (by positivity) (by nlinarith)
    rw [abs_of_nonneg this.1, abs_of_nonpos (by linarith : r ^ 2 - 1 ≤ 0)]
    nlinarith [this.2]
  · have := psd3_exp_diff (a := u) (b := r ^ 2 * u) (by positivity) (by nlinarith)
    rw [abs_of_nonpos (by linarith [this.1] : Real.exp (-(r ^ 2 * u)) - Real.exp (-u) ≤ 0),
      abs_of_nonneg (by linarith : 0 ≤ r ^ 2 - 1)]
    nlinarith [this.2]

theorem psd3_h_le_one {r : ℝ} (hr : r ^ 2 ≤ 1) {u : ℝ} (hu : 0 < u) : psd3_h r u ≤ 1 := by
  unfold psd3_h
  rw [div_le_one hu]
  have h1 : Real.exp (-(r ^ 2 * u)) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
  have h2 := Real.one_sub_le_exp_neg u
  linarith

theorem psd3_h_meas : Measurable (fun p : ℝ × ℝ => psd3_h p.1 p.2) := by
  unfold psd3_h
  exact (Real.measurable_exp.comp (((measurable_fst.pow_const 2).mul measurable_snd).neg)
    |>.sub (Real.measurable_exp.comp measurable_snd.neg)).div measurable_snd

theorem psd3_h_integrableOn (r : ℝ) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (psd3_h r) (Ioc (0 : ℝ) T) := by
  have hc : IntegrableOn (fun _ : ℝ => |r ^ 2 - 1|) (Ioc (0 : ℝ) T) :=
    integrableOn_const (by simp)
  refine Integrable.mono' hc
    ((psd3_h_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  rw [Real.norm_eq_abs]
  exact psd3_h_abs_le r hu.1


/-! ### Tails `∫_{1/τ}^∞ e^{-a u} du/u` -/

theorem psd3_tail_integrableOn {a : ℝ} (ha : 0 < a) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun u : ℝ => Real.exp (-(a * u)) / u) (Ioi (1 / τ)) := by
  have h1 : IntegrableOn (fun u : ℝ => τ * Real.exp (-a * u)) (Ioi (1 / τ)) :=
    Integrable.const_mul (exp_neg_integrableOn_Ioi _ ha) _
  have hm : Measurable (fun u : ℝ => Real.exp (-(a * u)) / u) :=
    (Real.measurable_exp.comp (measurable_id.const_mul a).neg).div measurable_id
  refine Integrable.mono' h1 hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : 1 / τ < u := hu
  have hu0 : 0 < u := lt_trans (by positivity) hu'
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), neg_mul, div_eq_mul_inv, mul_comm]
  have : u⁻¹ ≤ τ := by
    rw [inv_le_comm₀ hu0 hτ]; simpa using hu'.le
  exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

theorem psd3_tail_nonneg (a : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ ∫ u in Ioi (1 / τ), Real.exp (-(a * u)) / u := by
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have hu' : 1 / τ < u := hu
  have : 0 < u := lt_trans (by positivity) hu'
  positivity

theorem psd3_tail_mono {a : ℝ} (ha : 1 ≤ a) {τ : ℝ} (hτ : 0 < τ) :
    ∫ u in Ioi (1 / τ), Real.exp (-(a * u)) / u ≤ ∫ u in Ioi (1 / τ), Real.exp (-(1 * u)) / u := by
  refine setIntegral_mono_on (psd3_tail_integrableOn (by linarith) hτ)
    (psd3_tail_integrableOn one_pos hτ) measurableSet_Ioi fun u hu => ?_
  have hu' : 1 / τ < u := hu
  have : 0 < u := lt_trans (by positivity) hu'
  gcongr

theorem psd3_E_le {τ : ℝ} (hτ : 0 < τ) :
    ∫ u in Ioi (1 / τ), Real.exp (-u) / u ≤ τ := by
  have h1 : IntegrableOn (fun u : ℝ => Real.exp (-u) / u) (Ioi (1 / τ)) := by
    simpa using psd3_tail_integrableOn one_pos hτ
  have h2 : IntegrableOn (fun u : ℝ => τ * Real.exp (-u)) (Ioi (1 / τ)) :=
    Integrable.const_mul (integrableOn_exp_neg_Ioi _) _
  calc ∫ u in Ioi (1 / τ), Real.exp (-u) / u ≤ ∫ u in Ioi (1 / τ), τ * Real.exp (-u) := by
        refine setIntegral_mono_on h1 h2 measurableSet_Ioi fun u hu => ?_
        have hu' : 1 / τ < u := hu
        have hu0 : 0 < u := lt_trans (by positivity) hu'
        rw [div_eq_mul_inv, mul_comm]
        have : u⁻¹ ≤ τ := by
          rw [inv_le_comm₀ hu0 hτ]; simpa using hu'.le
        exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    _ = τ * Real.exp (-(1 / τ)) := by
        rw [integral_const_mul, integral_exp_neg_Ioi]
    _ ≤ τ * 1 := by
        gcongr
        rw [Real.exp_le_one_iff]; have : 0 < 1 / τ := by positivity
        linarith
    _ = τ := mul_one τ

/-! ### The split -/

theorem psd3_h_eq_g {r u : ℝ} (hu : 0 < u) : psd3_h r u = psd2_g r u := by
  unfold psd3_h psd2_g
  rw [show (0 : ℝ) / 2 - 1 = -1 by norm_num, Real.rpow_neg_one, one_mul]
  field_simp

theorem psd3_h_Ioi_integrable {r : ℝ} (hr : 0 < r) : IntegrableOn (psd3_h r) (Ioi (0 : ℝ)) :=
  (psd2_g_int hr).congr_fun (fun u hu => (psd3_h_eq_g hu).symm) measurableSet_Ioi

theorem psd3_h_Ioi_val {r : ℝ} (hr : 0 < r) :
    ∫ u in Ioi (0 : ℝ), psd3_h r u = 2 * (-Real.log r) := by
  rw [← psd2_g_val hr]
  exact setIntegral_congr_fun measurableSet_Ioi fun u hu => psd3_h_eq_g hu

theorem riesz_log_heat_split {τ : ℝ} (hτ : 0 < τ) {x : Euc d} (hx : x ≠ 0) :
    rieszKernel d 0 x = qTauLog d τ x + kTauLog d τ x := by
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hint := psd3_h_Ioi_integrable hr
  have hsplit : ∫ u in Ioi (0 : ℝ), psd3_h ‖x‖ u =
      (∫ u in Ioc (0 : ℝ) (1 / τ), psd3_h ‖x‖ u) + ∫ u in Ioi (1 / τ), psd3_h ‖x‖ u := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by positivity : (0 : ℝ) ≤ 1 / τ)]
    refine setIntegral_union ?_ measurableSet_Ioi ?_ ?_
    · exact Set.disjoint_left.2 fun t h1 h2 => absurd h1.2 (not_le.2 h2)
    · exact hint.mono_set (by rw [← Set.Ioc_union_Ioi_eq_Ioi (by positivity : (0 : ℝ) ≤ 1 / τ)]
                              exact subset_union_left)
    · exact hint.mono_set (by rw [← Set.Ioc_union_Ioi_eq_Ioi (by positivity : (0 : ℝ) ≤ 1 / τ)]
                              exact subset_union_right)
  have hT := psd3_tail_integrableOn (a := ‖x‖ ^ 2) (by positivity) hτ
  have hE : IntegrableOn (fun u : ℝ => Real.exp (-u) / u) (Ioi (1 / τ)) := by
    simpa using psd3_tail_integrableOn one_pos hτ
  have htail : ∫ u in Ioi (1 / τ), psd3_h ‖x‖ u =
      (∫ u in Ioi (1 / τ), Real.exp (-(‖x‖ ^ 2 * u)) / u) -
        ∫ u in Ioi (1 / τ), Real.exp (-u) / u := by
    rw [← integral_sub hT hE]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    unfold psd3_h
    rw [sub_div]
  have hv := psd3_h_Ioi_val hr
  have hk : rieszKernel d 0 x = -Real.log ‖x‖ := by simp [rieszKernel]
  rw [hk]
  unfold qTauLog kTauLog
  rw [hsplit, htail] at hv
  linarith

/-! ### Bounds and continuity of `kTauLog` -/

theorem qTauLog_nonneg {τ : ℝ} (hτ : 0 < τ) (x : Euc d) : 0 ≤ qTauLog d τ x := by
  unfold qTauLog
  have := psd3_tail_nonneg (‖x‖ ^ 2) hτ
  linarith

theorem psd3_q_le {τ : ℝ} (hτ : 0 < τ) {x : Euc d} (hx : 1 ≤ ‖x‖) : qTauLog d τ x ≤ τ / 2 := by
  unfold qTauLog
  have h1 := psd3_tail_mono (a := ‖x‖ ^ 2) (by nlinarith) hτ
  have h2 := psd3_E_le hτ
  have : ∫ u in Ioi (1 / τ), Real.exp (-(1 * u)) / u = ∫ u in Ioi (1 / τ), Real.exp (-u) / u := by
    simp
  linarith

theorem psd3_I_bounds {τ : ℝ} (hτ : 0 < τ) {r : ℝ} (hr : r ^ 2 ≤ 1) :
    0 ≤ ∫ u in Ioc (0 : ℝ) (1 / τ), psd3_h r u ∧ ∫ u in Ioc (0 : ℝ) (1 / τ), psd3_h r u ≤ 1 / τ := by
  have h1τ : 0 < 1 / τ := by positivity
  refine ⟨setIntegral_nonneg measurableSet_Ioc fun u hu => psd3_h_nonneg hr hu.1, ?_⟩
  calc ∫ u in Ioc (0 : ℝ) (1 / τ), psd3_h r u ≤ ∫ u in Ioc (0 : ℝ) (1 / τ), (1 : ℝ) :=
        setIntegral_mono_on (psd3_h_integrableOn r h1τ) (integrableOn_const (by simp))
          measurableSet_Ioc fun u hu => psd3_h_le_one hr hu.1
    _ = 1 / τ := by
        rw [setIntegral_const]; simp [hτ.le]

theorem kTauLog_abs_le_unit {τ : ℝ} (hτ : 0 < τ) {x : Euc d} (hx : ‖x‖ ≤ 1) :
    |kTauLog d τ x| ≤ 1 / (2 * τ) + τ / 2 := by
  have hr : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
  obtain ⟨h1, h2⟩ := psd3_I_bounds hτ hr
  have h3 := psd3_E_le hτ
  have h4 : 0 ≤ ∫ u in Ioi (1 / τ), Real.exp (-u) / u := by
    simpa using psd3_tail_nonneg 1 hτ
  have e : 1 / (2 * τ) = (1 / τ) / 2 := by field_simp
  unfold kTauLog
  rw [abs_le]
  constructor <;> linarith

theorem kTauLog_abs_le {τ : ℝ} (hτ : 0 < τ) (x : Euc d) :
    |kTauLog d τ x| ≤ 1 / (2 * τ) + τ / 2 + Real.log (2 + ‖x‖) := by
  have hl : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
  rcases le_total ‖x‖ 1 with h | h
  · linarith [kTauLog_abs_le_unit hτ h]
  · have hx : x ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h; linarith
    have hk := riesz_log_heat_split hτ hx
    have hq0 := qTauLog_nonneg hτ x
    have hq1 := psd3_q_le hτ h
    have hr : rieszKernel d 0 x = -Real.log ‖x‖ := by simp [rieszKernel]
    have hlog0 : 0 ≤ Real.log ‖x‖ := Real.log_nonneg h
    have hlog1 : Real.log ‖x‖ ≤ Real.log (2 + ‖x‖) :=
      Real.log_le_log (by linarith) (by linarith)
    have hpos : 0 < 1 / (2 * τ) := by positivity
    rw [abs_le]
    constructor <;> linarith

theorem psd3_I_continuous {τ : ℝ} (hτ : 0 < τ) :
    Continuous fun r : ℝ => ∫ u in Ioc (0 : ℝ) (1 / τ), psd3_h r u := by
  rw [continuous_iff_continuousAt]
  intro r₀
  have h1τ : 0 < 1 / τ := by positivity
  refine continuousAt_of_dominated (bound := fun _ => (|r₀| + 1) ^ 2 + 1) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun r =>
      ((psd3_h_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  · have : ∀ᶠ r in 𝓝 r₀, |r| < |r₀| + 1 := by
      have := (continuous_abs.tendsto r₀).eventually (gt_mem_nhds (by linarith : |r₀| < |r₀| + 1))
      exact this
    filter_upwards [this] with r hr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs]
    refine (psd3_h_abs_le r hu.1).trans ?_
    have h0 : 0 ≤ |r| := abs_nonneg r
    have : r ^ 2 ≤ (|r₀| + 1) ^ 2 := by
      rw [← sq_abs r]; exact pow_le_pow_left₀ h0 hr.le 2
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg r]
  · exact integrableOn_const (by simp)
  · refine Filter.Eventually.of_forall fun u => ?_
    exact (by unfold psd3_h; fun_prop : Continuous fun r : ℝ => psd3_h r u).continuousAt

theorem kTauLog_continuous {τ : ℝ} (hτ : 0 < τ) : Continuous (kTauLog d τ) := by
  unfold kTauLog
  exact (continuous_const.mul ((psd3_I_continuous hτ).comp continuous_norm)).sub continuous_const


/-! ### Conditional positive definiteness -/

theorem psd3_A_le {τ : ℝ} (hτ : 0 < τ) (x : Euc d) :
    ∫ u in Ioc (0 : ℝ) (1 / τ), |psd3_h ‖x‖ u| ≤ 1 / τ + τ + 2 * Real.log (2 + ‖x‖) := by
  have hl : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
  have h1τ : 0 < 1 / τ := by positivity
  have hE0 : 0 ≤ ∫ u in Ioi (1 / τ), Real.exp (-u) / u := by
    simpa using psd3_tail_nonneg 1 hτ
  rcases le_total ‖x‖ 1 with h | h
  · have hr : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x]
    have e : ∫ u in Ioc (0 : ℝ) (1 / τ), |psd3_h ‖x‖ u| =
        ∫ u in Ioc (0 : ℝ) (1 / τ), psd3_h ‖x‖ u :=
      setIntegral_congr_fun measurableSet_Ioc fun u hu => abs_of_nonneg (psd3_h_nonneg hr hu.1)
    rw [e]
    linarith [(psd3_I_bounds hτ hr).2]
  · have hr : 1 ≤ ‖x‖ ^ 2 := by nlinarith
    have e : ∫ u in Ioc (0 : ℝ) (1 / τ), |psd3_h ‖x‖ u| =
        -∫ u in Ioc (0 : ℝ) (1 / τ), psd3_h ‖x‖ u := by
      rw [← integral_neg]
      exact setIntegral_congr_fun measurableSet_Ioc fun u hu => abs_of_nonpos (psd3_h_nonpos hr hu.1)
    rw [e]
    have hk := kTauLog_abs_le hτ x
    unfold kTauLog at hk
    rw [abs_le] at hk
    have : 1 / (2 * τ) = (1 / τ) / 2 := by field_simp
    linarith [hk.1]

theorem psd3_log_sub_le (a b : Euc d) :
    Real.log (2 + ‖a - b‖) ≤ Real.log (2 + ‖a‖) + Real.log (2 + ‖b‖) := by
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  rw [← Real.log_mul (by positivity) (by positivity)]
  refine Real.log_le_log (by linarith [norm_nonneg (a - b)]) ?_
  nlinarith [norm_sub_le a b]

theorem psd3_gauss_int {ν : Measure (Euc d)} [IsFiniteMeasure ν] {u : Euc d → ℝ}
    (hum : Measurable u) (hu : Integrable u ν) (v : ℝ) (hv : 0 ≤ v) :
    Integrable (fun z : Euc d × Euc d => Real.exp (-v * ‖z.1 - z.2‖ ^ 2) * u z.1 * u z.2)
      (ν.prod ν) := by
  have hmaj : Integrable (fun z : Euc d × Euc d => |u z.1| * |u z.2|) (ν.prod ν) :=
    hu.abs.mul_prod hu.abs
  refine Integrable.mono' hmaj ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (((by fun_prop : Measurable (fun z : Euc d × Euc d =>
      Real.exp (-v * ‖z.1 - z.2‖ ^ 2))).mul (hum.comp measurable_fst)).mul
        (hum.comp measurable_snd)).aestronglyMeasurable
  · have h1 : Real.exp (-v * ‖z.1 - z.2‖ ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖z.1 - z.2‖]
    have h2 : 0 ≤ Real.exp (-v * ‖z.1 - z.2‖ ^ 2) := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h2]
    calc Real.exp (-v * ‖z.1 - z.2‖ ^ 2) * |u z.1| * |u z.2|
        ≤ 1 * |u z.1| * |u z.2| := by gcongr
      _ = |u z.1| * |u z.2| := by ring

/-- The integrable majorant of the `u`-integrated Frullani integrand. -/
def psd3_D (τ : ℝ) (u : Euc d → ℝ) (z : Euc d × Euc d) : ℝ :=
  (1 / τ + τ) * (|u z.1| * |u z.2|) + 2 * ((Real.log (2 + ‖z.1‖) * |u z.1|) * |u z.2|) +
    2 * (|u z.1| * (Real.log (2 + ‖z.2‖) * |u z.2|))

theorem psd3_D_int {τ : ℝ} {ν : Measure (Euc d)} [IsFiniteMeasure ν] {u : Euc d → ℝ}
    (hu : Integrable u ν) (hlog : Integrable (fun x : Euc d => Real.log (2 + ‖x‖) * u x) ν) :
    Integrable (psd3_D τ u) (ν.prod ν) := by
  have hL : Integrable (fun x : Euc d => Real.log (2 + ‖x‖) * |u x|) ν := by
    refine hlog.norm.congr (Filter.Eventually.of_forall fun x => ?_)
    have : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg this]
  have h1 : Integrable (fun z : Euc d × Euc d => |u z.1| * |u z.2|) (ν.prod ν) :=
    hu.abs.mul_prod hu.abs
  have h2 : Integrable (fun z : Euc d × Euc d => (Real.log (2 + ‖z.1‖) * |u z.1|) * |u z.2|)
      (ν.prod ν) := hL.mul_prod hu.abs
  have h3 : Integrable (fun z : Euc d × Euc d => |u z.1| * (Real.log (2 + ‖z.2‖) * |u z.2|))
      (ν.prod ν) := hu.abs.mul_prod hL
  exact (h1.const_mul _).add (h2.const_mul _) |>.add (h3.const_mul _)

theorem psd3_Phi_meas {u : Euc d → ℝ} (hum : Measurable u) :
    Measurable (fun p : (Euc d × Euc d) × ℝ => psd3_h ‖p.1.1 - p.1.2‖ p.2 * (u p.1.1 * u p.1.2)) := by
  have h1 : Measurable (fun p : (Euc d × Euc d) × ℝ => (‖p.1.1 - p.1.2‖, p.2)) :=
    (measurable_norm.comp ((measurable_fst.comp measurable_fst).sub
      (measurable_snd.comp measurable_fst))).prodMk measurable_snd
  exact (psd3_h_meas.comp h1).mul
    ((hum.comp (measurable_fst.comp measurable_fst)).mul
      (hum.comp (measurable_snd.comp measurable_fst)))

theorem psd3_Phi_norm_le {τ : ℝ} (hτ : 0 < τ) {u : Euc d → ℝ} (z : Euc d × Euc d) :
    ∫ v in Ioc (0 : ℝ) (1 / τ), ‖psd3_h ‖z.1 - z.2‖ v * (u z.1 * u z.2)‖ ≤ psd3_D τ u z := by
  have e : ∫ v in Ioc (0 : ℝ) (1 / τ), ‖psd3_h ‖z.1 - z.2‖ v * (u z.1 * u z.2)‖ =
      |u z.1| * |u z.2| * ∫ v in Ioc (0 : ℝ) (1 / τ), |psd3_h ‖z.1 - z.2‖ v| := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [norm_mul, Real.norm_eq_abs, abs_mul]
    ring
  rw [e]
  have hA := psd3_A_le hτ (z.1 - z.2)
  have hlg := psd3_log_sub_le z.1 z.2
  unfold psd3_D
  calc |u z.1| * |u z.2| * ∫ v in Ioc (0 : ℝ) (1 / τ), |psd3_h ‖z.1 - z.2‖ v|
      ≤ |u z.1| * |u z.2| * (1 / τ + τ + 2 * (Real.log (2 + ‖z.1‖) +
          Real.log (2 + ‖z.2‖))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = _ := by ring

theorem psd3_Phi_int {τ : ℝ} (hτ : 0 < τ) {ν : Measure (Euc d)} [IsFiniteMeasure ν]
    {u : Euc d → ℝ} (hum : Measurable u) (hu : Integrable u ν)
    (hlog : Integrable (fun x : Euc d => Real.log (2 + ‖x‖) * u x) ν) :
    Integrable (fun p : (Euc d × Euc d) × ℝ => psd3_h ‖p.1.1 - p.1.2‖ p.2 * (u p.1.1 * u p.1.2))
      ((ν.prod ν).prod (volume.restrict (Ioc (0 : ℝ) (1 / τ)))) := by
  have h1τ : 0 < 1 / τ := by positivity
  have hm := psd3_Phi_meas hum
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun z => ?_, ?_⟩
  · have h := (psd3_h_integrableOn ‖z.1 - z.2‖ h1τ).mul_const (u z.1 * u z.2)
    exact h
  · refine Integrable.mono' (psd3_D_int (τ := τ) hu hlog)
      hm.norm.aestronglyMeasurable.integral_prod_right' (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun v => norm_nonneg _)]
    exact psd3_Phi_norm_le hτ z

/-- Conditional positive definiteness of `kTauLog` on zero-mass finite signed measures `u ν`
with a finite logarithmic moment. -/
theorem kTauLog_cpd {τ : ℝ} (hτ : 0 < τ) {ν : Measure (Euc d)} [IsFiniteMeasure ν]
    {u : Euc d → ℝ} (hum : Measurable u) (hu : Integrable u ν)
    (hlog : Integrable (fun x : Euc d => Real.log (2 + ‖x‖) * u x) ν)
    (hmass : ∫ x, u x ∂ν = 0) :
    0 ≤ ∫ z : Euc d × Euc d, kTauLog d τ (z.1 - z.2) * (u z.1 * u z.2) ∂(ν.prod ν) := by
  set μv : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (1 / τ)) with hμv
  set Φ : (Euc d × Euc d) × ℝ → ℝ := fun p =>
    psd3_h ‖p.1.1 - p.1.2‖ p.2 * (u p.1.1 * u p.1.2) with hΦ
  have hΦi : Integrable Φ ((ν.prod ν).prod μv) := psd3_Phi_int hτ hum hu hlog
  set E : ℝ := ∫ u in Ioi (1 / τ), Real.exp (-u) / u with hE
  have step1 : ∀ z : Euc d × Euc d, kTauLog d τ (z.1 - z.2) * (u z.1 * u z.2) =
      (1 / 2) * ∫ v, Φ (z, v) ∂μv - (1 / 2 * E) * (u z.1 * u z.2) := by
    intro z
    simp only [hΦ, kTauLog, hμv, hE]
    rw [integral_mul_const]
    ring
  have hmi : Integrable (fun z : Euc d × Euc d => u z.1 * u z.2) (ν.prod ν) := hu.mul_prod hu
  have hm0 : ∫ z : Euc d × Euc d, u z.1 * u z.2 ∂(ν.prod ν) = 0 := by
    rw [integral_prod_mul, hmass, zero_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall step1),
    integral_sub (hΦi.integral_prod_left.const_mul _) (hmi.const_mul _), integral_const_mul,
    integral_const_mul, hm0, mul_zero, sub_zero,
    integral_integral_swap (f := fun z v => Φ (z, v)) hΦi]
  refine mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioc fun v hv => ?_)
  have hv0 : 0 < v := hv.1
  have e : ∀ z : Euc d × Euc d, Φ (z, v) =
      v⁻¹ * (Real.exp (-v * ‖z.1 - z.2‖ ^ 2) * u z.1 * u z.2) -
        (v⁻¹ * Real.exp (-v)) * (u z.1 * u z.2) := by
    intro z
    simp only [hΦ, psd3_h]
    have : -(‖z.1 - z.2‖ ^ 2 * v) = -v * ‖z.1 - z.2‖ ^ 2 := by ring
    rw [this]
    field_simp
  simp only [e]
  rw [integral_sub ((psd3_gauss_int hum hu v hv0.le).const_mul _) (hmi.const_mul _),
    integral_const_mul, integral_const_mul, hm0, mul_zero, sub_zero]
  exact mul_nonneg (inv_nonneg.2 hv0.le) (gauss_posdef hum hu hv0)


/-! ### The `L¹` norm of `qTauLog` -/

theorem psd3_gauss_integral {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Euc d => Real.exp (-b * ‖x‖ ^ 2)) ∧
      ∫ x : Euc d, Real.exp (-b * ‖x‖ ^ 2) = (Real.pi / b) ^ ((d : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Euc d) hb
  rw [finrank_euclideanSpace_fin] at h
  refine ⟨Integrable.of_integral_ne_zero ?_, h⟩
  rw [h]
  positivity

theorem psd3_qlog_prod_int (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun p : Euc d × ℝ => Real.exp (-(‖p.1‖ ^ 2 * p.2)) / p.2)
      ((volume : Measure (Euc d)).prod (volume.restrict (Ioi (1 / τ)))) := by
  have h1τ : 0 < 1 / τ := by positivity
  have hm : Measurable (fun p : Euc d × ℝ => Real.exp (-(‖p.1‖ ^ 2 * p.2)) / p.2) :=
    (Real.measurable_exp.comp (((measurable_norm.comp measurable_fst).pow_const 2).mul
      measurable_snd).neg).div measurable_snd
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hnorm : ∀ u ∈ Ioi (1 / τ), ∫ x : Euc d, ‖Real.exp (-(‖x‖ ^ 2 * u)) / u‖ =
      Real.pi ^ ((d : ℝ) / 2) * u ^ (-((d : ℝ) / 2) - 1) := by
    intro u hu
    have hu' : 0 < u := lt_trans h1τ hu
    have e : ∀ x : Euc d, ‖Real.exp (-(‖x‖ ^ 2 * u)) / u‖ =
        u⁻¹ * Real.exp (-u * ‖x‖ ^ 2) := by
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_mul_inv, mul_comm]
      congr 2; ring
    simp only [e]
    rw [integral_const_mul, (psd3_gauss_integral hu').2, Real.div_rpow Real.pi_pos.le hu'.le,
      Real.rpow_sub_one hu'.ne', Real.rpow_neg hu'.le]
    field_simp
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : 0 < u := lt_trans h1τ hu
    have := ((psd3_gauss_integral (d := d) hu').1.const_mul u⁻¹)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [div_eq_mul_inv, mul_comm]
    congr 2; ring
  · have h : IntegrableOn (fun u : ℝ => u ^ (-((d : ℝ) / 2) - 1)) (Ioi (1 / τ)) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) h1τ
    have h2 : IntegrableOn (fun u : ℝ => Real.pi ^ ((d : ℝ) / 2) * u ^ (-((d : ℝ) / 2) - 1))
        (Ioi (1 / τ)) := Integrable.const_mul h _
    exact h2.congr_fun (fun u hu => (hnorm u hu).symm) measurableSet_Ioi

theorem qTauLog_integrable_integral (hd : 1 ≤ d) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (qTauLog d τ) ∧
      ∫ x, qTauLog d τ x = Real.pi ^ ((d : ℝ) / 2) * τ ^ ((d : ℝ) / 2) / d := by
  have h1τ : 0 < 1 / τ := by positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hP := psd3_qlog_prod_int hd hτ
  refine ⟨hP.integral_prod_left.const_mul _, ?_⟩
  have e1 : ∫ x, qTauLog d τ x = (1 / 2) * ∫ x : Euc d, ∫ u in Ioi (1 / τ),
      Real.exp (-(‖x‖ ^ 2 * u)) / u := by
    unfold qTauLog
    rw [integral_const_mul]
  rw [e1, integral_integral_swap (f := fun (x : Euc d) (u : ℝ) => Real.exp (-(‖x‖ ^ 2 * u)) / u) hP]
  have e2 : ∀ u ∈ Ioi (1 / τ), ∫ x : Euc d, Real.exp (-(‖x‖ ^ 2 * u)) / u =
      Real.pi ^ ((d : ℝ) / 2) * u ^ (-((d : ℝ) / 2) - 1) := by
    intro u hu
    have hu' : 0 < u := lt_trans h1τ hu
    have e : ∀ x : Euc d, Real.exp (-(‖x‖ ^ 2 * u)) / u = u⁻¹ * Real.exp (-u * ‖x‖ ^ 2) := by
      intro x
      rw [div_eq_mul_inv, mul_comm]
      congr 2; ring
    simp only [e]
    rw [integral_const_mul, (psd3_gauss_integral hu').2, Real.div_rpow Real.pi_pos.le hu'.le,
      Real.rpow_sub_one hu'.ne', Real.rpow_neg hu'.le]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi e2, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith) h1τ]
  have h3 : -((d : ℝ) / 2) - 1 + 1 = -((d : ℝ) / 2) := by ring
  have hτi : (1 / τ) ^ (-((d : ℝ) / 2)) = τ ^ ((d : ℝ) / 2) := by
    rw [one_div, Real.inv_rpow hτ.le, ← Real.rpow_neg hτ.le, neg_neg]
  rw [h3, hτi]
  have : (-((d : ℝ) / 2)) ≠ 0 := by linarith
  field_simp

end HRS.MS.Psd
