import HRS.Whole.Q34Aux13

/-!
# PSD-3 (part 1): heat split of the Riesz kernel for `0 < s < d`

Namespace `HRS.MS.Psd`.  With the heat kernel `heatKerE d t x = (4πt)^{-d/2} e^{-|x|²/(4t)}`,
`aDS d s = (4π)^{d/2} / (4^{s/2} Γ(s/2))`, `α = (d-s)/2` and the integrand
`psd3_F d s t x = aDS d s * t^{α-1} * heatKerE d t x`, set
`qTau d s τ x = ∫_{(0,τ]} psd3_F` and `kTau d s τ x = ∫_{(τ,∞)} psd3_F`.

Main results (all for `0 < s < d` and `0 < τ`, unless stated):

* `riesz_heat_split`: `rieszKernel d s x = qTau d s τ x + kTau d s τ x` for `x ≠ 0`
  (at `x = 0` the integral defining `qTau` diverges and `qTau 0` is the junk value `0`, so the
  split is only claimed for `x ≠ 0`).
* `qTau_nonneg`, `qTau_integrable_integral`: `0 ≤ qTau`, `qTau` is integrable and
  `∫ qTau = (aDS/α) τ^α` (integrability is part of the statement, so the Bochner value is real).
* `kTau_zero`, `kTau_nonneg`, `kTau_le_zero`: `kTau 0 = 2 aDS/(s (4π)^{d/2}) τ^{-s/2}` and
  `0 ≤ kTau x ≤ kTau 0`; `kTau_continuous`.
* `kTau_posdef`: for every finite measure `ν` and `ν`-integrable measurable `u`
  (that is, every finite signed measure `u ν`, atoms allowed),
  `0 ≤ ∫ kTau (z.1 - z.2) (u z.1 u z.2) d(ν ⊗ ν)`.  No pairing hypothesis is needed because
  `kTau` is bounded.  (Only `0 < s` is used for this one.)

The change of variables `λ = 1/(4t)` (Jacobian `1/(4λ²)`) maps the integrand onto the Laplace
integrand `Γ(s/2)⁻¹ λ^{s/2-1} e^{-|x|²λ}` and gives the split via `Q34.riesz_heat`.
Helper lemmas carry the prefix `psd3_`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.MS.Psd

open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

/-- The heat kernel `p_t(x) = (4πt)^{-d/2} exp(-|x|²/(4t))` on `ℝ^d`. -/
def heatKerE (d : ℕ) (t : ℝ) (x : Euc d) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))

/-- `a_{d,s} = (4π)^{d/2} / (4^{s/2} Γ(s/2))`. -/
def aDS (d : ℕ) (s : ℝ) : ℝ :=
  (4 * Real.pi) ^ ((d : ℝ) / 2) / (4 ^ (s / 2) * Real.Gamma (s / 2))

/-- The integrand `a_{d,s} t^{(d-s)/2-1} p_t(x)` of the heat split. -/
def psd3_F (d : ℕ) (s t : ℝ) (x : Euc d) : ℝ :=
  aDS d s * t ^ (((d : ℝ) - s) / 2 - 1) * heatKerE d t x

/-- `q_τ = a_{d,s} ∫_0^τ t^{α-1} p_t dt`. -/
def qTau (d : ℕ) (s τ : ℝ) (x : Euc d) : ℝ := ∫ t in Ioc (0 : ℝ) τ, psd3_F d s t x

/-- `k_τ = a_{d,s} ∫_τ^∞ t^{α-1} p_t dt`. -/
def kTau (d : ℕ) (s τ : ℝ) (x : Euc d) : ℝ := ∫ t in Ioi τ, psd3_F d s t x

/-! ### Elementary facts on the integrand -/

theorem psd3_aDS_pos {s : ℝ} (hs : 0 < s) : 0 < aDS d s := by
  unfold aDS
  have : 0 < Real.Gamma (s / 2) := Real.Gamma_pos_of_pos (by linarith)
  positivity

theorem psd3_heat_nonneg {t : ℝ} (ht : 0 ≤ t) (x : Euc d) : 0 ≤ heatKerE d t x := by
  unfold heatKerE
  positivity

theorem psd3_F_nonneg {s : ℝ} (hs : 0 < s) {t : ℝ} (ht : 0 ≤ t) (x : Euc d) :
    0 ≤ psd3_F d s t x := by
  unfold psd3_F
  have := psd3_aDS_pos (d := d) hs
  have := psd3_heat_nonneg (d := d) ht x
  positivity

theorem psd3_F_meas (s : ℝ) : Measurable (fun p : ℝ × Euc d => psd3_F d s p.1 p.2) := by
  unfold psd3_F heatKerE
  have h1 : Measurable (fun p : ℝ × Euc d => p.1) := measurable_fst
  have h2 : Measurable (fun p : ℝ × Euc d => ‖p.2‖) := measurable_norm.comp measurable_snd
  refine (measurable_const.mul (h1.pow_const _)).mul ?_
  refine (((measurable_const.mul h1).pow_const _)).mul ?_
  exact Real.measurable_exp.comp (((h2.pow_const 2).neg).div (measurable_const.mul h1))

theorem psd3_F_meas_t (s : ℝ) (x : Euc d) : Measurable (fun t : ℝ => psd3_F d s t x) :=
  (psd3_F_meas (d := d) s).comp (measurable_id.prodMk measurable_const)

theorem psd3_F_meas_x (s t : ℝ) : Measurable (fun x : Euc d => psd3_F d s t x) :=
  (psd3_F_meas (d := d) s).comp (measurable_const.prodMk measurable_id)

/-- The value `∫ p_t = 1`. -/
theorem psd3_heat_integral {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Euc d => heatKerE d t x) ∧ ∫ x : Euc d, heatKerE d t x = 1 := by
  have hb : 0 < 1 / (4 * t) := by positivity
  have e : (fun x : Euc d => heatKerE d t x) =
      fun x => (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2) := by
    funext x
    unfold heatKerE
    congr 2
    field_simp
  have hG : ∫ x : Euc d, Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2) = (4 * Real.pi * t) ^ ((d : ℝ) / 2) := by
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, finrank_euclideanSpace_fin]
    congr 1
    field_simp
  have hGi : Integrable (fun x : Euc d => Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2)) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
    positivity
  rw [e]
  refine ⟨hGi.const_mul _, ?_⟩
  rw [integral_const_mul, hG, ← Real.rpow_add (by positivity)]
  have : -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 := by ring
  rw [this, Real.rpow_zero]

/-- The value at the origin: `a t^{α-1} (4πt)^{-d/2} = a (4π)^{-d/2} t^{-s/2-1}`. -/
theorem psd3_F_zero {s : ℝ} {t : ℝ} (ht : 0 < t) :
    psd3_F d s t 0 = aDS d s * (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(s / 2) - 1) := by
  unfold psd3_F heatKerE
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero,
    zero_div, Real.exp_zero, mul_one]
  have e : t ^ (((d : ℝ) - s) / 2 - 1) * t ^ (-(d : ℝ) / 2) = t ^ (-(s / 2) - 1) := by
    rw [← Real.rpow_add ht]; congr 1; ring
  rw [Real.mul_rpow (by positivity) ht.le]
  calc _ = aDS d s * (4 * Real.pi) ^ (-(d : ℝ) / 2) *
        (t ^ (((d : ℝ) - s) / 2 - 1) * t ^ (-(d : ℝ) / 2)) := by ring
    _ = _ := by rw [e]

theorem psd3_F_le_zero {s : ℝ} (hs : 0 < s) {t : ℝ} (ht : 0 < t) (x : Euc d) :
    psd3_F d s t x ≤ psd3_F d s t 0 := by
  unfold psd3_F heatKerE
  have h1 := psd3_aDS_pos (d := d) hs
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply Real.exp_le_exp.2
  simp only [norm_zero]
  have : 0 ≤ ‖x‖ ^ 2 / (4 * t) := by positivity
  rw [neg_div]
  simp
  linarith

/-- The majorant is integrable on `(τ, ∞)`. -/
theorem psd3_F_zero_integrableOn {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun t : ℝ => psd3_F d s t 0) (Ioi τ) := by
  have h : IntegrableOn (fun t : ℝ => t ^ (-(s / 2) - 1)) (Ioi τ) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hτ
  have h2 : IntegrableOn (fun t : ℝ => aDS d s * (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(s / 2) - 1))
      (Ioi τ) := Integrable.const_mul h _
  refine h2.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have : 0 < t := lt_trans hτ ht
  simp only
  rw [psd3_F_zero this]

theorem psd3_F_integrableOn {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) (x : Euc d) :
    IntegrableOn (fun t : ℝ => psd3_F d s t x) (Ioi τ) := by
  refine Integrable.mono' (psd3_F_zero_integrableOn (d := d) hs hτ)
    (psd3_F_meas_t (d := d) s x).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have : 0 < t := lt_trans hτ ht
  rw [Real.norm_eq_abs, abs_of_nonneg (psd3_F_nonneg hs this.le x)]
  exact psd3_F_le_zero hs this x

/-! ### Properties of `kTau` -/

theorem kTau_nonneg {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) (x : Euc d) :
    0 ≤ kTau d s τ x := by
  unfold kTau
  refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
  exact psd3_F_nonneg hs (lt_trans hτ ht).le x

theorem kTau_le_zero {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) (x : Euc d) :
    kTau d s τ x ≤ kTau d s τ 0 := by
  unfold kTau
  refine setIntegral_mono_on (psd3_F_integrableOn hs hτ x) (psd3_F_zero_integrableOn hs hτ)
    measurableSet_Ioi fun t ht => psd3_F_le_zero hs (lt_trans hτ ht) x

theorem kTau_zero {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) :
    kTau d s τ 0 = 2 * aDS d s / (s * (4 * Real.pi) ^ ((d : ℝ) / 2)) * τ ^ (-(s / 2)) := by
  unfold kTau
  have e : ∫ t in Ioi τ, psd3_F d s t (0 : Euc d) =
      ∫ t in Ioi τ, aDS d s * (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(s / 2) - 1) :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => psd3_F_zero (lt_trans hτ ht)
  rw [e, integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hτ]
  have h1 : -(s / 2) - 1 + 1 = -(s / 2) := by ring
  rw [h1]
  have h2 : (4 * Real.pi) ^ (-(d : ℝ) / 2) = ((4 * Real.pi) ^ ((d : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg (by positivity)]; congr 1; ring
  rw [h2]
  have : 0 < (4 * Real.pi) ^ ((d : ℝ) / 2) := by positivity
  field_simp

theorem kTau_continuous {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) :
    Continuous (kTau d s τ) := by
  unfold kTau
  refine continuous_of_dominated (bound := fun t => psd3_F d s t 0)
    (fun x => (psd3_F_meas_t (d := d) s x).aestronglyMeasurable) (fun x => ?_)
    (psd3_F_zero_integrableOn hs hτ) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have : 0 < t := lt_trans hτ ht
    rw [Real.norm_eq_abs, abs_of_nonneg (psd3_F_nonneg hs this.le x)]
    exact psd3_F_le_zero hs this x
  · refine Filter.Eventually.of_forall fun t => ?_
    unfold psd3_F heatKerE
    fun_prop


theorem psd3_F_eq_gauss {s : ℝ} {t : ℝ} (ht : 0 < t) (x : Euc d) :
    psd3_F d s t x = psd3_F d s t 0 * Real.exp (-(1 / (4 * t)) * ‖x‖ ^ 2) := by
  unfold psd3_F heatKerE
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero,
    zero_div, Real.exp_zero, mul_one]
  have : -‖x‖ ^ 2 / (4 * t) = -(1 / (4 * t)) * ‖x‖ ^ 2 := by field_simp
  rw [this]
  ring

/-- Positive definiteness of `kTau` on every finite signed measure `u ν` (atoms allowed). -/
theorem kTau_posdef {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) {ν : Measure (Euc d)}
    [IsFiniteMeasure ν] {u : Euc d → ℝ} (hum : Measurable u) (hu : Integrable u ν) :
    0 ≤ ∫ z : Euc d × Euc d, kTau d s τ (z.1 - z.2) * (u z.1 * u z.2) ∂(ν.prod ν) := by
  set μt : Measure ℝ := volume.restrict (Ioi τ) with hμt
  set Φ : (Euc d × Euc d) × ℝ → ℝ := fun p =>
    psd3_F d s p.2 (p.1.1 - p.1.2) * (u p.1.1 * u p.1.2) with hΦ
  have hΦm : Measurable Φ := by
    have h1 : Measurable (fun p : (Euc d × Euc d) × ℝ => (p.2, p.1.1 - p.1.2)) :=
      measurable_snd.prodMk ((measurable_fst.comp measurable_fst).sub
        (measurable_snd.comp measurable_fst))
    exact ((psd3_F_meas (d := d) s).comp h1).mul
      ((hum.comp (measurable_fst.comp measurable_fst)).mul
        (hum.comp (measurable_snd.comp measurable_fst)))
  have hmaj : Integrable (fun z : Euc d × Euc d => |u z.1| * |u z.2|) (ν.prod ν) :=
    hu.abs.mul_prod hu.abs
  have hmaj2 := hmaj.mul_prod (psd3_F_zero_integrableOn (d := d) hs hτ)
  have hΦi : Integrable Φ ((ν.prod ν).prod μt) := by
    refine Integrable.mono' hmaj2 hΦm.aestronglyMeasurable ?_
    have h2 : ∀ᵐ p ∂((ν.prod ν).prod μt), 0 < p.2 := by
      have hm : MeasurableSet {p : (Euc d × Euc d) × ℝ | 0 < p.2} :=
        measurableSet_lt measurable_const measurable_snd
      refine (Measure.ae_prod_mem_iff_ae_ae_mem hm).2 (Filter.Eventually.of_forall fun z => ?_)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using lt_trans hτ ht
    filter_upwards [h2] with p hp
    simp only [hΦ, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (psd3_F_nonneg hs hp.le _)]
    calc psd3_F d s p.2 (p.1.1 - p.1.2) * (|u p.1.1| * |u p.1.2|)
        ≤ psd3_F d s p.2 0 * (|u p.1.1| * |u p.1.2|) := by
          gcongr; exact psd3_F_le_zero hs hp _
      _ = _ := by ring
  have step1 : ∀ z : Euc d × Euc d, kTau d s τ (z.1 - z.2) * (u z.1 * u z.2) =
      ∫ t, Φ (z, t) ∂μt := by
    intro z
    simp only [hΦ, kTau, hμt]
    rw [integral_mul_const]
  rw [integral_congr_ae (Filter.Eventually.of_forall step1)]
  rw [integral_integral_swap (f := fun z t => Φ (z, t)) hΦi]
  refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := lt_trans hτ ht
  have e : ∀ z : Euc d × Euc d, Φ (z, t) = psd3_F d s t 0 *
      (Real.exp (-(1 / (4 * t)) * ‖z.1 - z.2‖ ^ 2) * u z.1 * u z.2) := by
    intro z
    simp only [hΦ]
    rw [psd3_F_eq_gauss ht0]
    ring
  simp only [e]
  rw [integral_const_mul]
  exact mul_nonneg (psd3_F_nonneg hs ht0.le 0)
    (gauss_posdef hum hu (by positivity : 0 < 1 / (4 * t)))


/-! ### `qTau`: nonnegativity and `L¹` norm -/

theorem qTau_nonneg {s : ℝ} (hs : 0 < s) {τ : ℝ} (x : Euc d) : 0 ≤ qTau d s τ x := by
  unfold qTau
  exact setIntegral_nonneg measurableSet_Ioc fun t ht => psd3_F_nonneg hs ht.1.le x

theorem psd3_q_prod_int {s : ℝ} (hs : 0 < s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun p : Euc d × ℝ => psd3_F d s p.2 p.1)
      ((volume : Measure (Euc d)).prod (volume.restrict (Ioc (0 : ℝ) τ))) := by
  have hm : Measurable (fun p : Euc d × ℝ => psd3_F d s p.2 p.1) :=
    (psd3_F_meas (d := d) s).comp measurable_swap
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  have hαa : -1 < ((d : ℝ) - s) / 2 - 1 := by linarith
  have hnorm : ∀ t ∈ Ioc (0 : ℝ) τ, ∫ x : Euc d, ‖psd3_F d s t x‖ =
      aDS d s * t ^ (((d : ℝ) - s) / 2 - 1) := by
    intro t ht
    have : ∀ x : Euc d, ‖psd3_F d s t x‖ = (aDS d s * t ^ (((d : ℝ) - s) / 2 - 1)) *
        heatKerE d t x := by
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (psd3_F_nonneg hs ht.1.le x)]
      rfl
    simp only [this]
    rw [integral_const_mul, (psd3_heat_integral ht.1).2, mul_one]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have := (psd3_heat_integral (d := d) ht.1).1.const_mul
      (aDS d s * t ^ (((d : ℝ) - s) / 2 - 1))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    rfl
  · have h1 : IntegrableOn (fun t : ℝ => t ^ (((d : ℝ) - s) / 2 - 1)) (Ioc 0 τ) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).1 (intervalIntegral.intervalIntegrable_rpow' hαa)
    have h2 : IntegrableOn (fun t : ℝ => aDS d s * t ^ (((d : ℝ) - s) / 2 - 1)) (Ioc 0 τ) :=
      Integrable.const_mul h1 _
    refine h2.congr_fun (fun t ht => (hnorm t ht).symm) measurableSet_Ioc

theorem qTau_integrable_integral {s : ℝ} (hs : 0 < s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (qTau d s τ) ∧
      ∫ x, qTau d s τ x = aDS d s / (((d : ℝ) - s) / 2) * τ ^ (((d : ℝ) - s) / 2) := by
  have hP := psd3_q_prod_int (d := d) hs hsd hτ
  refine ⟨hP.integral_prod_left, ?_⟩
  have hαa : -1 < ((d : ℝ) - s) / 2 - 1 := by linarith
  have hα : 0 < ((d : ℝ) - s) / 2 := by linarith
  have e1 : ∫ x, qTau d s τ x = ∫ t in Ioc (0 : ℝ) τ, ∫ x : Euc d, psd3_F d s t x ∂volume := by
    exact integral_integral_swap (f := fun (x : Euc d) (t : ℝ) => psd3_F d s t x) hP
  rw [e1]
  have e2 : ∫ t in Ioc (0 : ℝ) τ, ∫ x : Euc d, psd3_F d s t x =
      ∫ t in Ioc (0 : ℝ) τ, aDS d s * t ^ (((d : ℝ) - s) / 2 - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have : ∀ x : Euc d, psd3_F d s t x = (aDS d s * t ^ (((d : ℝ) - s) / 2 - 1)) *
        heatKerE d t x := fun x => rfl
    simp only [this]
    rw [integral_const_mul, (psd3_heat_integral ht.1).2, mul_one]
  rw [e2, integral_const_mul, ← intervalIntegral.integral_of_le hτ.le,
    integral_rpow (Or.inl hαa)]
  have h3 : ((d : ℝ) - s) / 2 - 1 + 1 = ((d : ℝ) - s) / 2 := by ring
  rw [h3, Real.zero_rpow hα.ne']
  ring


/-! ### The split, by the change of variables `λ = 1/(4t)` -/

/-- The Laplace integrand `Γ(s/2)⁻¹ λ^{s/2-1} e^{-|x|²λ}`. -/
def psd3_psi (d : ℕ) (s : ℝ) (x : Euc d) (l : ℝ) : ℝ :=
  (Real.Gamma (s / 2))⁻¹ * (l ^ (s / 2 - 1) * Real.exp (-(‖x‖ ^ 2 * l)))

theorem psd3_pointwise {s : ℝ} (hs : 0 < s) (x : Euc d) {l : ℝ} (hl : 0 < l) :
    |(-4 / (4 * l) ^ 2)| • psd3_F d s ((4 * l)⁻¹) x = psd3_psi d s x l := by
  have h4l : 0 < 4 * l := by positivity
  have ht : 0 < (4 * l)⁻¹ := inv_pos.2 h4l
  rw [smul_eq_mul, psd3_F_eq_gauss ht, psd3_F_zero ht]
  have hG : 0 < Real.Gamma (s / 2) := Real.Gamma_pos_of_pos (by linarith)
  have e1 : ((4 * l)⁻¹) ^ (-(s / 2) - 1) = 4 ^ (s / 2) * 4 * (l ^ (s / 2) * l) := by
    rw [Real.inv_rpow h4l.le, ← inv_inv ((4 * l) ^ (-(s / 2) - 1)), ← Real.rpow_neg h4l.le,
      Real.mul_rpow (by norm_num) hl.le]
    have : -(-(s / 2) - 1) = s / 2 + 1 := by ring
    rw [this, Real.rpow_add (by norm_num), Real.rpow_add hl, Real.rpow_one, Real.rpow_one, inv_inv]
  have e2 : -(1 / (4 * (4 * l)⁻¹)) * ‖x‖ ^ 2 = -(‖x‖ ^ 2 * l) := by
    field_simp
  have e3 : (4 * Real.pi) ^ (-(d : ℝ) / 2) = ((4 * Real.pi) ^ ((d : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg (by positivity)]; congr 1; ring
  have e4 : l ^ (s / 2 - 1) = l ^ (s / 2) / l := Real.rpow_sub_one hl.ne' _
  have e5 : |(-4 / (4 * l) ^ 2)| = 4 / (4 * l) ^ 2 := by
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_pos (by positivity)]
  rw [e1, e2, e3, e5]
  unfold psd3_psi aDS
  rw [e4]
  have hA : 0 < (4 * Real.pi) ^ ((d : ℝ) / 2) := by positivity
  have hB : 0 < (4 : ℝ) ^ (s / 2) := by positivity
  have hC : 0 < l ^ (s / 2) := by positivity
  field_simp

theorem psd3_image : (fun l : ℝ => (4 * l)⁻¹) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
  ext t
  constructor
  · rintro ⟨l, hl, rfl⟩
    have hl' : (0:ℝ) < l := hl
    exact inv_pos.2 (by positivity : (0:ℝ) < 4 * l)
  · intro ht
    have ht' : (0:ℝ) < t := ht
    refine ⟨(4 * t)⁻¹, inv_pos.2 (by positivity : (0:ℝ) < 4 * t), ?_⟩
    simp only
    field_simp

theorem psd3_cov {s : ℝ} (hs : 0 < s) (x : Euc d) :
    (IntegrableOn (fun t : ℝ => psd3_F d s t x) (Ioi (0 : ℝ)) ↔
      IntegrableOn (psd3_psi d s x) (Ioi (0 : ℝ))) ∧
    ∫ t in Ioi (0 : ℝ), psd3_F d s t x = ∫ l in Ioi (0 : ℝ), psd3_psi d s x l := by
  have hder : ∀ l ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun l : ℝ => (4 * l)⁻¹) (-4 / (4 * l) ^ 2) (Ioi (0 : ℝ)) l := by
    intro l hl
    have hl' : (0:ℝ) < l := hl
    have h : HasDerivAt (fun l : ℝ => 4 * l) 4 l := by
      simpa using (hasDerivAt_id l).const_mul (4 : ℝ)
    exact (h.inv (by positivity)).hasDerivWithinAt
  have hinj : InjOn (fun l : ℝ => (4 * l)⁻¹) (Ioi (0 : ℝ)) := by
    intro a ha b hb hab
    have ha' : (0:ℝ) < a := ha
    have hb' : (0:ℝ) < b := hb
    simp only [inv_inj] at hab
    linarith
  have hcongr : ∀ l ∈ Ioi (0 : ℝ), |(-4 / (4 * l) ^ 2)| • psd3_F d s ((4 * l)⁻¹) x =
      psd3_psi d s x l := fun l hl => psd3_pointwise hs x hl
  have hI := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hder hinj
    (fun t : ℝ => psd3_F d s t x)
  have hV := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj
    (fun t : ℝ => psd3_F d s t x)
  rw [psd3_image] at hI hV
  refine ⟨?_, ?_⟩
  · rw [hI]
    exact integrableOn_congr_fun hcongr measurableSet_Ioi
  · rw [hV]
    exact setIntegral_congr_fun measurableSet_Ioi hcongr

/-- The heat split of the Riesz kernel: `|x|^{-s} = qTau x + kTau x` for `x ≠ 0` and `0 < s`
(the hypothesis `s < d` is not needed for the identity). -/
theorem riesz_heat_split {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) {x : Euc d} (hx : x ≠ 0) :
    rieszKernel d s x = qTau d s τ x + kTau d s τ x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hG : 0 < Real.Gamma (s / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hψ : IntegrableOn (psd3_psi d s x) (Ioi (0 : ℝ)) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s / 2 - 1) (b := ‖x‖ ^ 2)
      (by linarith) one_pos (by positivity)
    have h2 : IntegrableOn (fun l : ℝ => (Real.Gamma (s / 2))⁻¹ *
        (l ^ (s / 2 - 1) * Real.exp (-(‖x‖ ^ 2 * l)))) (Ioi (0 : ℝ)) := by
      refine Integrable.const_mul ?_ _
      refine this.congr_fun (fun l hl => ?_) measurableSet_Ioi
      simp only [Real.rpow_one]
      rw [neg_mul]
    exact h2
  obtain ⟨hi, hv⟩ := psd3_cov hs x
  have hF := hi.2 hψ
  have hint : ∫ t in Ioi (0 : ℝ), psd3_F d s t x = ‖x‖ ^ (-s) := by
    rw [hv]
    unfold psd3_psi
    rw [integral_const_mul]
    have := riesz_heat hs x
    rw [← this]
    field_simp
  have hsplit : ∫ t in Ioi (0 : ℝ), psd3_F d s t x =
      (∫ t in Ioc (0 : ℝ) τ, psd3_F d s t x) + ∫ t in Ioi τ, psd3_F d s t x := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hτ.le]
    refine setIntegral_union ?_ measurableSet_Ioi ?_ ?_
    · exact Set.disjoint_left.2 fun t h1 h2 => absurd h1.2 (not_le.2 h2)
    · exact hF.mono_set (by rw [← Set.Ioc_union_Ioi_eq_Ioi hτ.le]; exact subset_union_left)
    · exact hF.mono_set (by rw [← Set.Ioc_union_Ioi_eq_Ioi hτ.le]; exact subset_union_right)
  rw [rieszKernel_eq hs.ne', ← hint, hsplit]
  rfl

end HRS.MS.Psd
