import HRS.MS.PsdAux1
import HRS.Energy.Commutator.SliceAux

/-!
# PSD-2: the logarithmic (`s = 0`) energy is nonnegative on mass-zero signed densities

Statement (namespace `HRS.MS.Psd`): for `1 ≤ d`, `f` integrable with `∫ f = 0` and absolutely
convergent pairing `hI` of `rieszKernel d 0 = -log |·|`, the iterated integral
`∫ x, ∫ y, (-log |x-y|) f x f y` is `≥ 0`.

Both hypotheses are needed: without `hI` the Bochner integral is the junk value `0`, and without
the mass condition the claim is false (a probability density spread over a large ball has negative
log energy).

Route.  For `r > 0`, the Frullani identity `∫_0^∞ t⁻¹ (e^{-t r²} - e^{-t}) dt = log (1/r²) = 2 (-log r)`
(`HRS.Commutator.SliceAux.xside_value` at `s = 0`).  The integrand `t⁻¹ (e^{-t r²} - e^{-t})` has the
sign of `1 - r²` for all `t`, so `∫_t |·| = |∫_t ·| = 2 |log r|`, and absolute integrability of the
triple integrand over `(x, y, t)` is exactly `hI` (no extra hypothesis).  Fubini in `(t, x, y)`,
`HRS.Whole.Q34.gauss_posdef` for each fixed `t` (via `ν = |f| dx`, `u = sign f`) and `∫ f = 0` to kill
the constant `e^{-t}` give `2 E(f) = ∫_0^∞ t⁻¹ G(t) dt ≥ 0`.
Helper lemmas carry the prefix `psd2_`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.MS.Psd

open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

/-- Transfer of a translation-invariant pairing between `|f| dx` (with the sign `u`) and `dx`. -/
theorem psd2_transfer {f : Euc d → ℝ} (hfm : Measurable f) (k : Euc d → ℝ) :
    ∫ z, k (z.1 - z.2) * (psd1_sgn f z.1 * psd1_sgn f z.2)
        ∂((HRS.Whole.withDensityReal fun x => ‖f x‖).prod (HRS.Whole.withDensityReal fun x => ‖f x‖)) =
      ∫ z, k (z.1 - z.2) * (f z.1 * f z.2) ∂((volume : Measure (Euc d)).prod volume) := by
  set ρ : Euc d → ℝ := fun x => ‖f x‖ with hρ
  have hρm : Measurable ρ := hfm.norm
  set w : Euc d → ℝ≥0∞ := fun x => ENNReal.ofReal (ρ x) with hw
  have hwm : Measurable w := ENNReal.measurable_ofReal.comp hρm
  have hprod : (HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ) =
      (volume.prod volume).withDensity (fun z : Euc d × Euc d => w z.1 * w z.2) := by
    simp only [HRS.Whole.withDensityReal]
    exact prod_withDensity hwm hwm
  have hwm2 : Measurable (fun z : Euc d × Euc d => w z.1 * w z.2) :=
    (hwm.comp measurable_fst).mul (hwm.comp measurable_snd)
  have hlt : ∀ᵐ z ∂(volume.prod volume : Measure (Euc d × Euc d)), w z.1 * w z.2 < ∞ :=
    Filter.Eventually.of_forall fun z =>
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  rw [hprod, integral_withDensity_eq_integral_toReal_smul hwm2 hlt]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [ENNReal.toReal_mul, hw]
  simp only [ENNReal.toReal_ofReal (norm_nonneg _), hρ, smul_eq_mul]
  have e : f z.1 * f z.2 = (‖f z.1‖ * psd1_sgn f z.1) * (‖f z.2‖ * psd1_sgn f z.2) := by
    rw [psd1_norm_mul_sgn f z.1, psd1_norm_mul_sgn f z.2]
  rw [e]
  ring

/-- The Gaussian pairing of an integrable measurable `f` is nonnegative. -/
theorem psd2_gauss {f : Euc d → ℝ} (hfm : Measurable f) (hf : Integrable f) {t : ℝ} (ht : 0 < t) :
    0 ≤ ∫ z, Real.exp (-(‖z.1 - z.2‖ ^ 2 * t)) * (f z.1 * f z.2)
      ∂((volume : Measure (Euc d)).prod volume) := by
  have hν : IsFiniteMeasure (HRS.Whole.withDensityReal fun x => ‖f x‖) :=
    isFiniteMeasure_withDensity_ofReal hf.norm.hasFiniteIntegral
  have hum : Measurable (psd1_sgn f) := psd1_sgn_measurable hfm
  have huν : Integrable (psd1_sgn f) (HRS.Whole.withDensityReal fun x => ‖f x‖) :=
    Integrable.of_bound hum.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => psd1_sgn_abs f x)
  have key := gauss_posdef (ν := HRS.Whole.withDensityReal fun x => ‖f x‖) hum huν ht
  have h2 := psd2_transfer hfm (fun z => Real.exp (-(‖z‖ ^ 2 * t)))
  have h3 : ∫ z, Real.exp (-t * ‖z.1 - z.2‖ ^ 2) * psd1_sgn f z.1 * psd1_sgn f z.2
      ∂((HRS.Whole.withDensityReal fun x => ‖f x‖).prod (HRS.Whole.withDensityReal fun x => ‖f x‖)) =
      ∫ z, Real.exp (-(‖z.1 - z.2‖ ^ 2 * t)) * (psd1_sgn f z.1 * psd1_sgn f z.2)
      ∂((HRS.Whole.withDensityReal fun x => ‖f x‖).prod (HRS.Whole.withDensityReal fun x => ‖f x‖)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [mul_assoc]
    congr 2
    ring
  rw [h3] at key
  rw [h2] at key
  exact key

/-- The Frullani integrand `t^{-1} (e^{-r² t} - e^{-t})`, in the exact shape of `xside_value`. -/
def psd2_g (r t : ℝ) : ℝ :=
  t ^ ((0 : ℝ) / 2 - 1) * (Real.exp (-(r ^ 2 * t)) - Real.exp (-(1 * t)))

theorem psd2_g_int {r : ℝ} (hr : 0 < r) : IntegrableOn (psd2_g r) (Ioi (0 : ℝ)) :=
  HRS.Commutator.SliceAux.xside_integrable (le_refl (0 : ℝ)) (A := r ^ 2) (B := 1)
    (by positivity) one_pos

theorem psd2_g_val {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), psd2_g r t = 2 * (-Real.log r) := by
  have := HRS.Commutator.SliceAux.xside_value (le_refl (0 : ℝ)) (A := r ^ 2) (B := 1)
    (by positivity) one_pos
  rw [if_pos rfl] at this
  have e : Real.log (1 / r ^ 2) = 2 * (-Real.log r) := by
    rw [one_div, Real.log_inv, Real.log_pow]; push_cast; ring
  rw [← e, ← this]
  rfl

theorem psd2_g_nonneg {r : ℝ} (hr : 0 < r) (h1 : r ≤ 1) {t : ℝ} (ht : 0 < t) : 0 ≤ psd2_g r t := by
  unfold psd2_g
  refine mul_nonneg (Real.rpow_nonneg ht.le _) ?_
  rw [sub_nonneg]
  apply Real.exp_le_exp.2
  have : r ^ 2 ≤ 1 := by nlinarith
  nlinarith

theorem psd2_g_nonpos {r : ℝ} (h1 : 1 ≤ r) {t : ℝ} (ht : 0 < t) : psd2_g r t ≤ 0 := by
  unfold psd2_g
  refine mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg ht.le _) ?_
  rw [sub_nonpos]
  apply Real.exp_le_exp.2
  have : 1 ≤ r ^ 2 := by nlinarith
  nlinarith

theorem psd2_g_abs {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), ‖psd2_g r t‖ = 2 * |Real.log r| := by
  rcases le_total r 1 with h | h
  · have e : ∫ t in Ioi (0 : ℝ), ‖psd2_g r t‖ = ∫ t in Ioi (0 : ℝ), psd2_g r t := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (psd2_g_nonneg hr h ht)]
    rw [e, psd2_g_val hr, abs_of_nonpos (Real.log_nonpos hr.le h)]
  · have e : ∫ t in Ioi (0 : ℝ), ‖psd2_g r t‖ = -∫ t in Ioi (0 : ℝ), psd2_g r t := by
      rw [← integral_neg]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [Real.norm_eq_abs, abs_of_nonpos (psd2_g_nonpos h ht)]
    rw [e, psd2_g_val hr, abs_of_nonneg (Real.log_nonneg h)]
    ring

/-- Core case of PSD-2: `f` measurable, as an integral over the product. -/
theorem psd2_core (hd : 1 ≤ d) {f : Euc d → ℝ} (hfm : Measurable f) (hf : Integrable f)
    (hmass : ∫ x, f x = 0)
    (hI : Integrable (fun p : Euc d × Euc d => rieszKernel d 0 (p.1 - p.2) * (f p.1 * f p.2))
      (volume.prod volume)) :
    0 ≤ ∫ p : Euc d × Euc d, rieszKernel d 0 (p.1 - p.2) * (f p.1 * f p.2)
      ∂(volume.prod volume) := by
  set μ2 : Measure (Euc d × Euc d) := (volume : Measure (Euc d)).prod volume with hμ2
  set μt : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμt
  have hK : ∀ z : Euc d, rieszKernel d 0 z = -Real.log ‖z‖ := fun z => by simp [rieszKernel]
  set Ψ : (Euc d × Euc d) × ℝ → ℝ :=
    fun q => psd2_g ‖q.1.1 - q.1.2‖ q.2 * (f q.1.1 * f q.1.2) with hΨ
  have hff : Integrable (fun z : Euc d × Euc d => f z.1 * f z.2) μ2 := hf.mul_prod hf
  have hΨm : Measurable Ψ := by
    have h1 : Measurable (fun q : (Euc d × Euc d) × ℝ => q.2 ^ ((0 : ℝ) / 2 - 1)) :=
      measurable_snd.pow_const _
    have h2 : Measurable (fun q : (Euc d × Euc d) × ℝ =>
        Real.exp (-(‖q.1.1 - q.1.2‖ ^ 2 * q.2)) - Real.exp (-(1 * q.2))) := by
      have a1 : Measurable (fun q : (Euc d × Euc d) × ℝ => ‖q.1.1 - q.1.2‖ ^ 2 * q.2) :=
        ((measurable_norm.comp ((measurable_fst.comp measurable_fst).sub
          (measurable_snd.comp measurable_fst))).pow_const 2).mul measurable_snd
      exact (Real.measurable_exp.comp a1.neg).sub
        (Real.measurable_exp.comp (measurable_snd.const_mul 1).neg)
    exact (h1.mul h2).mul
      ((hfm.comp (measurable_fst.comp measurable_fst)).mul (hfm.comp (measurable_snd.comp measurable_fst)))
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hdiag : ∀ᵐ z ∂μ2, z.1 ≠ z.2 := diag_ae (volume : Measure (Euc d))
  -- integrability on the triple product
  have hΨi : Integrable Ψ (μ2.prod μt) := by
    rw [integrable_prod_iff hΨm.aestronglyMeasurable]
    refine ⟨?_, ?_⟩
    · filter_upwards [hdiag] with z hz
      have hr : 0 < ‖z.1 - z.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
      exact (psd2_g_int hr).mul_const (f z.1 * f z.2)
    · have hae : (fun z : Euc d × Euc d => 2 * ‖rieszKernel d 0 (z.1 - z.2) * (f z.1 * f z.2)‖)
          =ᵐ[μ2] fun z => ∫ t, ‖Ψ (z, t)‖ ∂μt := by
        filter_upwards [hdiag] with z hz
        have hr : 0 < ‖z.1 - z.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
        have e : ∫ t, ‖Ψ (z, t)‖ ∂μt =
            (∫ t in Ioi (0 : ℝ), ‖psd2_g ‖z.1 - z.2‖ t‖) * ‖f z.1 * f z.2‖ := by
          rw [← integral_mul_const]
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          simp only [hΨ, norm_mul]
        rw [e, psd2_g_abs hr, norm_mul, hK, Real.norm_eq_abs, abs_neg, Real.norm_eq_abs]
        ring
      exact (hI.norm.const_mul 2).congr hae
  have hswap := integral_integral_swap (μ := μ2) (ν := μt) (f := fun z t => Ψ (z, t)) hΨi
  -- left side
  have hL : ∫ z, ∫ t, Ψ (z, t) ∂μt ∂μ2 =
      2 * ∫ z, rieszKernel d 0 (z.1 - z.2) * (f z.1 * f z.2) ∂μ2 := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hdiag] with z hz
    have hr : 0 < ‖z.1 - z.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
    have e : ∫ t, Ψ (z, t) ∂μt = (∫ t in Ioi (0 : ℝ), psd2_g ‖z.1 - z.2‖ t) * (f z.1 * f z.2) := by
      rw [← integral_mul_const]
    rw [e, psd2_g_val hr, hK]
    ring
  -- right side
  have hR : ∀ t : ℝ, 0 < t → 0 ≤ ∫ z, Ψ (z, t) ∂μ2 := by
    intro t ht
    have hE : Integrable (fun z : Euc d × Euc d =>
        Real.exp (-(‖z.1 - z.2‖ ^ 2 * t)) * (f z.1 * f z.2)) μ2 := by
      refine Integrable.mono' hff.norm ?_ (Filter.Eventually.of_forall fun z => ?_)
      · have : Measurable (fun z : Euc d × Euc d =>
            Real.exp (-(‖z.1 - z.2‖ ^ 2 * t)) * (f z.1 * f z.2)) :=
          (Real.measurable_exp.comp (((measurable_norm.comp (measurable_fst.sub
            measurable_snd)).pow_const 2).mul_const t).neg).mul
            ((hfm.comp measurable_fst).mul (hfm.comp measurable_snd))
        exact this.aestronglyMeasurable
      · have h1 : Real.exp (-(‖z.1 - z.2‖ ^ 2 * t)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖z.1 - z.2‖]
        rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        calc _ ≤ 1 * ‖f z.1 * f z.2‖ := by gcongr
          _ = _ := one_mul _
    have hC : Integrable (fun z : Euc d × Euc d => Real.exp (-(1 * t)) * (f z.1 * f z.2)) μ2 :=
      hff.const_mul _
    have hz0 : ∫ z, f z.1 * f z.2 ∂μ2 = 0 := by
      rw [hμ2, integral_prod_mul f f, hmass, zero_mul]
    have e : ∫ z, Ψ (z, t) ∂μ2 = t ^ ((0 : ℝ) / 2 - 1) *
        ∫ z, Real.exp (-(‖z.1 - z.2‖ ^ 2 * t)) * (f z.1 * f z.2) ∂μ2 := by
      have e1 : ∀ z : Euc d × Euc d, Ψ (z, t) = t ^ ((0 : ℝ) / 2 - 1) *
          (Real.exp (-(‖z.1 - z.2‖ ^ 2 * t)) * (f z.1 * f z.2) -
            Real.exp (-(1 * t)) * (f z.1 * f z.2)) := fun z => by
        simp only [hΨ, psd2_g]; ring
      simp_rw [e1]
      rw [integral_const_mul, integral_sub hE hC, integral_const_mul, hz0]
      ring
    rw [e]
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (psd2_gauss hfm hf ht)
  have hR2 : 0 ≤ ∫ t, ∫ z, Ψ (z, t) ∂μ2 ∂μt := by
    refine integral_nonneg_of_ae ?_
    rw [hμt, Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun t ht => hR t ht
  have := hswap
  rw [hL] at this
  linarith

/-- **PSD-2.**  The logarithmic (`s = 0`) energy is nonnegative on integrable mass-zero signed
densities with absolutely convergent pairing. -/
theorem log_energy_nonneg (hd : 1 ≤ d) {f : Euc d → ℝ} (hf : Integrable f)
    (hmass : ∫ x, f x = 0)
    (hI : Integrable (fun p : Euc d × Euc d => rieszKernel d 0 (p.1 - p.2) * (f p.1 * f p.2))
      (volume.prod volume)) :
    0 ≤ ∫ x, ∫ y, rieszKernel d 0 (x - y) * f x * f y := by
  have hI0 : Integrable (psd1_P d 0 f f) (volume.prod volume) := hI
  rw [psd1_iter hI0]
  set f' : Euc d → ℝ := hf.aestronglyMeasurable.mk f with hf'
  have hm : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hae : f =ᵐ[volume] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hP := psd1_P_ae (d := d) (s := 0) hae hae
  rw [integral_congr_ae hP]
  exact psd2_core hd hm (hf.congr hae) (by rw [← integral_congr_ae hae]; exact hmass)
    (hI0.congr hP)

end HRS.MS.Psd
