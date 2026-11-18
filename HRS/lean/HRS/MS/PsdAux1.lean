import HRS.Whole.Q34Aux13
import HRS.Whole.Q34Aux14

/-!
# PSD-1: positive-definite Riesz energy for `s > 0` on signed densities

Statements (namespace `HRS.MS.Psd`), all for the whole-space kernel `rieszKernel d s`:

* `riesz_energy_nonneg`: for `1 ≤ d`, `0 < s`, `f` integrable and with absolutely convergent
  double pairing `hI`, the iterated integral `∫ x, ∫ y, g(x-y) f x f y` is `≥ 0`.
* `energy_midpoint_le`: for integrable `ρ₁ ρ₂` with `g(|ρ₁|+|ρ₂|)(|ρ₁|+|ρ₂|)` absolutely
  integrable, `E((ρ₁+ρ₂)/2) ≤ (E ρ₁ + E ρ₂)/2` where `E ρ = ∫ x, ∫ y, g(x-y) ρ x ρ y`.

The absolute integrability hypotheses cannot be dropped: otherwise the Bochner integral is the
junk value `0` and the statements are vacuous.  Route: reduce to `HRS.Whole.Q34.riesz_posdef`
with `ν = |f| dx` and `u = sign f`, undoing the density with `integral_withDensity_eq_integral_toReal_smul`;
an integrable `f` is first replaced by a measurable a.e.-equal version.
Helper lemmas carry the prefix `psd1_`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.MS.Psd

open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

/-- the sign function `±1`, with `‖f x‖ * u x = f x`. -/
def psd1_sgn (f : Euc d → ℝ) (x : Euc d) : ℝ := if 0 ≤ f x then 1 else -1

theorem psd1_sgn_measurable {f : Euc d → ℝ} (hf : Measurable f) : Measurable (psd1_sgn f) := by
  unfold psd1_sgn
  exact Measurable.ite (measurableSet_le measurable_const hf) measurable_const measurable_const

theorem psd1_norm_mul_sgn (f : Euc d → ℝ) (x : Euc d) : ‖f x‖ * psd1_sgn f x = f x := by
  unfold psd1_sgn
  split_ifs with h
  · rw [Real.norm_eq_abs, abs_of_nonneg h]; ring
  · rw [Real.norm_eq_abs, abs_of_neg (not_le.1 h)]; ring

theorem psd1_sgn_abs (f : Euc d → ℝ) (x : Euc d) : ‖psd1_sgn f x‖ ≤ 1 := by
  unfold psd1_sgn
  split_ifs <;> simp

/-- Core case: `f` measurable. -/
theorem psd1_core (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) {f : Euc d → ℝ} (hfm : Measurable f)
    (hf : Integrable f)
    (hI : Integrable (fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2) * (f p.1 * f p.2))
      (volume.prod volume)) :
    0 ≤ ∫ p : Euc d × Euc d, rieszKernel d s (p.1 - p.2) * (f p.1 * f p.2)
      ∂(volume.prod volume) := by
  have hs0 : s ≠ 0 := hs.ne'
  set ρ : Euc d → ℝ := fun x => ‖f x‖ with hρ
  set ν : Measure (Euc d) := HRS.Whole.withDensityReal ρ with hν
  have hρm : Measurable ρ := hfm.norm
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hf.norm.hasFiniteIntegral
  have : NullSingletonClass ν := noAtoms_nu hd
  set u := psd1_sgn f with hu
  have hum : Measurable u := psd1_sgn_measurable hfm
  have huν : Integrable u ν :=
    Integrable.of_bound hum.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => psd1_sgn_abs f x)
  set w : Euc d → ℝ≥0∞ := fun x => ENNReal.ofReal (ρ x) with hw
  have hwm : Measurable w := ENNReal.measurable_ofReal.comp hρm
  have hprod : ν.prod ν = (volume.prod volume).withDensity (fun z : Euc d × Euc d => w z.1 * w z.2) := by
    simp only [hν, HRS.Whole.withDensityReal]
    exact prod_withDensity hwm hwm
  have hwm2 : Measurable (fun z : Euc d × Euc d => w z.1 * w z.2) :=
    (hwm.comp measurable_fst).mul (hwm.comp measurable_snd)
  have hlt : ∀ᵐ z ∂(volume.prod volume : Measure (Euc d × Euc d)), w z.1 * w z.2 < ∞ :=
    Filter.Eventually.of_forall fun z => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hpt : ∀ z : Euc d × Euc d,
      (w z.1 * w z.2).toReal • (‖z.1 - z.2‖ ^ (-s) * (u z.1 * u z.2)) =
        rieszKernel d s (z.1 - z.2) * (f z.1 * f z.2) := by
    intro z
    rw [rieszKernel_eq hs0, ENNReal.toReal_mul, hw]
    simp only [ENNReal.toReal_ofReal (norm_nonneg _), hρ, smul_eq_mul]
    have e : f z.1 * f z.2 = (‖f z.1‖ * psd1_sgn f z.1) * (‖f z.2‖ * psd1_sgn f z.2) := by
      rw [psd1_norm_mul_sgn f z.1, psd1_norm_mul_sgn f z.2]
    rw [e]
    simp only [hu]
    ring
  have hIν : Integrable (fun z : Euc d × Euc d => ‖z.1 - z.2‖ ^ (-s) * (u z.1 * u z.2)) (ν.prod ν) := by
    rw [hprod, integrable_withDensity_iff_integrable_smul' hwm2 hlt]
    refine hI.congr (Filter.Eventually.of_forall fun z => ?_)
    exact (hpt z).symm
  have key := riesz_posdef hs hum huν hIν
  rw [hprod, integral_withDensity_eq_integral_toReal_smul hwm2 hlt] at key
  simpa only [hpt] using key

/-- the pairing integrand `g(x-y) a(x) b(y)` on the product. -/
def psd1_P (d : ℕ) (s : ℝ) (a b : Euc d → ℝ) : Euc d × Euc d → ℝ :=
  fun p => rieszKernel d s (p.1 - p.2) * (a p.1 * b p.2)

theorem psd1_iter {s : ℝ} {a b : Euc d → ℝ}
    (h : Integrable (psd1_P d s a b) (volume.prod volume)) :
    ∫ x, ∫ y, rieszKernel d s (x - y) * a x * b y =
      ∫ p, psd1_P d s a b p ∂(volume.prod volume) := by
  rw [integral_prod _ h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [psd1_P]; ring

theorem psd1_P_ae {s : ℝ} {a a' b b' : Euc d → ℝ} (ha : a =ᵐ[volume] a') (hb : b =ᵐ[volume] b') :
    psd1_P d s a b =ᵐ[volume.prod volume] psd1_P d s a' b' := by
  have h1 : (fun p : Euc d × Euc d => a p.1) =ᵐ[volume.prod volume] fun p => a' p.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Euc d)))
      (ν := (volume : Measure (Euc d)))).ae_eq_comp ha
  have h2 : (fun p : Euc d × Euc d => b p.2) =ᵐ[volume.prod volume] fun p => b' p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Euc d)))
      (ν := (volume : Measure (Euc d)))).ae_eq_comp hb
  filter_upwards [h1, h2] with p hp1 hp2
  simp only [psd1_P, hp1, hp2]

/-- **PSD-1.**  The `s > 0` Riesz energy is nonnegative on integrable signed densities with
absolutely convergent pairing. -/
theorem riesz_energy_nonneg (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) {f : Euc d → ℝ}
    (hf : Integrable f)
    (hI : Integrable (fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2) * (f p.1 * f p.2))
      (volume.prod volume)) :
    0 ≤ ∫ x, ∫ y, rieszKernel d s (x - y) * f x * f y := by
  have hI0 : Integrable (psd1_P d s f f) (volume.prod volume) := hI
  rw [psd1_iter hI0]
  set f' : Euc d → ℝ := hf.aestronglyMeasurable.mk f with hf'
  have hm : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hae : f =ᵐ[volume] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hP := psd1_P_ae (s := s) hae hae
  rw [integral_congr_ae hP]
  exact psd1_core hd hs hm (hf.congr hae) (hI0.congr hP)

theorem psd1_K_nonneg {s : ℝ} (hs : 0 < s) (z : Euc d) : 0 ≤ rieszKernel d s z := by
  rw [rieszKernel_eq hs.ne']
  exact Real.rpow_nonneg (norm_nonneg _) _

theorem psd1_K_symm {s : ℝ} (hs : 0 < s) (z : Euc d) :
    rieszKernel d s (-z) = rieszKernel d s z := by
  rw [rieszKernel_eq hs.ne', rieszKernel_eq hs.ne', norm_neg]

theorem psd1_P_integrable {s : ℝ} (hs : 0 < s) {a b A : Euc d → ℝ} (ha : Integrable a)
    (hb : Integrable b) (haA : ∀ x, |a x| ≤ A x) (hbA : ∀ x, |b x| ≤ A x)
    (hI : Integrable (psd1_P d s A A) (volume.prod volume)) :
    Integrable (psd1_P d s a b) (volume.prod volume) := by
  refine Integrable.mono' hI ?_ (Filter.Eventually.of_forall fun p => ?_)
  · have hK : AEStronglyMeasurable (fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2))
        (volume.prod volume) :=
      ((measurable_rieszKernel hs.ne').comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
    have h1 : AEStronglyMeasurable (fun p : Euc d × Euc d => a p.1) (volume.prod volume) :=
      ha.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h2 : AEStronglyMeasurable (fun p : Euc d × Euc d => b p.2) (volume.prod volume) :=
      hb.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    exact hK.mul (h1.mul h2)
  · simp only [psd1_P, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (psd1_K_nonneg hs _)]
    have hA1 : 0 ≤ A p.1 := (abs_nonneg _).trans (haA _)
    exact mul_le_mul_of_nonneg_left (mul_le_mul (haA _) (hbA _) (abs_nonneg _) hA1)
      (psd1_K_nonneg hs _)

/-- **PSD-1 (midpoint convexity).**  The `s > 0` Riesz energy `E ρ = ∬ g(x-y) ρ(x) ρ(y)` satisfies
`E((ρ₁+ρ₂)/2) ≤ (E ρ₁ + E ρ₂)/2`, under absolute integrability of the pairing of `|ρ₁|+|ρ₂|`. -/
theorem energy_midpoint_le (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) {ρ₁ ρ₂ : Euc d → ℝ}
    (h1 : Integrable ρ₁) (h2 : Integrable ρ₂)
    (hI : Integrable (fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2) *
      ((|ρ₁ p.1| + |ρ₂ p.1|) * (|ρ₁ p.2| + |ρ₂ p.2|))) (volume.prod volume)) :
    ∫ x, ∫ y, rieszKernel d s (x - y) * ((ρ₁ x + ρ₂ x) / 2) * ((ρ₁ y + ρ₂ y) / 2) ≤
      ((∫ x, ∫ y, rieszKernel d s (x - y) * ρ₁ x * ρ₁ y) +
        (∫ x, ∫ y, rieszKernel d s (x - y) * ρ₂ x * ρ₂ y)) / 2 := by
  set A : Euc d → ℝ := fun x => |ρ₁ x| + |ρ₂ x| with hA
  have hIA : Integrable (psd1_P d s A A) (volume.prod volume) := hI
  have hb1 : ∀ x, |ρ₁ x| ≤ A x := fun x => by simp only [hA]; linarith [abs_nonneg (ρ₂ x)]
  have hb2 : ∀ x, |ρ₂ x| ≤ A x := fun x => by simp only [hA]; linarith [abs_nonneg (ρ₁ x)]
  have hbm : ∀ x, |(ρ₁ x + ρ₂ x) / 2| ≤ A x := fun x => by
    simp only [hA]
    rw [abs_div, abs_two]
    linarith [abs_add_le (ρ₁ x) (ρ₂ x), abs_nonneg (ρ₁ x), abs_nonneg (ρ₂ x)]
  have hbd : ∀ x, |ρ₁ x - ρ₂ x| ≤ A x := fun x => by
    simp only [hA]
    linarith [abs_sub (ρ₁ x) (ρ₂ x)]
  have hm : Integrable (fun x => (ρ₁ x + ρ₂ x) / 2) := (h1.add h2).div_const 2
  have hd' : Integrable (fun x => ρ₁ x - ρ₂ x) := h1.sub h2
  have I11 := psd1_P_integrable hs h1 h1 hb1 hb1 hIA
  have I12 := psd1_P_integrable hs h1 h2 hb1 hb2 hIA
  have I21 := psd1_P_integrable hs h2 h1 hb2 hb1 hIA
  have I22 := psd1_P_integrable hs h2 h2 hb2 hb2 hIA
  have Imm := psd1_P_integrable hs hm hm hbm hbm hIA
  have Idd := psd1_P_integrable hs hd' hd' hbd hbd hIA
  -- the iterated integrals as product integrals
  have e11 := psd1_iter I11
  have e22 := psd1_iter I22
  have emm := psd1_iter Imm
  have edd := psd1_iter Idd
  -- nonnegativity of the energy of the difference
  have hnn : 0 ≤ ∫ p, psd1_P d s (fun x => ρ₁ x - ρ₂ x) (fun x => ρ₁ x - ρ₂ x) p
      ∂(volume.prod volume) := by
    rw [← edd]
    have := riesz_energy_nonneg hd hs hd' Idd
    simpa [mul_assoc] using this
  -- symmetry
  have hsw : ∫ p, psd1_P d s ρ₂ ρ₁ p ∂(volume.prod volume) =
      ∫ p, psd1_P d s ρ₁ ρ₂ p ∂(volume.prod volume) := by
    rw [← integral_prod_swap (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
      (psd1_P d s ρ₁ ρ₂)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [psd1_P, Prod.fst_swap, Prod.snd_swap]
    rw [← psd1_K_symm hs (p.1 - p.2), neg_sub]
    ring
  have hlin1 : ∫ p, psd1_P d s (fun x => ρ₁ x - ρ₂ x) (fun x => ρ₁ x - ρ₂ x) p
        ∂(volume.prod volume) =
      (∫ p, psd1_P d s ρ₁ ρ₁ p ∂(volume.prod volume)) - (∫ p, psd1_P d s ρ₁ ρ₂ p ∂(volume.prod volume))
        - (∫ p, psd1_P d s ρ₂ ρ₁ p ∂(volume.prod volume))
        + (∫ p, psd1_P d s ρ₂ ρ₂ p ∂(volume.prod volume)) := by
    have J1 : Integrable (fun p => psd1_P d s ρ₁ ρ₁ p - psd1_P d s ρ₁ ρ₂ p) (volume.prod volume) :=
      I11.sub I12
    have J2 : Integrable (fun p => psd1_P d s ρ₁ ρ₁ p - psd1_P d s ρ₁ ρ₂ p - psd1_P d s ρ₂ ρ₁ p)
        (volume.prod volume) := J1.sub I21
    rw [integral_congr_ae (g := fun p => psd1_P d s ρ₁ ρ₁ p - psd1_P d s ρ₁ ρ₂ p
      - psd1_P d s ρ₂ ρ₁ p + psd1_P d s ρ₂ ρ₂ p)
      (Filter.Eventually.of_forall fun p => by simp only [psd1_P]; ring),
      integral_add J2 I22, integral_sub J1 I21, integral_sub I11 I12]
  have hlin2 : ∫ p, psd1_P d s (fun x => (ρ₁ x + ρ₂ x) / 2) (fun x => (ρ₁ x + ρ₂ x) / 2) p
        ∂(volume.prod volume) =
      ((∫ p, psd1_P d s ρ₁ ρ₁ p ∂(volume.prod volume)) + (∫ p, psd1_P d s ρ₁ ρ₂ p ∂(volume.prod volume))
        + (∫ p, psd1_P d s ρ₂ ρ₁ p ∂(volume.prod volume))
        + (∫ p, psd1_P d s ρ₂ ρ₂ p ∂(volume.prod volume))) / 4 := by
    have J1 : Integrable (fun p => psd1_P d s ρ₁ ρ₁ p + psd1_P d s ρ₁ ρ₂ p) (volume.prod volume) :=
      I11.add I12
    have J2 : Integrable (fun p => psd1_P d s ρ₁ ρ₁ p + psd1_P d s ρ₁ ρ₂ p + psd1_P d s ρ₂ ρ₁ p)
        (volume.prod volume) := J1.add I21
    have J3 : Integrable (fun p => psd1_P d s ρ₁ ρ₁ p + psd1_P d s ρ₁ ρ₂ p + psd1_P d s ρ₂ ρ₁ p
        + psd1_P d s ρ₂ ρ₂ p) (volume.prod volume) := J2.add I22
    rw [integral_congr_ae (g := fun p => (psd1_P d s ρ₁ ρ₁ p + psd1_P d s ρ₁ ρ₂ p
      + psd1_P d s ρ₂ ρ₁ p + psd1_P d s ρ₂ ρ₂ p) / 4)
      (Filter.Eventually.of_forall fun p => by simp only [psd1_P]; ring),
      integral_div, integral_add J2 I22, integral_add J1 I21, integral_add I11 I12]
  have e1 : ∫ x, ∫ y, rieszKernel d s (x - y) * ((ρ₁ x + ρ₂ x) / 2) * ((ρ₁ y + ρ₂ y) / 2) =
      ∫ p, psd1_P d s (fun x => (ρ₁ x + ρ₂ x) / 2) (fun x => (ρ₁ x + ρ₂ x) / 2) p
        ∂(volume.prod volume) := emm
  rw [e1, hlin2]
  rw [hlin1, hsw] at hnn
  rw [e11, e22]
  linarith

end HRS.MS.Psd
