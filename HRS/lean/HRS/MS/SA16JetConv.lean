import HRS.MS.SA16JetInterface
import HRS.Commutator.Whole.XLIAux23

/-!
# S.A.16: `L^p` gain for convolution with an odd kernel (Minkowski + Taylor)

`sa16j_mink`: a weighted Minkowski integral inequality (the proof pattern of `young_lintegral`).
`sa16j_odd_gain`: for an odd kernel `k` with `∫ |k| |z| < ∞` and `w ∈ C¹_b`,
`‖k ⋆ w‖_p ≤ (∫ |k||z|) ‖∇w‖_p`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

/-- weighted Minkowski inequality for `ℝ≥0∞`-valued functions -/
lemma sa16j_mink {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {p : ℝ} (hp : 1 ≤ p) {a : Y → ℝ≥0∞} (ha : Measurable a)
    {F : X → Y → ℝ≥0∞} (hF : Measurable (Function.uncurry F)) :
    ∫⁻ x, (∫⁻ y, a y * F x y ∂ν) ^ p ∂μ ≤
      (∫⁻ y, a y ∂ν) ^ (p - 1) * ∫⁻ y, a y * ∫⁻ x, F x y ^ p ∂μ ∂ν := by
  have hFx : ∀ x, Measurable (F x) := fun x => hF.comp (measurable_const.prodMk measurable_id)
  have hFy : ∀ y, Measurable (fun x => F x y) := fun y => hF.comp (measurable_id.prodMk measurable_const)
  rcases eq_or_lt_of_le hp with hp1 | hp1
  · subst hp1
    simp only [ENNReal.rpow_one, sub_self, ENNReal.rpow_zero, one_mul]
    have hm : Measurable (fun q : X × Y => a q.2 * F q.1 q.2) :=
      (ha.comp measurable_snd).mul hF
    rw [lintegral_lintegral_swap hm.aemeasurable]
    refine le_of_eq (lintegral_congr fun y => ?_)
    rw [lintegral_const_mul _ (hFy y)]
  have hp0 : 0 < p := by linarith
  set q : ℝ := p.conjExponent with hq
  have hconj : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hq0 : 0 < q := hconj.symm.pos
  have hpq : p / q = p - 1 := by
    have h := hconj.inv_add_inv_eq_one
    have hq' : q ≠ 0 := hq0.ne'
    field_simp at h
    field_simp
    linarith
  have hpt : ∀ x, (∫⁻ y, a y * F x y ∂ν) ^ p ≤
      (∫⁻ y, a y ∂ν) ^ (p - 1) * ∫⁻ y, a y * F x y ^ p ∂ν := by
    intro x
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hconj.symm
      (f := fun y => a y ^ (1 / q)) (g := fun y => a y ^ (1 / p) * F x y)
      (ha.pow_const _).aemeasurable ((ha.pow_const _).mul (hFx x)).aemeasurable
    have e1 : ∀ y, a y ^ (1 / q) * (a y ^ (1 / p) * F x y) = a y * F x y := by
      intro y
      rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
      have : 1 / q + 1 / p = 1 := by
        have := hconj.inv_add_inv_eq_one; simp only [one_div]; linarith
      rw [this, ENNReal.rpow_one]
    have e2 : ∀ y, (a y ^ (1 / q)) ^ q = a y := by
      intro y; rw [← ENNReal.rpow_mul]; field_simp; simp
    have e3 : ∀ y, (a y ^ (1 / p) * F x y) ^ p = a y * F x y ^ p := by
      intro y
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul]
      field_simp; simp
    simp only [Pi.mul_apply, e1, e2, e3] at h
    calc (∫⁻ y, a y * F x y ∂ν) ^ p
        ≤ ((∫⁻ y, a y ∂ν) ^ (1 / q) * (∫⁻ y, a y * F x y ^ p ∂ν) ^ (1 / p)) ^ p := by
          gcongr
      _ = (∫⁻ y, a y ∂ν) ^ (p - 1) * ∫⁻ y, a y * F x y ^ p ∂ν := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          have h1 : 1 / q * p = p - 1 := by rw [one_div, ← div_eq_inv_mul, hpq]
          have h2 : 1 / p * p = 1 := by field_simp
          rw [h1, h2, ENNReal.rpow_one]
  have hmeasB : Measurable (fun x => ∫⁻ y, a y * F x y ^ p ∂ν) := by
    refine Measurable.lintegral_prod_right'
      (f := fun q : X × Y => a q.2 * F q.1 q.2 ^ p) ?_
    exact (ha.comp measurable_snd).mul (hF.pow_const _)
  calc ∫⁻ x, (∫⁻ y, a y * F x y ∂ν) ^ p ∂μ
      ≤ ∫⁻ x, (∫⁻ y, a y ∂ν) ^ (p - 1) * ∫⁻ y, a y * F x y ^ p ∂ν ∂μ := lintegral_mono hpt
    _ = (∫⁻ y, a y ∂ν) ^ (p - 1) * ∫⁻ x, ∫⁻ y, a y * F x y ^ p ∂ν ∂μ :=
        lintegral_const_mul'' _ hmeasB.aemeasurable
    _ = (∫⁻ y, a y ∂ν) ^ (p - 1) * ∫⁻ y, a y * ∫⁻ x, F x y ^ p ∂μ ∂ν := by
        congr 1
        have hm : Measurable (fun q : X × Y => a q.2 * F q.1 q.2 ^ p) :=
          (ha.comp measurable_snd).mul (hF.pow_const _)
        rw [lintegral_lintegral_swap hm.aemeasurable]
        refine lintegral_congr fun y => ?_
        rw [lintegral_const_mul _ ((hFy y).pow_const _)]

section OddGain
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma sa16j_conv_aesm {k : Euc d → ℝ} (hk : Measurable k) {u : Euc d → F} (hu : Continuous u) :
    AEStronglyMeasurable (fun x => ∫ z, k z • u (x - z)) volume := by
  have hm : StronglyMeasurable (fun q : Euc d × Euc d => k q.2 • u (q.1 - q.2)) :=
    (hk.comp measurable_snd).stronglyMeasurable.smul
      ((hu.comp (continuous_fst.sub continuous_snd)).stronglyMeasurable)
  exact (hm.integral_prod_right' (ν := volume)).aestronglyMeasurable

/-- first-order Taylor in integral form -/
lemma sa16j_taylor {w : Euc d → F} (hw : ContDiff ℝ 1 w) (x z : Euc d) :
    ‖w (x - z) - w x‖ₑ ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ‖fderiv ℝ w (x - s • z)‖ₑ * ‖z‖ₑ := by
  have hd : Differentiable ℝ w := hw.differentiable one_ne_zero
  have hcd : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  have hder : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => w (x - s • z))
      (-(fderiv ℝ w (x - s • z) z)) s := by
    intro s _
    have h1 : HasDerivAt (fun s : ℝ => x - s • z) (-z) s := by
      simpa using ((hasDerivAt_id s).smul_const z).const_sub x
    have h2 := (hd (x - s • z)).hasFDerivAt.comp_hasDerivAt s h1
    rw [map_neg] at h2
    exact h2
  have hcont : Continuous (fun s : ℝ => -(fderiv ℝ w (x - s • z) z)) :=
    (((hcd.comp (continuous_const.sub (continuous_id.smul continuous_const))).clm_apply
      continuous_const)).neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hcont.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, sub_zero] at hftc
  rw [← hftc, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun s => ?_)
  have h := ContinuousLinearMap.le_opENorm (fderiv ℝ w (x - s • z)) z
  simpa using h

/-- the product measure (space times the unit time interval) -/
def sa16j_nu (d : ℕ) : Measure (Euc d × ℝ) :=
  (volume : Measure (Euc d)).prod (volume.restrict (Ioc (0 : ℝ) 1))

/-- the weight -/
def sa16j_aw (k : Euc d → ℝ) : Euc d × ℝ → ℝ≥0∞ := fun y => ‖k y.1‖ₑ * ‖y.1‖ₑ

/-- the transported gradient -/
def sa16j_Fw (w : Euc d → F) : Euc d → Euc d × ℝ → ℝ≥0∞ :=
  fun x y => ‖fderiv ℝ w (x - y.2 • y.1)‖ₑ

lemma sa16j_aw_meas {k : Euc d → ℝ} (hk : Measurable k) : Measurable (sa16j_aw k) :=
  (hk.comp measurable_fst).enorm.mul measurable_fst.enorm

lemma sa16j_Fw_meas {w : Euc d → F} (hcd : Continuous (fderiv ℝ w)) :
    Measurable (Function.uncurry (sa16j_Fw w)) :=
  (hcd.measurable.comp (measurable_fst.sub (measurable_snd.snd.smul measurable_snd.fst))).enorm

instance sa16j_nu_sfinite (d : ℕ) : SFinite (sa16j_nu d) := by
  unfold sa16j_nu; infer_instance

lemma sa16j_Fx_meas {w : Euc d → F} (hcd : Continuous (fderiv ℝ w)) (x : Euc d) :
    Measurable (sa16j_Fw w x) :=
  (hcd.measurable.comp (measurable_const.sub (measurable_snd.smul measurable_fst))).enorm

lemma sa16j_odd_pt {k : Euc d → ℝ} (hk : Measurable k) {w : Euc d → F} (hw : ContDiff ℝ 1 w)
    (x : Euc d) :
    ‖∫ z, k z • (w (x - z) - w x)‖ₑ ≤ ∫⁻ y, sa16j_aw k y * sa16j_Fw w x y ∂(sa16j_nu d) := by
  have hcd : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hm : Measurable (fun q : Euc d × ℝ => sa16j_aw k q * sa16j_Fw w x q) :=
    (sa16j_aw_meas hk).mul (sa16j_Fx_meas hcd x)
  rw [sa16j_nu, lintegral_prod _ hm.aemeasurable]
  refine lintegral_mono fun z => ?_
  rw [enorm_smul]
  calc ‖k z‖ₑ * ‖w (x - z) - w x‖ₑ ≤ ‖k z‖ₑ * ∫⁻ s in Ioc (0 : ℝ) 1, ‖fderiv ℝ w (x - s • z)‖ₑ * ‖z‖ₑ :=
        mul_le_mul' le_rfl (sa16j_taylor hw x z)
    _ = ∫⁻ s in Ioc (0 : ℝ) 1, ‖k z‖ₑ * (‖fderiv ℝ w (x - s • z)‖ₑ * ‖z‖ₑ) := by
        rw [lintegral_const_mul]
        exact (hcd.measurable.comp (measurable_const.sub (measurable_id.smul_const z))).enorm.mul_const _
    _ = ∫⁻ s in Ioc (0 : ℝ) 1, sa16j_aw k (z, s) * sa16j_Fw w x (z, s) := by
        refine lintegral_congr fun s => ?_
        simp only [sa16j_aw, sa16j_Fw]
        ring

lemma sa16j_nu_aw {k : Euc d → ℝ} (hk : Measurable k) :
    ∫⁻ y, sa16j_aw k y ∂(sa16j_nu d) = ∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ := by
  rw [sa16j_nu, lintegral_prod _ (sa16j_aw_meas hk).aemeasurable]
  simp [sa16j_aw]

lemma sa16j_Fw_lintegral {w : Euc d → F} {p : ℝ} (y : Euc d × ℝ) :
    ∫⁻ x, sa16j_Fw w x y ^ p = ∫⁻ x, ‖fderiv ℝ w x‖ₑ ^ p := by
  simp only [sa16j_Fw]
  exact lintegral_sub_right_eq_self (fun x => ‖fderiv ℝ w x‖ₑ ^ p) (y.2 • y.1)

/-- `L^p` gain of an odd kernel against a `C¹` function with `L^p` gradient -/
theorem sa16j_odd_gain {p : ℝ} (hp : 1 ≤ p) {k : Euc d → ℝ} (hk : Measurable k)
    (hk1 : Integrable k) (hkm : Integrable (fun z => |k z| * ‖z‖))
    (hodd : ∀ z, k (-z) = - k z) {w : Euc d → F} (hw : ContDiff ℝ 1 w) {B : ℝ}
    (hwb : ∀ x, ‖w x‖ ≤ B) :
    eLpNorm (fun x => ∫ z, k z • w (x - z)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (∫ z, |k z| * ‖z‖) *
        eLpNorm (fun x => ‖fderiv ℝ w x‖) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hpe0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hpetop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hwc : Continuous w := hw.continuous
  have hcd : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  have hk0 : ∫ z, k z = 0 := by
    have h := integral_neg_eq_self k (volume : Measure (Euc d))
    simp only [hodd, integral_neg] at h
    linarith
  have hint : ∀ x, Integrable (fun z => k z • w (x - z)) := by
    intro x
    refine Integrable.mono' (hk1.norm.mul_const B)
      (hk.aestronglyMeasurable.smul (hwc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hwb _) (norm_nonneg _)
  have hcx : ∀ x, (∫ z, k z • w (x - z)) = ∫ z, k z • (w (x - z) - w x) := by
    intro x
    have : ∀ z, k z • (w (x - z) - w x) = k z • w (x - z) - k z • w x := fun z => by
      rw [smul_sub]
    simp_rw [this]
    rw [integral_sub (hint x) (hk1.smul_const _), integral_smul_const, hk0, zero_smul, sub_zero]
  have hcm : AEStronglyMeasurable (fun x => ∫ z, k z • w (x - z)) volume :=
    sa16j_conv_aesm hk hwc
  have hgm : AEStronglyMeasurable (fun x => ‖fderiv ℝ w x‖) volume :=
    hcd.norm.aestronglyMeasurable
  have hMk' : ∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ = ENNReal.ofReal (∫ z, |k z| * ‖z‖) := by
    rw [ofReal_integral_eq_lintegral_ofReal hkm (Eventually.of_forall fun z => by positivity)]
    refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_mul (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm,
      ofReal_norm]
  have hnu := sa16j_nu_aw (d := d) hk
  have hmain : ∫⁻ x, ‖∫ z, k z • w (x - z)‖ₑ ^ p ≤
      (∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ) ^ p * ∫⁻ x, ‖fderiv ℝ w x‖ₑ ^ p := by
    calc ∫⁻ x, ‖∫ z, k z • w (x - z)‖ₑ ^ p
        ≤ ∫⁻ x, (∫⁻ y, sa16j_aw k y * sa16j_Fw w x y ∂(sa16j_nu d)) ^ p := by
          refine lintegral_mono fun x => ENNReal.rpow_le_rpow ?_ hp0.le
          rw [hcx x]
          exact sa16j_odd_pt hk hw x
      _ ≤ (∫⁻ y, sa16j_aw k y ∂(sa16j_nu d)) ^ (p - 1) *
            ∫⁻ y, sa16j_aw k y * ∫⁻ x, sa16j_Fw w x y ^ p ∂volume ∂(sa16j_nu d) :=
          sa16j_mink hp (sa16j_aw_meas hk) (sa16j_Fw_meas hcd)
      _ = (∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ) ^ (p - 1) *
            ((∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ) * ∫⁻ x, ‖fderiv ℝ w x‖ₑ ^ p) := by
          simp only [sa16j_Fw_lintegral]
          rw [hnu, lintegral_mul_const _ (sa16j_aw_meas hk), hnu]
      _ = (∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ) ^ p * ∫⁻ x, ‖fderiv ℝ w x‖ₑ ^ p := by
          rw [← mul_assoc]
          congr 1
          have := ENNReal.rpow_add_of_nonneg (x := ∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ) (p - 1) 1
            (by linarith) (by norm_num)
          rw [ENNReal.rpow_one, show p - 1 + 1 = p by ring] at this
          exact this.symm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpe0 hpetop hcm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hpe0 hpetop hgm, hpr, ← hMk']
  have hGp' : ∫⁻ x, ‖‖fderiv ℝ w x‖‖ₑ ^ p = ∫⁻ x, ‖fderiv ℝ w x‖ₑ ^ p := by
    simp only [enorm_norm]
  rw [hGp']
  calc (∫⁻ x, ‖∫ z, k z • w (x - z)‖ₑ ^ p) ^ (1 / p)
      ≤ ((∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ) ^ p * ∫⁻ x, ‖fderiv ℝ w x‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hmain (by positivity)
    _ = (∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ) * (∫⁻ x, ‖fderiv ℝ w x‖ₑ ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
        congr 2
        field_simp
        simp

end OddGain

end HRS.Whole.AppendixA.Phase2SA16
