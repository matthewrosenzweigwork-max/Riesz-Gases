import HRS.MS.SA16JetSchwartz

/-!
# S.A.16 SL1 support: `L^p` gain of an even kernel against a second difference

`sa16y_line2`: second difference on a line is bounded by the integral of the second derivative over `(-1,1)`.
`sa16y_taylor2`: the same along `x + r z`.
`sa16y_even_gain`: for an even kernel `k` with `∫ |k||z|² < ∞`,
`‖∫ k(z) (w(·) - w(· - z)) dz‖_p ≤ (∫ |k||z|²) ‖D²w‖_p`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

section Even
variable {d : ℕ}

/-- the second difference of a `C²` function of one variable -/
lemma sa16y_line2 {φ φ' φ'' : ℝ → ℝ} (h1 : ∀ s, HasDerivAt φ (φ' s) s)
    (h2 : ∀ s, HasDerivAt φ' (φ'' s) s) (hc : Continuous φ'') :
    ‖φ 1 + φ (-1) - 2 * φ 0‖ₑ ≤ ∫⁻ r in Ioc (-1 : ℝ) 1, ‖φ'' r‖ₑ := by
  have hc1 : Continuous φ' := continuous_iff_continuousAt.2 fun s => (h2 s).continuousAt
  have hA : ∫ s in (0 : ℝ)..1, φ' s = φ 1 - φ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => h1 s) (hc1.intervalIntegrable 0 1)
  have hB : ∫ s in (0 : ℝ)..1, -φ' (-s) = φ (-1) - φ 0 := by
    have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s => φ (-s)) (-φ' (-s)) s := by
      intro s _
      have := (h1 (-s)).comp s (hasDerivAt_neg s)
      simpa [Function.comp_def] using this
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((hc1.comp continuous_neg).neg.intervalIntegrable 0 1)
    simpa using this
  have hq : ∀ s : ℝ, φ' s - φ' (-s) = ∫ r in (-s)..s, φ'' r := by
    intro s
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => h2 r) (hc.intervalIntegrable _ _)]
  have hsum : φ 1 + φ (-1) - 2 * φ 0 = ∫ s in (0 : ℝ)..1, (φ' s - φ' (-s)) := by
    have hc2 : IntervalIntegrable (fun s => φ' (-s)) volume 0 1 :=
      (hc1.comp continuous_neg).intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub (hc1.intervalIntegrable 0 1) hc2]
    have : ∫ s in (0 : ℝ)..1, φ' (-s) = -(φ (-1) - φ 0) := by
      rw [← hB, ← intervalIntegral.integral_neg]
      simp
    rw [hA, this]; ring
  set L : ℝ≥0∞ := ∫⁻ r in Ioc (-1 : ℝ) 1, ‖φ'' r‖ₑ with hL
  have hqb : ∀ s ∈ Ioc (0 : ℝ) 1, ‖φ' s - φ' (-s)‖ₑ ≤ L := by
    intro s hs
    rw [hq s, intervalIntegral.integral_of_le (by linarith [hs.1])]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine lintegral_mono_set (Ioc_subset_Ioc ?_ hs.2)
    linarith [hs.2]
  rw [hsum, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ s in Ioc (0 : ℝ) 1, ‖φ' s - φ' (-s)‖ₑ ≤ ∫⁻ s in Ioc (0 : ℝ) 1, L :=
        setLIntegral_mono' measurableSet_Ioc hqb
    _ = L := by simp

/-- second-order Taylor along a line, in integral form -/
lemma sa16y_taylor2 {w : Euc d → ℝ} (hw : ContDiff ℝ 2 w) (x z : Euc d) :
    ‖w (x + z) + w (x - z) - 2 * w x‖ₑ ≤
      ∫⁻ r in Ioc (-1 : ℝ) 1, ‖iteratedFDeriv ℝ 2 w (x + r • z)‖ₑ * ‖z‖ₑ ^ 2 := by
  have hd : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hf1 : ContDiff ℝ 1 (fderiv ℝ w) := hw.fderiv_right (m := 1) (by norm_num)
  have hdf : Differentiable ℝ (fderiv ℝ w) := hf1.differentiable one_ne_zero
  have hcf : Continuous (fderiv ℝ (fderiv ℝ w)) := hf1.continuous_fderiv one_ne_zero
  have hl : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • z) z s := by
    intro s
    simpa using ((hasDerivAt_id s).smul_const z).const_add x
  have h1 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => w (x + s • z)) (fderiv ℝ w (x + s • z) z) s :=
    fun s => (hd (x + s • z)).hasFDerivAt.comp_hasDerivAt s (hl s)
  have h2 : ∀ s : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ w (x + s • z) z)
      (fderiv ℝ (fderiv ℝ w) (x + s • z) z z) s := by
    intro s
    have hh : HasDerivAt (fun s : ℝ => fderiv ℝ w (x + s • z))
        (fderiv ℝ (fderiv ℝ w) (x + s • z) z) s :=
      (hdf (x + s • z)).hasFDerivAt.comp_hasDerivAt s (hl s)
    have hev := (ContinuousLinearMap.apply ℝ ℝ z).hasFDerivAt.comp_hasDerivAt s hh
    exact hev
  have hc : Continuous (fun s : ℝ => fderiv ℝ (fderiv ℝ w) (x + s • z) z z) :=
    ((hcf.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const).clm_apply continuous_const
  have key := sa16y_line2 h1 h2 hc
  have e1 : (fun s : ℝ => w (x + s • z)) 1 = w (x + z) := by simp
  have e2 : (fun s : ℝ => w (x + s • z)) (-1) = w (x - z) := by simp [sub_eq_add_neg]
  have e3 : (fun s : ℝ => w (x + s • z)) 0 = w x := by simp
  simp only [e1, e2, e3] at key
  refine key.trans (lintegral_mono fun r => ?_)
  have hb := (iteratedFDeriv ℝ 2 w (x + r • z)).le_opNorm ![z, z]
  rw [iteratedFDeriv_two_apply, Fin.prod_univ_two] at hb
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hb
  show ‖fderiv ℝ (fderiv ℝ w) (x + r • z) z z‖ₑ ≤ _
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow
    (norm_nonneg _), ← ENNReal.ofReal_mul (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [hb, norm_nonneg z]

/-- the product measure (space times the interval `(-1,1]`) -/
def sa16y_nu (d : ℕ) : Measure (Euc d × ℝ) :=
  (volume : Measure (Euc d)).prod (volume.restrict (Ioc (-1 : ℝ) 1))

/-- the weight `|k(z)| |z|²` -/
def sa16y_aw (k : Euc d → ℝ) : Euc d × ℝ → ℝ≥0∞ := fun y => ‖k y.1‖ₑ * ‖y.1‖ₑ ^ 2

/-- the transported second derivative -/
def sa16y_Fw (w : Euc d → ℝ) : Euc d → Euc d × ℝ → ℝ≥0∞ :=
  fun x y => ‖iteratedFDeriv ℝ 2 w (x + y.2 • y.1)‖ₑ

instance sa16y_nu_sfinite (d : ℕ) : SFinite (sa16y_nu d) := by
  unfold sa16y_nu; infer_instance

lemma sa16y_aw_meas {k : Euc d → ℝ} (hk : Measurable k) : Measurable (sa16y_aw k) :=
  (hk.comp measurable_fst).enorm.mul (measurable_fst.enorm.pow_const _)

lemma sa16y_Fw_meas {w : Euc d → ℝ} (hc : Continuous (iteratedFDeriv ℝ 2 w)) :
    Measurable (Function.uncurry (sa16y_Fw w)) :=
  (hc.enorm.measurable.comp (measurable_fst.add (measurable_snd.snd.smul measurable_snd.fst)))

lemma sa16y_Fx_meas {w : Euc d → ℝ} (hc : Continuous (iteratedFDeriv ℝ 2 w)) (x : Euc d) :
    Measurable (sa16y_Fw w x) :=
  (hc.enorm.measurable.comp (measurable_const.add (measurable_snd.smul measurable_fst)))

lemma sa16y_Fw_lintegral {w : Euc d → ℝ} {p : ℝ} (y : Euc d × ℝ) :
    ∫⁻ x, sa16y_Fw w x y ^ p = ∫⁻ x, ‖iteratedFDeriv ℝ 2 w x‖ₑ ^ p := by
  simp only [sa16y_Fw]
  exact lintegral_add_right_eq_self (fun x => ‖iteratedFDeriv ℝ 2 w x‖ₑ ^ p) (y.2 • y.1)

lemma sa16y_nu_aw {k : Euc d → ℝ} (hk : Measurable k) :
    ∫⁻ y, sa16y_aw k y ∂(sa16y_nu d) = 2 * ∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ ^ 2 := by
  rw [sa16y_nu, lintegral_prod _ (sa16y_aw_meas hk).aemeasurable]
  simp only [sa16y_aw, setLIntegral_const, Real.volume_Ioc]
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_congr fun z => ?_
  norm_num
  ring

/-- the symmetrised integral is bounded pointwise -/
lemma sa16y_even_pt {k : Euc d → ℝ} (hk : Measurable k) {w : Euc d → ℝ} (hw : ContDiff ℝ 2 w)
    (x : Euc d) :
    ‖∫ z, k z * (w (x + z) + w (x - z) - 2 * w x)‖ₑ ≤
      ∫⁻ y, sa16y_aw k y * sa16y_Fw w x y ∂(sa16y_nu d) := by
  have hc : Continuous (iteratedFDeriv ℝ 2 w) := hw.continuous_iteratedFDeriv (by norm_num)
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hm : Measurable (fun q : Euc d × ℝ => sa16y_aw k q * sa16y_Fw w x q) :=
    (sa16y_aw_meas hk).mul (sa16y_Fx_meas hc x)
  rw [sa16y_nu, lintegral_prod _ hm.aemeasurable]
  refine lintegral_mono fun z => ?_
  rw [enorm_mul]
  calc ‖k z‖ₑ * ‖w (x + z) + w (x - z) - 2 * w x‖ₑ
      ≤ ‖k z‖ₑ * ∫⁻ r in Ioc (-1 : ℝ) 1, ‖iteratedFDeriv ℝ 2 w (x + r • z)‖ₑ * ‖z‖ₑ ^ 2 :=
        mul_le_mul' le_rfl (sa16y_taylor2 hw x z)
    _ = ∫⁻ r in Ioc (-1 : ℝ) 1, ‖k z‖ₑ * (‖iteratedFDeriv ℝ 2 w (x + r • z)‖ₑ * ‖z‖ₑ ^ 2) := by
        rw [lintegral_const_mul]
        exact (hc.enorm.measurable.comp (measurable_const.add (measurable_id.smul_const z))).mul_const _
    _ = ∫⁻ r in Ioc (-1 : ℝ) 1, sa16y_aw k (z, r) * sa16y_Fw w x (z, r) := by
        refine lintegral_congr fun r => ?_
        simp only [sa16y_aw, sa16y_Fw]
        ring

/-- `L^p` gain of an even kernel against a `C²` function with `L^p` second derivative -/
theorem sa16y_even_gain {p : ℝ} (hp : 1 ≤ p) {k : Euc d → ℝ} (hk : Measurable k)
    (hk1 : Integrable k) (hkm : Integrable (fun z => |k z| * ‖z‖ ^ 2))
    (heven : ∀ z, k (-z) = k z) {w : Euc d → ℝ} (hw : ContDiff ℝ 2 w) {B : ℝ}
    (hwb : ∀ x, |w x| ≤ B) :
    eLpNorm (fun x => ∫ z, k z * (w x - w (x - z))) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (2 * ∫ z, |k z| * ‖z‖ ^ 2) *
        eLpNorm (fun x => ‖iteratedFDeriv ℝ 2 w x‖) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hpe0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hpetop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hwc : Continuous w := hw.continuous
  have hc : Continuous (iteratedFDeriv ℝ 2 w) := hw.continuous_iteratedFDeriv (by norm_num)
  -- integrability of the three pieces
  have hint : ∀ x, Integrable (fun z => k z * w (x - z)) := by
    intro x
    refine Integrable.mono' (hk1.norm.mul_const B)
      (hk.aestronglyMeasurable.mul (hwc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hwb _) (norm_nonneg _)
  have hint' : ∀ x, Integrable (fun z => k z * w (x + z)) := by
    intro x
    refine Integrable.mono' (hk1.norm.mul_const B)
      (hk.aestronglyMeasurable.mul (hwc.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hwb _) (norm_nonneg _)
  have hEeq : ∀ x, (∫ z, k z * (w x - w (x - z))) = (∫ z, k z) * w x - ∫ z, k z * w (x - z) := by
    intro x
    have : ∀ z, k z * (w x - w (x - z)) = k z * w x - k z * w (x - z) := fun z => by ring
    simp_rw [this]
    rw [integral_sub (hk1.mul_const _) (hint x), integral_mul_const]
  have hsym : ∀ x, ∫ z, k z * w (x + z) = ∫ z, k z * w (x - z) := by
    intro x
    have h := integral_neg_eq_self (fun z => k z * w (x + z)) (volume : Measure (Euc d))
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [heven, sub_eq_add_neg]
  have hIeq : ∀ x, (∫ z, k z * (w (x + z) + w (x - z) - 2 * w x)) =
      -2 * ∫ z, k z * (w x - w (x - z)) := by
    intro x
    have : ∀ z, k z * (w (x + z) + w (x - z) - 2 * w x) =
        k z * w (x + z) + k z * w (x - z) - k z * (2 * w x) := fun z => by ring
    simp_rw [this]
    rw [integral_sub (f := fun z => k z * w (x + z) + k z * w (x - z)) (g := fun z => k z * (2 * w x))
      ((hint' x).add (hint x)) (hk1.mul_const _), integral_add (hint' x) (hint x),
      integral_mul_const, hsym x, hEeq x]
    ring
  have hpt : ∀ x, ‖∫ z, k z * (w x - w (x - z))‖ₑ ≤
      ∫⁻ y, sa16y_aw k y * sa16y_Fw w x y ∂(sa16y_nu d) := by
    intro x
    refine le_trans ?_ (sa16y_even_pt hk hw x)
    rw [enorm_le_iff_norm_le, hIeq x, norm_mul]
    have : ‖(-2 : ℝ)‖ = 2 := by simp
    rw [this]
    nlinarith [norm_nonneg (∫ z, k z * (w x - w (x - z)))]
  have hcm : AEStronglyMeasurable (fun x => ∫ z, k z * (w x - w (x - z))) volume := by
    have h1 : (fun x => ∫ z, k z * (w x - w (x - z))) =
        fun x => (∫ z, k z) * w x - ∫ z, k z • w (x - z) := by
      funext x; rw [hEeq x]; simp [smul_eq_mul]
    rw [h1]
    exact (hwc.aestronglyMeasurable.const_mul _).sub (sa16j_conv_aesm hk hwc)
  have hgm : AEStronglyMeasurable (fun x => ‖iteratedFDeriv ℝ 2 w x‖) volume :=
    hc.norm.aestronglyMeasurable
  have hMk' : ∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ ^ 2 = ENNReal.ofReal (∫ z, |k z| * ‖z‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hkm (Eventually.of_forall fun z => by positivity)]
    refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_mul (abs_nonneg _), ← Real.norm_eq_abs, ofReal_norm, ENNReal.ofReal_pow
      (norm_nonneg _), ofReal_norm]
  have hnu := sa16y_nu_aw (d := d) hk
  have hmain : ∫⁻ x, ‖∫ z, k z * (w x - w (x - z))‖ₑ ^ p ≤
      (2 * ∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ ^ 2) ^ p * ∫⁻ x, ‖iteratedFDeriv ℝ 2 w x‖ₑ ^ p := by
    calc ∫⁻ x, ‖∫ z, k z * (w x - w (x - z))‖ₑ ^ p
        ≤ ∫⁻ x, (∫⁻ y, sa16y_aw k y * sa16y_Fw w x y ∂(sa16y_nu d)) ^ p :=
          lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) hp0.le
      _ ≤ (∫⁻ y, sa16y_aw k y ∂(sa16y_nu d)) ^ (p - 1) *
            ∫⁻ y, sa16y_aw k y * ∫⁻ x, sa16y_Fw w x y ^ p ∂volume ∂(sa16y_nu d) :=
          sa16j_mink hp (sa16y_aw_meas hk) (sa16y_Fw_meas hc)
      _ = (2 * ∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ ^ 2) ^ (p - 1) *
            ((2 * ∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ ^ 2) * ∫⁻ x, ‖iteratedFDeriv ℝ 2 w x‖ₑ ^ p) := by
          simp only [sa16y_Fw_lintegral]
          rw [hnu, lintegral_mul_const _ (sa16y_aw_meas hk), hnu]
      _ = (2 * ∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ ^ 2) ^ p * ∫⁻ x, ‖iteratedFDeriv ℝ 2 w x‖ₑ ^ p := by
          rw [← mul_assoc]
          congr 1
          have := ENNReal.rpow_add_of_nonneg (x := 2 * ∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ ^ 2) (p - 1) 1
            (by linarith) (by norm_num)
          rw [ENNReal.rpow_one, show p - 1 + 1 = p by ring] at this
          exact this.symm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpe0 hpetop hcm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hpe0 hpetop hgm, hpr]
  have hGp' : ∫⁻ x, ‖‖iteratedFDeriv ℝ 2 w x‖‖ₑ ^ p = ∫⁻ x, ‖iteratedFDeriv ℝ 2 w x‖ₑ ^ p := by
    simp only [enorm_norm]
  rw [hGp']
  have hc2 : ENNReal.ofReal (2 * ∫ z, |k z| * ‖z‖ ^ 2) = 2 * ∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ ^ 2 := by
    rw [ENNReal.ofReal_mul (by norm_num), hMk', ENNReal.ofReal_ofNat]
  rw [hc2]
  calc (∫⁻ x, ‖∫ z, k z * (w x - w (x - z))‖ₑ ^ p) ^ (1 / p)
      ≤ ((2 * ∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ ^ 2) ^ p * ∫⁻ x, ‖iteratedFDeriv ℝ 2 w x‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hmain (by positivity)
    _ = (2 * ∫⁻ z, ‖k z‖ₑ * ‖z‖ₑ ^ 2) * (∫⁻ x, ‖iteratedFDeriv ℝ 2 w x‖ₑ ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
        congr 2
        field_simp
        simp

end Even

end HRS.Whole.AppendixA.Phase2SA16
