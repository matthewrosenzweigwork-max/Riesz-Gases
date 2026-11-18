import HRS.Commutator.Whole.LocalAuxSAMP2
import Mathlib.Analysis.Convolution

/-!
# Cube-kernel bounds and the sampling estimate for a convolution (packet CMX-SAMP, helper file 3)
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

variable {d : ℕ}

lemma latV_sub (j ℓ : Fin d → ℤ) : latV (j - ℓ) = latV j - latV ℓ := by
  ext i; simp [latV]

lemma norm_latV_le {j ℓ : Fin d → ℤ} {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ cubeS d j)
    (hy : y ∈ cubeS d ℓ) : ‖latV (j - ℓ)‖ ≤ ‖x - y‖ + 2 * Real.sqrt d := by
  have h1 := norm_sub_latV_le hx
  have h2 := norm_sub_latV_le hy
  have e : latV (j - ℓ) = (x - y) - (x - latV j) + (y - latV ℓ) := by
    rw [latV_sub]; abel
  rw [e]
  calc ‖(x - y) - (x - latV j) + (y - latV ℓ)‖
      ≤ ‖(x - y) - (x - latV j)‖ + ‖y - latV ℓ‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ + ‖x - latV j‖ + ‖y - latV ℓ‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ _ := by linarith

lemma far_bound (hd : 1 ≤ d) {K : EuclideanSpace ℝ (Fin d) → ℝ} {C₂ : ℝ}
    (hK2 : ∀ x : EuclideanSpace ℝ (Fin d), 1 ≤ ‖x‖ → |K x| ≤ C₂ * ‖x‖ ^ (-((d : ℝ) + 1)))
    {x y : EuclideanSpace ℝ (Fin d)} {j ℓ : Fin d → ℤ} (hx : x ∈ cubeS d j) (hy : y ∈ cubeS d ℓ)
    (hn : 4 * Real.sqrt d ≤ ‖latV (j - ℓ)‖) :
    |K (x - y)| ≤ |C₂| * 4 ^ ((d : ℝ) + 1) * wtK d (j - ℓ) := by
  have hsd : 1 ≤ Real.sqrt d := by
    rw [Real.one_le_sqrt]; exact_mod_cast hd
  set n := ‖latV (j - ℓ)‖ with hndef
  have hn1 : 4 ≤ n := by linarith
  have hxy : n / 2 ≤ ‖x - y‖ := by
    have := norm_latV_le hx hy
    linarith
  have hxy1 : 1 ≤ ‖x - y‖ := by linarith
  have h1 := hK2 _ hxy1
  have hpos : 0 < n / 2 := by linarith
  have h2 : ‖x - y‖ ^ (-((d : ℝ) + 1)) ≤ (n / 2) ^ (-((d : ℝ) + 1)) :=
    Real.rpow_le_rpow_of_nonpos hpos hxy (by linarith)
  have h3 : (n / 2) ^ (-((d : ℝ) + 1)) = 2 ^ ((d : ℝ) + 1) * n ^ (-((d : ℝ) + 1)) := by
    rw [Real.div_rpow (by linarith) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_neg (by linarith : (0:ℝ) ≤ n)]
    field_simp
  have h4 : n ^ (-((d : ℝ) + 1)) ≤ 2 ^ ((d : ℝ) + 1) * (1 + n) ^ (-((d : ℝ) + 1)) := by
    have h5 : 1 + n ≤ 2 * n := by linarith
    have h6 : (1 + n) ^ ((d : ℝ) + 1) ≤ (2 * n) ^ ((d : ℝ) + 1) :=
      Real.rpow_le_rpow (by linarith) h5 (by positivity)
    rw [Real.mul_rpow (by norm_num) (by linarith)] at h6
    have h7 : 0 < (1 + n) ^ ((d : ℝ) + 1) := Real.rpow_pos_of_pos (by linarith) _
    have h8 : 0 < n ^ ((d : ℝ) + 1) := Real.rpow_pos_of_pos (by linarith) _
    rw [Real.rpow_neg (by linarith), Real.rpow_neg (by linarith),
      show (2 : ℝ) ^ ((d : ℝ) + 1) * ((1 + n) ^ ((d : ℝ) + 1))⁻¹ =
        2 ^ ((d : ℝ) + 1) / (1 + n) ^ ((d : ℝ) + 1) from (div_eq_mul_inv _ _).symm,
      inv_eq_one_div, div_le_div_iff₀ h8 h7]
    linarith
  have h9 : (4 : ℝ) ^ ((d : ℝ) + 1) = 2 ^ ((d : ℝ) + 1) * 2 ^ ((d : ℝ) + 1) := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have hwt : wtK d (j - ℓ) = (1 + n) ^ (-((d : ℝ) + 1)) := rfl
  calc |K (x - y)| ≤ C₂ * ‖x - y‖ ^ (-((d : ℝ) + 1)) := h1
    _ ≤ |C₂| * ‖x - y‖ ^ (-((d : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ |C₂| * (n / 2) ^ (-((d : ℝ) + 1)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = |C₂| * (2 ^ ((d : ℝ) + 1) * n ^ (-((d : ℝ) + 1))) := by rw [h3]
    _ ≤ |C₂| * (2 ^ ((d : ℝ) + 1) * (2 ^ ((d : ℝ) + 1) * (1 + n) ^ (-((d : ℝ) + 1)))) := by
        gcongr
    _ = |C₂| * 4 ^ ((d : ℝ) + 1) * wtK d (j - ℓ) := by rw [hwt, h9]; ring


lemma cube_kernel_bound (hd : 1 ≤ d) {α p : ℝ} (hp : 1 < p) (hα : (d : ℝ) < α * p)
    {K : EuclideanSpace ℝ (Fin d) → ℝ} (hKm : AEStronglyMeasurable K volume)
    {C₁ : ℝ} (hK1 : ∀ x : EuclideanSpace ℝ (Fin d), x ≠ 0 → ‖x‖ ≤ 1 →
      |K x| ≤ C₁ * ‖x‖ ^ (α - d))
    {C₂ : ℝ} (hK2 : ∀ x : EuclideanSpace ℝ (Fin d), 1 ≤ ‖x‖ →
      |K x| ≤ C₂ * ‖x‖ ^ (-((d : ℝ) + 1))) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ (x : EuclideanSpace ℝ (Fin d)) (j ℓ : Fin d → ℤ), x ∈ cubeS d j →
      (∫⁻ y in cubeS d ℓ, ‖K (x - y)‖ₑ ^ p.conjExponent) ^ (1 / p.conjExponent) ≤
        c * ENNReal.ofReal (wtK d (j - ℓ)) := by
  set q := p.conjExponent with hqdef
  have hq := Real.HolderConjugate.conjExponent hp
  have hq0 : 0 < q := by have := hq.symm.lt; linarith
  have hfin := kernel_Lq_lt_top hd hp hα hKm hK1 hK2
  set κ : ℝ≥0∞ := (∫⁻ z, ‖K z‖ₑ ^ q) ^ (1 / q) with hκ
  have hκtop : κ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hfin.ne
  set R : ℝ := 4 * Real.sqrt d with hR
  refine ⟨max (κ * ENNReal.ofReal ((1 + R) ^ ((d : ℝ) + 1)))
    (ENNReal.ofReal (|C₂| * 4 ^ ((d : ℝ) + 1))), ?_, fun x j ℓ hx => ?_⟩
  · exact (max_lt (ENNReal.mul_lt_top hκtop.lt_top ENNReal.ofReal_lt_top)
      ENNReal.ofReal_lt_top).ne
  by_cases hn : R ≤ ‖latV (j - ℓ)‖
  · -- far field
    set M : ℝ≥0∞ := ENNReal.ofReal (|C₂| * 4 ^ ((d : ℝ) + 1) * wtK d (j - ℓ)) with hM
    have h1 : ∀ y ∈ cubeS d ℓ, ‖K (x - y)‖ₑ ^ q ≤ M ^ q := by
      intro y hy
      refine ENNReal.rpow_le_rpow ?_ hq0.le
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (far_bound hd hK2 hx hy hn)
    have h2 : (∫⁻ y in cubeS d ℓ, ‖K (x - y)‖ₑ ^ q) ≤ M ^ q := by
      calc (∫⁻ y in cubeS d ℓ, ‖K (x - y)‖ₑ ^ q) ≤ ∫⁻ _y in cubeS d ℓ, M ^ q :=
            setLIntegral_mono' (measurableSet_cubeS ℓ) h1
        _ = M ^ q := by rw [setLIntegral_const, volume_cubeS, mul_one]
    calc (∫⁻ y in cubeS d ℓ, ‖K (x - y)‖ₑ ^ q) ^ (1 / q) ≤ (M ^ q) ^ (1 / q) :=
          ENNReal.rpow_le_rpow h2 (by positivity)
      _ = M := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
      _ = ENNReal.ofReal (|C₂| * 4 ^ ((d : ℝ) + 1)) * ENNReal.ofReal (wtK d (j - ℓ)) := by
          rw [hM, ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · -- near field
    push_neg at hn
    have h1 : (∫⁻ y in cubeS d ℓ, ‖K (x - y)‖ₑ ^ q) ≤ ∫⁻ z, ‖K z‖ₑ ^ q := by
      calc (∫⁻ y in cubeS d ℓ, ‖K (x - y)‖ₑ ^ q) ≤ ∫⁻ y, ‖K (x - y)‖ₑ ^ q :=
            setLIntegral_le_lintegral _ _
        _ = ∫⁻ z, ‖K z‖ₑ ^ q := lintegral_sub_left_eq_self (fun z => ‖K z‖ₑ ^ q) x
    have h2 : (∫⁻ y in cubeS d ℓ, ‖K (x - y)‖ₑ ^ q) ^ (1 / q) ≤ κ :=
      ENNReal.rpow_le_rpow h1 (by positivity)
    have h3 : (1 : ℝ) ≤ (1 + R) ^ ((d : ℝ) + 1) * wtK d (j - ℓ) := by
      have hn0 : 0 ≤ ‖latV (j - ℓ)‖ := norm_nonneg _
      unfold wtK
      rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    calc (∫⁻ y in cubeS d ℓ, ‖K (x - y)‖ₑ ^ q) ^ (1 / q) ≤ κ := h2
      _ = κ * 1 := (mul_one _).symm
      _ ≤ κ * ENNReal.ofReal ((1 + R) ^ ((d : ℝ) + 1) * wtK d (j - ℓ)) := by
          gcongr
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal h3
      _ = (κ * ENNReal.ofReal ((1 + R) ^ ((d : ℝ) + 1))) * ENNReal.ofReal (wtK d (j - ℓ)) := by
          rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
      _ ≤ _ := by gcongr; exact le_max_left _ _


/-- The abstract cube sampling estimate (`(3.cube-convolution)`, Hölder on cubes, Young for
sequences): if `u ≤ |K| * W` pointwise, then `(∑_j sup_{Q_j} u^p)^{1/p} ≲ ‖W‖_p`. -/
theorem cube_sampling_abstract (hd : 1 ≤ d) {α p : ℝ} (hp : 1 < p) (hα : (d : ℝ) < α * p)
    {K : EuclideanSpace ℝ (Fin d) → ℝ} (hKm : AEStronglyMeasurable K volume)
    {C₁ : ℝ} (hK1 : ∀ x : EuclideanSpace ℝ (Fin d), x ≠ 0 → ‖x‖ ≤ 1 →
      |K x| ≤ C₁ * ‖x‖ ^ (α - d))
    {C₂ : ℝ} (hK2 : ∀ x : EuclideanSpace ℝ (Fin d), 1 ≤ ‖x‖ →
      |K x| ≤ C₂ * ‖x‖ ^ (-((d : ℝ) + 1))) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ (W : EuclideanSpace ℝ (Fin d) → ℝ≥0∞), Measurable W →
      ∀ u : EuclideanSpace ℝ (Fin d) → ℝ≥0∞,
        (∀ x, u x ≤ ∫⁻ y, ‖K (x - y)‖ₑ * W y) →
        (∑' j : Fin d → ℤ, (⨆ x ∈ cubeS d j, u x) ^ p) ^ (1 / p) ≤
          c * (∫⁻ y, W y ^ p) ^ (1 / p) := by
  have hq := Real.HolderConjugate.conjExponent hp
  set q := p.conjExponent with hqdef
  have hp0 : 0 < p := by linarith
  obtain ⟨c₀, hc₀, hcube⟩ := cube_kernel_bound hd hp hα hKm hK1 hK2
  set β : (Fin d → ℤ) → ℝ≥0∞ := fun y => c₀ * ENNReal.ofReal (wtK d y) with hβ
  have hβsum : ∑' y, β y ≠ ⊤ := by
    rw [hβ]; simp only
    rw [ENNReal.tsum_mul_left]
    exact (ENNReal.mul_lt_top hc₀.lt_top tsum_wtK_lt_top).ne
  refine ⟨∑' y, β y, hβsum, fun W hW u hu => ?_⟩
  set b : (Fin d → ℤ) → ℝ≥0∞ := fun ℓ => (∫⁻ y in cubeS d ℓ, W y ^ p) ^ (1 / p) with hb
  -- Step e: pointwise bound on a cube
  have he : ∀ j : Fin d → ℤ, ∀ x ∈ cubeS d j, u x ≤ ∑' ℓ, β (j - ℓ) * b ℓ := by
    intro j x hx
    refine (hu x).trans ?_
    have hKx : AEMeasurable (fun y => ‖K (x - y)‖ₑ) volume :=
      (hKm.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)).enorm
    rw [← tsum_lintegral_cubeS]
    refine ENNReal.tsum_le_tsum fun ℓ => ?_
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (cubeS d ℓ)) hq.symm
      (f := fun y => ‖K (x - y)‖ₑ) (g := W) hKx.restrict hW.aemeasurable.restrict
    simp only [Pi.mul_apply] at h
    exact h.trans (mul_le_mul_left (hcube x j ℓ hx) _)
  have hsup : ∀ j : Fin d → ℤ, (⨆ x ∈ cubeS d j, u x) ≤ ∑' y, β y * b (j - y) := by
    intro j
    refine iSup₂_le fun x hx => (he j x hx).trans (le_of_eq ?_)
    have := Equiv.tsum_eq (Equiv.subLeft j) (fun y => β y * b (j - y))
    simp only [Equiv.subLeft_apply, sub_sub_cancel] at this
    exact this
  have hbp : ∑' ℓ, b ℓ ^ p = ∫⁻ y, W y ^ p := by
    rw [← tsum_lintegral_cubeS]
    refine tsum_congr fun ℓ => ?_
    rw [hb]; simp only
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  calc (∑' j : Fin d → ℤ, (⨆ x ∈ cubeS d j, u x) ^ p) ^ (1 / p)
      ≤ (∑' j : Fin d → ℤ, (∑' y, β y * b (j - y)) ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum fun j => ENNReal.rpow_le_rpow (hsup j) hp0.le)
          (by positivity)
    _ ≤ ((∑' y, β y) ^ p * ∑' ℓ, b ℓ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (young_tsum hp hβsum) (by positivity)
    _ = (∑' y, β y) * (∫⁻ y, W y ^ p) ^ (1 / p) := by
        rw [hbp, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne',
          ENNReal.rpow_one]


/-- The convolution `x ↦ ∫ k(y) f(x-y) dy` is a.e. strongly measurable. -/
lemma aesm_conv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {k : EuclideanSpace ℝ (Fin d) → ℝ} (hk : AEStronglyMeasurable k volume)
    {f : EuclideanSpace ℝ (Fin d) → E} (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun x => ∫ y, k y • f (x - y)) volume := by
  have h := AEStronglyMeasurable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hk hf
  exact h.integral_prod_right'

/-- Young's inequality with an `L¹` kernel: `‖k * f‖_p ≤ ‖k‖₁ ‖f‖_p` (`1 < p < ∞`). -/
lemma eLpNorm_conv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {k : EuclideanSpace ℝ (Fin d) → ℝ} (hk : Integrable k) {f : EuclideanSpace ℝ (Fin d) → E}
    (hf : AEStronglyMeasurable f volume) {p : ℝ} (hp : 1 < p) :
    eLpNorm (fun x => ∫ y, k y • f (x - y)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (∫ y, ‖k y‖) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hpne : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hconv := aesm_conv hk.1 hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hpt hconv,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hpt hf, hpr]
  set k' := hk.1.mk k with hk'
  set f' := hf.mk f with hf'
  have hkm : Measurable fun y => ‖k' y‖ₑ := hk.1.stronglyMeasurable_mk.enorm
  have hfm : Measurable fun y => ‖f' y‖ₑ := hf.stronglyMeasurable_mk.enorm
  have hkae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), k y = k' y := hk.1.ae_eq_mk
  have hfae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), f y = f' y := hf.ae_eq_mk
  have hA : ∫⁻ y, ‖k' y‖ₑ = ENNReal.ofReal (∫ y, ‖k y‖) := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hk]
    exact lintegral_congr_ae (by filter_upwards [hkae] with y hy; rw [hy])
  have hpt1 : ∀ x : EuclideanSpace ℝ (Fin d), ‖∫ y, k y • f (x - y)‖ₑ ≤
      ∫⁻ y, ‖k' y‖ₑ * ‖f' (x - y)‖ₑ := by
    intro x
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr_ae ?_
    have h2 : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), f (x - y) = f' (x - y) :=
      (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae_eq_comp hfae
    filter_upwards [hkae, h2] with y hy1 hy2
    rw [enorm_smul, hy1, hy2]
  have hA' : ∫⁻ y, ‖k' y‖ₑ ≠ ⊤ := by
    rw [hA]; exact ENNReal.ofReal_ne_top
  have hY := SAMP1.young_lintegral (volume : Measure (EuclideanSpace ℝ (Fin d))) hkm hfm hp hA'
  have hF : ∫⁻ x, ‖f' x‖ₑ ^ p = ∫⁻ x, ‖f x‖ₑ ^ p :=
    lintegral_congr_ae (by filter_upwards [hfae] with y hy; rw [hy])
  calc (∫⁻ x, ‖∫ y, k y • f (x - y)‖ₑ ^ p) ^ (1 / p)
      ≤ (∫⁻ x, (∫⁻ y, ‖k' y‖ₑ * ‖f' (x - y)‖ₑ) ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt1 x) hp0.le)
          (by positivity)
    _ ≤ ((∫⁻ y, ‖k' y‖ₑ) ^ p * ∫⁻ x, ‖f' x‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hY (by positivity)
    _ = ENNReal.ofReal (∫ y, ‖k y‖) * (∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p) := by
        rw [hF, hA, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

end HRS.Commutator.Whole.SAMP1
