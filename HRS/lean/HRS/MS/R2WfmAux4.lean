import HRS.MS.R2WfmAux3
import HRS.MS.WrQuadAux2
import HRS.MS.WrRowAux2

/-!
# HRS.MS.R2WfmAux4 -- `round2_weighted_field_moments` (S9.7), part 4: kernel-level Fourier synthesis

Packet S97.  `s97_pe_integral`: `pairEnergy` commutes with a `ξ`-integral of kernels dominated by `β(ξ) E(x,y)`;
`s97_val_phi`, `s97_fderiv_phi`: the values and derivatives of `⟨x⟩^P ψ` as `ξ`-integrals of those of the weighted plane waves
`s97_pw ξ 0`, `s97_pw ξ (-π/2)` with weights `A_ψ`, `B_ψ`; the commutator kernels `s97_K` and their envelope `s97_E`.
-/

open MeasureTheory
open scoped FourierTransform ENNReal NNReal

noncomputable section
namespace HRS.MS.R2Wfm
open HRS.Whole HRS.MS.R2Poly HRS.MS.Wr

variable {d : ℕ}

/-- `pairEnergy` commutes with a `ξ`-integral of kernels. -/
theorem s97_pe_integral {N : ℕ} (X : EucConfig d N) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (g : Euc d → Euc d → Euc d → ℝ)
    (hg : Measurable (fun q : Euc d × Euc d × Euc d => g q.1 q.2.1 q.2.2))
    (β : Euc d → ℝ) (hβ : Integrable β) (hβ0 : ∀ ξ, 0 ≤ β ξ)
    (E : Euc d → Euc d → ℝ) (hE0 : ∀ x y, 0 ≤ E x y)
    (hEm : Measurable (fun p : Euc d × Euc d => E p.1 p.2))
    (hE1 : ∀ x, Integrable (E x) μ)
    (hE2 : Integrable (fun p : Euc d × Euc d => E p.1 p.2) (μ.prod μ))
    (hbd : ∀ ξ x y, |g ξ x y| ≤ β ξ * E x y) :
    pairEnergy (fun x y => ∫ ξ, g ξ x y) X μ = ∫ ξ, pairEnergy (g ξ) X μ := by
  have hgm3 : ∀ x y, Measurable (fun ξ => g ξ x y) := fun x y =>
    hg.comp (measurable_id.prodMk (measurable_const.prodMk measurable_const))
  have hint_pt : ∀ x y, Integrable (fun ξ => g ξ x y) := fun x y =>
    (hβ.mul_const (E x y)).mono' (hgm3 x y).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => by simpa using hbd ξ x y)
  -- section integrals
  have hsec_meas : ∀ x, Measurable (fun q : Euc d × Euc d => g q.1 x q.2) := fun x =>
    hg.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hsec_int : ∀ x, Integrable (fun q : Euc d × Euc d => g q.2 x q.1) (μ.prod volume) := by
    intro x
    refine ((hE1 x).mul_prod hβ).mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
    · exact (hg.comp (measurable_snd.prodMk (measurable_const.prodMk measurable_fst))).aestronglyMeasurable
    · simpa [mul_comm] using hbd q.2 x q.1
  have hswap1 : ∀ x, ∫ y, (∫ ξ, g ξ x y) ∂μ = ∫ ξ, (∫ y, g ξ x y ∂μ) := fun x =>
    integral_integral_swap (f := fun y ξ => g ξ x y) (hsec_int x)
  set H : Euc d → Euc d → ℝ := fun x ξ => ∫ y, g ξ x y ∂μ with hH
  set e : Euc d → ℝ := fun x => ∫ y, E x y ∂μ with he
  have he_int : Integrable e μ := hE2.integral_prod_left
  have hHm : Measurable (fun p : Euc d × Euc d => H p.1 p.2) := by
    have : StronglyMeasurable (fun p : Euc d × Euc d => ∫ y, g p.2 p.1 y ∂μ) := by
      refine StronglyMeasurable.integral_prod_right (f := fun (p : Euc d × Euc d) (y : Euc d) => g p.2 p.1 y) ?_
      exact (hg.comp (measurable_snd.comp measurable_fst |>.prodMk
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))).stronglyMeasurable
    exact this.measurable
  have hHbd : ∀ x ξ, |H x ξ| ≤ β ξ * e x := by
    intro x ξ
    have := norm_integral_le_of_norm_le (μ := μ) (f := fun y => g ξ x y)
      (g := fun y => β ξ * E x y) ((hE1 x).const_mul _) (Filter.Eventually.of_forall fun y => by
        simpa using hbd ξ x y)
    simpa [hH, he, integral_const_mul] using this
  have hH_int : Integrable (fun p : Euc d × Euc d => H p.1 p.2) (μ.prod volume) := by
    refine (he_int.mul_prod hβ).mono' hHm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    simpa [mul_comm] using hHbd p.1 p.2
  have hswap2 : ∫ x, (∫ ξ, H x ξ) ∂μ = ∫ ξ, (∫ x, H x ξ ∂μ) :=
    integral_integral_swap (f := fun x ξ => H x ξ) hH_int
  have hHξm : ∀ x, Measurable (fun ξ => H x ξ) := fun x => hHm.comp (measurable_const.prodMk measurable_id)
  have hT2 : ∀ x, Integrable (fun ξ => H x ξ) := fun x =>
    (hβ.mul_const (e x)).mono' (hHξm x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => by simpa using hHbd x ξ)
  have hT3 : Integrable (fun ξ => ∫ x, H x ξ ∂μ) := hH_int.integral_prod_right
  have i1 : Integrable (fun ξ => (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, g ξ (X i) (X j)) :=
    (integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint_pt (X i) (X j)).const_mul _
  have i2 : Integrable (fun ξ => (1 / (N : ℝ)) * ∑ i, H (X i) ξ) :=
    (integrable_finset_sum _ fun i _ => hT2 (X i)).const_mul _
  have i3 : Integrable (fun ξ => (1 / 2 : ℝ) * ∫ x, H x ξ ∂μ) := hT3.const_mul _
  unfold pairEnergy
  have r1 : ∀ x, ∫ y, (∫ ξ, g ξ x y) ∂μ = ∫ ξ, H x ξ := hswap1
  simp_rw [r1]
  rw [hswap2]
  have hR : ∀ ξ, (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, g ξ (X i) (X j) -
      (1 / (N : ℝ)) * ∑ i, ∫ y, g ξ (X i) y ∂μ + (1 / 2) * ∫ x, ∫ y, g ξ x y ∂μ ∂μ =
      ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, g ξ (X i) (X j) -
      (1 / (N : ℝ)) * ∑ i, H (X i) ξ) + (1 / 2 : ℝ) * ∫ x, H x ξ ∂μ := fun ξ => rfl
  simp_rw [hR]
  have e1 := integral_add (μ := (volume : Measure (Euc d))) (f := fun ξ => (1 / (2 * (N : ℝ) ^ 2)) *
    ∑ i, ∑ j ∈ Finset.univ.erase i, g ξ (X i) (X j) - (1 / (N : ℝ)) * ∑ i, H (X i) ξ)
    (g := fun ξ => (1 / 2 : ℝ) * ∫ x, H x ξ ∂μ) (i1.sub i2) i3
  have e2 := integral_sub (μ := (volume : Measure (Euc d))) i1 i2
  have e3 : ∫ ξ, (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, g ξ (X i) (X j) =
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, ∫ ξ, g ξ (X i) (X j) := by
    rw [integral_const_mul, integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => hint_pt (X i) (X j))]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ (fun j _ => hint_pt (X i) (X j))]
  have e4 : ∫ ξ, (1 / (N : ℝ)) * ∑ i, H (X i) ξ = (1 / (N : ℝ)) * ∑ i, ∫ ξ, H (X i) ξ := by
    rw [integral_const_mul, integral_finset_sum _ (fun i _ => hT2 (X i))]
  have e5 : ∫ ξ, (1 / 2 : ℝ) * ∫ x, H x ξ ∂μ = (1 / 2 : ℝ) * ∫ ξ, ∫ x, H x ξ ∂μ := integral_const_mul _ _
  rw [e1, e2, e3, e4, e5]


theorem s97_comm_eq (s : ℝ) (φ : Euc d → ℝ) (x y : Euc d) :
    commutatorKernel d s (fun z => gradient φ z) x y =
      fderiv ℝ φ x (rieszKernelGrad d s (x - y)) - fderiv ℝ φ y (rieszKernelGrad d s (x - y)) := by
  unfold commutatorKernel
  rw [inner_sub_left]
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply, InnerProductSpace.toDual_symm_apply]

theorem s97_fderiv_pw_apply (Pw : ℝ) (ξ : Euc d) (φ0 : ℝ) (x g : Euc d) :
    fderiv ℝ (s97_pw Pw ξ φ0) x g =
      Real.cos (2 * Real.pi * inner ℝ x ξ + φ0) * inner ℝ (s97_W1 Pw x) g -
        (2 * Real.pi * jbracket x ^ Pw * Real.sin (2 * Real.pi * inner ℝ x ξ + φ0)) * inner ℝ ξ g := by
  rw [(s97_hasFDerivAt_pw Pw ξ φ0 x).fderiv, innerSL_apply_apply, s97_gpw, inner_sub_left, inner_smul_left,
    inner_smul_left]
  simp

/-- Fourier synthesis of the weighted test function. -/
theorem s97_val_phi (ψ : SchwartzMap (Euc d) ℝ) (Pw : ℝ) (x : Euc d) :
    jbracket x ^ Pw * ψ x = ∫ ξ, (s97_A ψ ξ * s97_pw Pw ξ 0 x - s97_B ψ ξ * s97_pw Pw ξ (-(Real.pi / 2)) x) := by
  rw [s97_inv' ψ x, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [s97_pw, add_zero]
  rw [show 2 * Real.pi * inner ℝ x ξ + -(Real.pi / 2) = 2 * Real.pi * inner ℝ x ξ - Real.pi / 2 by ring,
    Real.cos_sub_pi_div_two]
  ring


theorem s97_int1 (ψ : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    Integrable (fun ξ => s97_A ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ) -
      s97_B ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ)) := by
  refine (s97_AB_int ψ).mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
  · have := s97_A_cont ψ; have := s97_B_cont ψ
    exact Continuous.aestronglyMeasurable (by fun_prop)
  · have h3 := Real.abs_cos_le_one (2 * Real.pi * inner ℝ x ξ)
    have h4 := Real.abs_sin_le_one (2 * Real.pi * inner ℝ x ξ)
    rw [Real.norm_eq_abs]
    calc _ ≤ |s97_A ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ)| + |s97_B ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ)| :=
          abs_sub _ _
      _ = |s97_A ψ ξ| * |Real.cos (2 * Real.pi * inner ℝ x ξ)| + |s97_B ψ ξ| * |Real.sin (2 * Real.pi * inner ℝ x ξ)| := by
          rw [abs_mul, abs_mul]
      _ ≤ |s97_A ψ ξ| + |s97_B ψ ξ| := by
          have := abs_nonneg (s97_A ψ ξ); have := abs_nonneg (s97_B ψ ξ)
          nlinarith
      _ ≤ (1 + ‖ξ‖) ^ 2 * (|s97_A ψ ξ| + |s97_B ψ ξ|) := by
          have : 1 ≤ (1 + ‖ξ‖) ^ 2 := by nlinarith [norm_nonneg ξ]
          have h0 : 0 ≤ |s97_A ψ ξ| + |s97_B ψ ξ| := by positivity
          nlinarith

theorem s97_int2 (ψ : SchwartzMap (Euc d) ℝ) (x g : Euc d) :
    Integrable (fun ξ => (2 * Real.pi * inner ℝ ξ g) * (s97_A ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ) +
      s97_B ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ))) := by
  refine ((s97_AB_int ψ).const_mul (2 * Real.pi * ‖g‖)).mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
  · have := s97_A_cont ψ; have := s97_B_cont ψ
    exact Continuous.aestronglyMeasurable (by fun_prop)
  · have h3 := Real.abs_cos_le_one (2 * Real.pi * inner ℝ x ξ)
    have h4 := Real.abs_sin_le_one (2 * Real.pi * inner ℝ x ξ)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    have h1 : |inner ℝ ξ g| ≤ ‖ξ‖ * ‖g‖ := abs_real_inner_le_norm _ _
    have h2 : |s97_A ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ) + s97_B ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ)| ≤
        |s97_A ψ ξ| + |s97_B ψ ξ| := by
      calc _ ≤ |s97_A ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ)| + |s97_B ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ)| :=
            abs_add_le _ _
        _ = |s97_A ψ ξ| * |Real.sin (2 * Real.pi * inner ℝ x ξ)| + |s97_B ψ ξ| * |Real.cos (2 * Real.pi * inner ℝ x ξ)| := by
            rw [abs_mul, abs_mul]
        _ ≤ |s97_A ψ ξ| + |s97_B ψ ξ| := by
            have := abs_nonneg (s97_A ψ ξ); have := abs_nonneg (s97_B ψ ξ)
            nlinarith
    have hn := norm_nonneg ξ
    have hg := norm_nonneg g
    have hAB : 0 ≤ |s97_A ψ ξ| + |s97_B ψ ξ| := by positivity
    have hq : ‖ξ‖ ≤ (1 + ‖ξ‖) ^ 2 := by nlinarith
    calc 2 * Real.pi * |inner ℝ ξ g| * |s97_A ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ) +
          s97_B ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ)|
        ≤ 2 * Real.pi * (‖ξ‖ * ‖g‖) * (|s97_A ψ ξ| + |s97_B ψ ξ|) := by
          gcongr
      _ ≤ 2 * Real.pi * ‖g‖ * ((1 + ‖ξ‖) ^ 2 * (|s97_A ψ ξ| + |s97_B ψ ξ|)) := by
          have : ‖ξ‖ * (|s97_A ψ ξ| + |s97_B ψ ξ|) ≤ (1 + ‖ξ‖) ^ 2 * (|s97_A ψ ξ| + |s97_B ψ ξ|) :=
            mul_le_mul_of_nonneg_right hq hAB
          nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi * ‖g‖) (sub_nonneg.2 this)]

theorem s97_hpt (ψ : SchwartzMap (Euc d) ℝ) (Pw : ℝ) (x g : Euc d) (ξ : Euc d) :
    s97_A ψ ξ * fderiv ℝ (s97_pw Pw ξ 0) x g -
      s97_B ψ ξ * fderiv ℝ (s97_pw Pw ξ (-(Real.pi / 2))) x g =
      inner ℝ (s97_W1 Pw x) g * (s97_A ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ) -
        s97_B ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ)) -
        jbracket x ^ Pw * ((2 * Real.pi * inner ℝ ξ g) * (s97_A ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ) +
          s97_B ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ))) := by
  rw [s97_fderiv_pw_apply, s97_fderiv_pw_apply]
  have e1 : 2 * Real.pi * inner ℝ x ξ + -(Real.pi / 2) = 2 * Real.pi * inner ℝ x ξ - Real.pi / 2 := by ring
  rw [add_zero, e1, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two]
  ring

theorem s97_phi_int (ψ : SchwartzMap (Euc d) ℝ) (Pw : ℝ) (x g : Euc d) :
    Integrable (fun ξ => s97_A ψ ξ * fderiv ℝ (s97_pw Pw ξ 0) x g -
      s97_B ψ ξ * fderiv ℝ (s97_pw Pw ξ (-(Real.pi / 2))) x g) := by
  simp_rw [s97_hpt]
  exact ((s97_int1 ψ x).const_mul _).sub ((s97_int2 ψ x g).const_mul _)

theorem s97_fderiv_phi (ψ : SchwartzMap (Euc d) ℝ) (Pw : ℝ) (x g : Euc d) :
    fderiv ℝ (fun z => jbracket z ^ Pw * ψ z) x g =
      ∫ ξ, (s97_A ψ ξ * fderiv ℝ (s97_pw Pw ξ 0) x g -
        s97_B ψ ξ * fderiv ℝ (s97_pw Pw ξ (-(Real.pi / 2))) x g) := by
  have hψ : HasFDerivAt (⇑ψ) (fderiv ℝ ψ x) x := (ψ.differentiableAt).hasFDerivAt
  have hmul := (s97_hasFDerivAt_w Pw x).mul hψ
  rw [show (fun z : Euc d => jbracket z ^ Pw * ψ z) = (fun z => jbracket z ^ Pw) * ⇑ψ from rfl, hmul.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply]
  set W : ℝ := inner ℝ (s97_W1 Pw x) g with hW
  have hW' : (Pw * (1 + ‖x‖ ^ 2) ^ (Pw / 2 - 1)) * inner ℝ x g = W := by
    rw [hW, s97_W1, inner_smul_left]; simp
  rw [s97_fderiv ψ x g]
  have hpt : ∀ ξ : Euc d, s97_A ψ ξ * fderiv ℝ (s97_pw Pw ξ 0) x g - s97_B ψ ξ * fderiv ℝ (s97_pw Pw ξ (-(Real.pi / 2))) x g = W * (s97_A ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ) - s97_B ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ)) - jbracket x ^ Pw * ((2 * Real.pi * inner ℝ ξ g) * (s97_A ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ) + s97_B ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ))) := fun ξ => s97_hpt ψ Pw x g ξ
  simp_rw [hpt]
  rw [integral_sub ((s97_int1 ψ x).const_mul W) ((s97_int2 ψ x g).const_mul _), integral_const_mul, integral_const_mul,
    ← s97_inv' ψ x]
  have : ∫ ξ, (-(2 * Real.pi * inner ℝ g ξ)) * (s97_A ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ) +
      s97_B ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ)) =
      -∫ ξ, (2 * Real.pi * inner ℝ ξ g) * (s97_A ψ ξ * Real.sin (2 * Real.pi * inner ℝ x ξ) +
      s97_B ψ ξ * Real.cos (2 * Real.pi * inner ℝ x ξ)) := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [real_inner_comm g ξ]; ring
  rw [this, hW']
  ring


/-- The commutator kernel of the weighted plane wave. -/
def s97_K (s Pw : ℝ) (ξ : Euc d) (φ0 : ℝ) : Euc d → Euc d → ℝ :=
  commutatorKernel d s (fun x => gradient (s97_pw Pw ξ φ0) x)

theorem s97_K_eq (s Pw : ℝ) (ξ : Euc d) (φ0 : ℝ) (x y : Euc d) :
    s97_K s Pw ξ φ0 x y = inner ℝ (s97_gpw Pw ξ φ0 x - s97_gpw Pw ξ φ0 y) (rieszKernelGrad d s (x - y)) := by
  unfold s97_K commutatorKernel
  simp only [s97_gradient_pw]

theorem s97_K_meas (s Pw φ0 : ℝ) :
    Measurable (fun q : Euc d × Euc d × Euc d => s97_K s Pw q.1 φ0 q.2.1 q.2.2) := by
  simp_rw [s97_K_eq]
  have h1 : Continuous (fun q : Euc d × Euc d × Euc d => s97_gpw Pw q.1 φ0 q.2.1) :=
    Continuous.comp (g := fun p : Euc d × Euc d => s97_gpw Pw p.1 φ0 p.2) (s97_gpw_cont2 Pw φ0)
      (f := fun q : Euc d × Euc d × Euc d => (q.1, q.2.1)) (by fun_prop)
  have h2 : Continuous (fun q : Euc d × Euc d × Euc d => s97_gpw Pw q.1 φ0 q.2.2) :=
    Continuous.comp (g := fun p : Euc d × Euc d => s97_gpw Pw p.1 φ0 p.2) (s97_gpw_cont2 Pw φ0)
      (f := fun q : Euc d × Euc d × Euc d => (q.1, q.2.2)) (by fun_prop)
  have h3 : Measurable (fun q : Euc d × Euc d × Euc d => rieszKernelGrad d s (q.2.1 - q.2.2)) :=
    (movtr_rieszKernelGrad_measurable (d := d) s).comp
      ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))
  have h4 : Measurable (fun q : Euc d × Euc d × Euc d => s97_gpw Pw q.1 φ0 q.2.1 - s97_gpw Pw q.1 φ0 q.2.2) :=
    h1.measurable.sub h2.measurable
  exact Measurable.inner h4 h3

/-- The envelope kernel `(⟨x⟩+⟨y⟩)^P (1 + W_s(x-y))`. -/
def s97_E (s Pw : ℝ) (x y : Euc d) : ℝ := (jbracket x + jbracket y) ^ Pw * (1 + rieszWeight s (x - y))

theorem s97_E_nonneg (s Pw : ℝ) (x y : Euc d) : 0 ≤ s97_E s Pw x y :=
  mul_nonneg (Real.rpow_nonneg (add_nonneg (s97_jb_nonneg x) (s97_jb_nonneg y)) _)
    (by have := wr3_rieszWeight_nonneg (d := d) s (x - y); linarith)

theorem s97_E_poly (s Pw : ℝ) : IsR2PolyPairKernel s Pw 1 (s97_E (d := d) s Pw) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold s97_E
    have h1 : Measurable (fun p : Euc d × Euc d => (jbracket p.1 + jbracket p.2) ^ Pw) :=
      ((s95_jb_meas.comp measurable_fst).add (s95_jb_meas.comp measurable_snd)).pow_const _
    have h2 : Measurable (fun p : Euc d × Euc d => 1 + rieszWeight s (p.1 - p.2)) :=
      measurable_const.add ((wr3_measurable_rieszWeight (d := d) s).comp (measurable_fst.sub measurable_snd))
    exact h1.mul h2
  · intro x y
    unfold s97_E
    rw [add_comm (jbracket x), show x - y = -(y - x) by abel, wr14a_W_symm]
  · intro x y _
    rw [abs_of_nonneg (s97_E_nonneg s Pw x y), one_mul]
    rfl

theorem s97_K_bound {s : ℝ} (hs0 : 0 ≤ s) {Pw : ℝ} (hP : 0 ≤ Pw) (ξ : Euc d) (φ0 : ℝ) (x y : Euc d) :
    |s97_K s Pw ξ φ0 x y| ≤ s97_Kc s Pw * (1 + ‖ξ‖) ^ 2 * s97_E s Pw x y := by
  by_cases hxy : x = y
  · subst hxy
    rw [s97_K_eq]; simp only [sub_self, inner_zero_left, abs_zero]
    exact mul_nonneg (mul_nonneg (s97_Kc_nonneg Pw hP) (by positivity)) (s97_E_nonneg s Pw _ _)
  · have := (s97_poly_kernel hs0 hP ξ φ0).bound x y hxy
    simpa [s97_K, s97_E, mul_assoc] using this

end HRS.MS.R2Wfm
end
