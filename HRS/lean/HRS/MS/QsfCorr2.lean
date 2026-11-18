import HRS.MS.QsfCorr1
import HRS.MS.QsfStat1
import HRS.MD.DOMCalc

/-!
# S4.5 packet B1, part 2: thermal data and the pointwise corrector identity

`s45_corr_identity`: for the thermal reference `μ = ρ dx`, `U = g * μ` and a `C²` function `χ` with bounded `∇χ`,
`D²χ` (the S4.4 correctors have this form),
`∫ ⟨∇χ(x) - ∇χ(y), ∇g(x-y)⟩ dμ(y) = ⟨∇χ(x), ∇U(x)⟩ + ∫ g(x-y) (Lχ)(y) dμ(y)`
for every `x`, `L = thermalGen`.  This is the "symmetrised integration by parts" of the TeX proof (S lines 2569-2580),
valid also when the unsymmetrised force `∇g` is not locally integrable (`d-1 ≤ s < d`): it uses the difference of
gradients before integrating by parts (`s45_obi`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- The thermal data used throughout. -/
structure ThermalData (d : ℕ) (s a β C c BU : ℝ) : Prop where
  prob : IsProbDensity (thermalDensity d s a β)
  smooth : ContDiff ℝ ∞ (thermalDensity d s a β)
  pos : ∀ y : Euc d, 0 < thermalDensity d s a β y
  C0 : 0 ≤ C
  hc : 0 < c
  h0 : ∀ y : Euc d, |thermalDensity d s a β y| ≤ C * Real.exp (-c * ‖y‖ ^ 2)
  h1 : ∀ y : Euc d, ‖fderiv ℝ (thermalDensity d s a β) y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)
  Usmooth : ContDiff ℝ ∞ (convMeasure (rieszKernel d s) (thermalMeasure d s a β))
  BU0 : 0 ≤ BU
  gradU_le : ∀ y : Euc d, ‖gradient (convMeasure (rieszKernel d s) (thermalMeasure d s a β)) y‖ ≤ BU
  grad_rho : ∀ y : Euc d, gradient (thermalDensity d s a β) y = thermalDensity d s a β y •
    (-(a * β) • y + (-β) • gradient (convMeasure (rieszKernel d s) (thermalMeasure d s a β)) y)

theorem s45_thermal_data (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) : ∃ C c BU : ℝ, ThermalData d s a β C c BU := by
  obtain ⟨c₀, M₀, m₂, hc₀, hM₀, hU, hMb⟩ := HRS.MS.Tc6.tc6_unif hd hs0 hsd (am := a) (ap := a)
    (βm := β) (βp := β) ha hβ le_rfl le_rfl
  obtain ⟨S, hS0, hS⟩ := hU 1
  obtain ⟨Mb, hMb0, hMbρ⟩ := hMb 0
  have href := hS a β le_rfl le_rfl le_rfl le_rfl
  have hdr := hMbρ a β le_rfl le_rfl le_rfl le_rfl
  obtain ⟨Cp, hCp0, hCp⟩ := s45_poly_le (half_pos hc₀)
  obtain ⟨hcb, -⟩ := HRS.MS.Tc1.tc1_drift_data hd hs0 hsd ha hβ hdr
  refine ⟨max M₀ (S * Cp), c₀ / 2, Mb / β, ⟨href.prob, href.smooth, href.pos, le_max_of_le_left hM₀.le,
    half_pos hc₀, fun y => ?_, fun y => ?_, HRS.MS.Tc1.tc1_U_smooth hd hs0 hsd ha hβ, by positivity,
    fun y => ?_, HRS.MS.Tc1.tc1_grad_rho hd hs0 hsd ha hβ⟩⟩
  · rw [abs_of_nonneg (href.prob.nonneg y)]
    refine (href.gauss y).trans ?_
    have : Real.exp (-c₀ * ‖y‖ ^ 2) ≤ Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) :=
      Real.exp_le_exp.2 (by nlinarith [sq_nonneg ‖y‖])
    calc M₀ * Real.exp (-c₀ * ‖y‖ ^ 2) ≤ M₀ * Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left this hM₀.le
      _ ≤ max M₀ (S * Cp) * Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · have h := href.deriv 1 le_rfl y
    rw [norm_iteratedFDeriv_one] at h
    have hp := hCp ‖y‖ (norm_nonneg _)
    have e : Real.exp (c₀ / 2 * ‖y‖ ^ 2) * Real.exp (-c₀ * ‖y‖ ^ 2) =
        Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) := by rw [← Real.exp_add]; congr 1; ring
    calc ‖fderiv ℝ (thermalDensity d s a β) y‖ ≤ S * (1 + ‖y‖) ^ 1 * Real.exp (-c₀ * ‖y‖ ^ 2) := h
      _ = S * (1 + ‖y‖) * Real.exp (-c₀ * ‖y‖ ^ 2) := by rw [pow_one]
      _ ≤ S * (Cp * Real.exp (c₀ / 2 * ‖y‖ ^ 2)) * Real.exp (-c₀ * ‖y‖ ^ 2) := by gcongr
      _ = (S * Cp) * (Real.exp (c₀ / 2 * ‖y‖ ^ 2) * Real.exp (-c₀ * ‖y‖ ^ 2)) := by ring
      _ = (S * Cp) * Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) := by rw [e]
      _ ≤ max M₀ (S * Cp) * Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
  · have h := hcb.2 0 le_rfl y
    rw [norm_iteratedFDeriv_zero, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hβ] at h
    rw [le_div_iff₀ hβ]
    linarith

/-! ### Calculus facts -/

theorem s45_contDiff_gradient {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ) : ContDiff ℝ 1 (gradient χ) := by
  unfold gradient
  exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearEquiv.contDiff).comp
    (hχ.fderiv_right (m := 1) (by norm_num))

theorem s45_div_gradient {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ) (x : Euc d) :
    s45_div (gradient χ) x = Laplacian.laplacian χ x := by
  have hgd : Differentiable ℝ (gradient χ) := (s45_contDiff_gradient hχ).differentiable (by norm_num)
  rw [HRS.MD.DOMProof.domp_lap_eq_sum_ddk hχ.contDiffAt]
  unfold s45_div
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 : (fun y => gradient χ y a) = HRS.MD.DOMProof.dk χ a := by
    funext y; exact HRS.MD.DOMProof.domp_gradient_apply χ y a
  have h2 : HasFDerivAt (fun y => gradient χ y a)
      ((EuclideanSpace.proj a : Euc d →L[ℝ] ℝ).comp (fderiv ℝ (gradient χ) x)) x :=
    (EuclideanSpace.proj a : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x (hgd x).hasFDerivAt
  rw [h1] at h2
  unfold HRS.MD.DOMProof.ddk
  rw [h2.fderiv]
  rfl

/-- The gradient of the potential is the convolution of the kernel with the gradient of the density. -/
theorem s45_gradU_apply (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c C : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) {ρ : Euc d → ℝ} (hρp : IsProbDensity ρ) (hρ1 : ContDiff ℝ 1 ρ)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (hU : Differentiable ℝ (convMeasure (rieszKernel d s) (withDensityReal ρ))) (x : Euc d)
    (b : Fin d) :
    gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) x b =
      ∫ y, rieszKernel d s (x - y) * gradient ρ y b := by
  set e : Euc d := EuclideanSpace.single b (1 : ℝ) with he_def
  have he : ‖e‖ ≤ 1 := movtr_norm_single b
  have hgm : Measurable (rieszKernel d s) := by
    rw [← movtr_gEps_zero d s]; exact movtr_gEps_measurable s 0
  have A := movtr_hasDerivAt_conv (c := c) hc (k := rieszKernel d s)
    (B := fun z => 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) hgm.aestronglyMeasurable
    (by
      filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
      rw [← movtr_gEps_zero d s]
      exact movtr_gEps_abs_le hs0 le_rfl zero_le_one hz)
    (movtr_majorant_integrable hd hs0 hsd (c := c / 2) (by positivity)) hC hρ1 h0 h1 x e he
  have hfun : (fun h : ℝ => ∫ z, rieszKernel d s z * ρ (x + h • e - z)) =
      fun h : ℝ => convMeasure (rieszKernel d s) (withDensityReal ρ) (x + h • e) := by
    funext h
    rw [movtr_convMeasure_eq _ hρp, ← integral_sub_left_eq_self
      (fun y => rieszKernel d s (x + h • e - y) * ρ y) volume (x + h • e)]
    simp
  rw [hfun] at A
  have hline : HasDerivAt (fun h : ℝ => x + h • e) e 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const e).const_add x
    simpa using this
  have hB := (hU (x + (0 : ℝ) • e)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
  have hEq := A.unique hB
  rw [movtr_gradient_apply]
  simp only [zero_smul, add_zero] at hEq
  rw [← he_def, ← hEq]
  rw [← integral_sub_left_eq_self (fun z => rieszKernel d s z * fderiv ℝ ρ (x - z) e) volume x]
  simp [movtr_gradient_apply, he_def]

theorem s45_gen_eq {s a β : ℝ} {χ : Euc d → ℝ}
    (hU : Differentiable ℝ (convMeasure (rieszKernel d s) (thermalMeasure d s a β))) (y : Euc d) :
    thermalGen d s a β χ y = -Laplacian.laplacian χ y +
      β * ⟪a • y + gradient (convMeasure (rieszKernel d s) (thermalMeasure d s a β)) y,
        gradient χ y⟫ := by
  unfold thermalGen
  rw [HRS.MS.Tc1.tc1_gradient_conf_add (hU y) a]

/-- The corrector identity for an abstract density with the thermal structure (`∇ρ = -β ρ ∇(V+U)`). -/
theorem s45_corr_abstract (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β C c BU : ℝ}
    {ρ : Euc d → ℝ} (hρp : IsProbDensity ρ) (hρ1 : ContDiff ℝ 1 ρ) (hC : 0 ≤ C) (hc : 0 < c)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (hUs : ContDiff ℝ 1 (convMeasure (rieszKernel d s) (withDensityReal ρ))) (hBU : 0 ≤ BU)
    (hgU : ∀ y, ‖gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) y‖ ≤ BU)
    (hgr : ∀ y, gradient ρ y = ρ y • (-(a * β) • y +
      (-β) • gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) y))
    {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ) {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1)
    (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) (x : Euc d) :
    ∫ y, ρ y * commutatorKernel d s (gradient χ) x y =
      ⟪gradient χ x, gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) x⟫ +
        ∫ y, ρ y * (rieszKernel d s (x - y) * (-Laplacian.laplacian χ y +
          β * ⟪a • y + gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) y,
            gradient χ y⟫)) := by
  have hd1 : 1 ≤ d := by omega
  set U := convMeasure (rieszKernel d s) (withDensityReal ρ) with hUdef
  set v := gradient χ with hvdef
  have hv1 : ContDiff ℝ 1 v := s45_contDiff_gradient hχ
  have hUd : Differentiable ℝ U := hUs.differentiable (by simp)
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  have hgρ : Continuous (gradient ρ) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hρ1.continuous_fderiv one_ne_zero)
  have hgU' : Continuous (gradient U) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hUs.continuous_fderiv one_ne_zero)
  have hvc : Continuous v := hv1.continuous
  have hdivc := s45_continuous_div hv1
  have hlapc : Continuous (Laplacian.laplacian χ) := by
    have : Laplacian.laplacian χ = s45_div v := funext fun y => (s45_div_gradient hχ y).symm
    rw [this]; exact hdivc
  have hay : Continuous fun y : Euc d => a • y + gradient U y :=
    Continuous.add (f := fun y : Euc d => a • y) (g := gradient U)
      (continuous_id.const_smul a) hgU'
  have hrc : Continuous (fun y => -Laplacian.laplacian χ y + β * ⟪a • y + gradient U y, v y⟫) :=
    hlapc.neg.add (continuous_const.mul (hay.inner hvc))
  have hgm : Measurable (rieszKernel d s) := by
    rw [← movtr_gEps_zero d s]; exact movtr_gEps_measurable s 0
  have hkB : ∀ z : Euc d, z ≠ 0 → |rieszKernel d s z| ≤
      1 * (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) := fun z hz => by
    rw [one_mul, ← movtr_gEps_zero d s]
    exact movtr_gEps_abs_le hs0 le_rfl zero_le_one hz
  have hcomm : ∀ y, commutatorKernel d s v x y = ⟪v x - v y, rieszKernelGrad d s (x - y)⟫ := fun y => rfl
  simp_rw [hcomm]
  rw [s45_obi hd1 hs0 hsd hc hC hρ1 h0 h1 hv1 hB1 hB2 x]
  -- pointwise decomposition
  have hdecomp : ∀ y, rieszKernel d s (x - y) * (⟪gradient ρ y, v x - v y⟫ - ρ y * s45_div v y) =
      ρ y * (rieszKernel d s (x - y) * (-Laplacian.laplacian χ y + β * ⟪a • y + gradient U y, v y⟫)) +
        ∑ b : Fin d, v x b * (rieszKernel d s (x - y) * gradient ρ y b) := by
    intro y
    rw [s45_div_gradient hχ y, hgr y]
    have e : ∑ b : Fin d, v x b * (rieszKernel d s (x - y) * (ρ y • (-(a * β) • y +
        (-β) • gradient U y)) b) =
        rieszKernel d s (x - y) * ρ y * ⟪v x, -(a * β) • y + (-β) • gradient U y⟫ := by
      rw [s45_inner_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
      inner_sub_right, inner_neg_left, inner_neg_right, real_inner_comm y (v x),
      real_inner_comm (gradient U y) (v x)]
    ring
  have hsplit : (fun y => rieszKernel d s (x - y) * (⟪gradient ρ y, v x - v y⟫ - ρ y * s45_div v y)) =
      fun y => ρ y * (rieszKernel d s (x - y) * (-Laplacian.laplacian χ y + β * ⟪a • y + gradient U y, v y⟫)) +
        ∑ b : Fin d, v x b * (rieszKernel d s (x - y) * gradient ρ y b) := funext hdecomp
  rw [hsplit]
  -- integrability
  obtain ⟨Cp, hCp0, hCp⟩ := s45_poly_le (half_pos hc)
  have hI1 : Integrable (fun y => ρ y * (rieszKernel d s (x - y) *
      (-Laplacian.laplacian χ y + β * ⟪a • y + gradient U y, v y⟫))) := by
    have hbd : ∀ y, |ρ y * (-Laplacian.laplacian χ y + β * ⟪a • y + gradient U y, v y⟫)| ≤
        (C * (max (d * B2 + |β| * BU * B1) (|β| * |a| * B1) * Cp)) * Real.exp (-(c / 2) * ‖y‖ ^ 2) := by
      intro y
      rw [abs_mul]
      have hr : |-Laplacian.laplacian χ y + β * ⟪a • y + gradient U y, v y⟫| ≤
          max (d * B2 + |β| * BU * B1) (|β| * |a| * B1) * (1 + ‖y‖) := by
        have e1 : |Laplacian.laplacian χ y| ≤ d * B2 := by
          rw [← s45_div_gradient hχ y]; exact s45_div_le hB2 y
        have e2 : |⟪a • y + gradient U y, v y⟫| ≤ (|a| * ‖y‖ + BU) * B1 := by
          calc |⟪a • y + gradient U y, v y⟫| ≤ ‖a • y + gradient U y‖ * ‖v y‖ := abs_real_inner_le_norm _ _
            _ ≤ (|a| * ‖y‖ + BU) * B1 := by
                refine mul_le_mul ?_ (hB1 y) (norm_nonneg _) (by positivity)
                calc ‖a • y + gradient U y‖ ≤ ‖a • y‖ + ‖gradient U y‖ := norm_add_le _ _
                  _ ≤ |a| * ‖y‖ + BU := by
                      rw [norm_smul, Real.norm_eq_abs]; exact add_le_add le_rfl (hgU y)
        have e3 : |-Laplacian.laplacian χ y + β * ⟪a • y + gradient U y, v y⟫| ≤
            (d * B2) + |β| * ((|a| * ‖y‖ + BU) * B1) := by
          calc _ ≤ |-Laplacian.laplacian χ y| + |β * ⟪a • y + gradient U y, v y⟫| := abs_add_le _ _
            _ ≤ (d * B2) + |β| * ((|a| * ‖y‖ + BU) * B1) := by
                rw [abs_neg, abs_mul]
                exact add_le_add e1 (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
        refine e3.trans ?_
        have hm1 := le_max_left (d * B2 + |β| * BU * B1) (|β| * |a| * B1)
        have hm2 := le_max_right (d * B2 + |β| * BU * B1) (|β| * |a| * B1)
        have hn := norm_nonneg y
        nlinarith [mul_le_mul_of_nonneg_right hm2 hn, abs_nonneg β, abs_nonneg a]
      have hp := hCp ‖y‖ (norm_nonneg _)
      have e : Real.exp (c / 2 * ‖y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2) =
          Real.exp (-(c / 2) * ‖y‖ ^ 2) := by rw [← Real.exp_add]; congr 1; ring
      calc |ρ y| * |-Laplacian.laplacian χ y + β * ⟪a • y + gradient U y, v y⟫|
          ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (max (d * B2 + |β| * BU * B1) (|β| * |a| * B1) * (1 + ‖y‖)) :=
            mul_le_mul (h0 y) hr (abs_nonneg _) (by positivity)
        _ ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (max (d * B2 + |β| * BU * B1) (|β| * |a| * B1) *
              (Cp * Real.exp (c / 2 * ‖y‖ ^ 2))) := by gcongr
        _ = (C * (max (d * B2 + |β| * BU * B1) (|β| * |a| * B1) * Cp)) *
              (Real.exp (c / 2 * ‖y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2)) := by ring
        _ = _ := by rw [e]
    have := s45_LI hd1 hs0 hsd (half_pos hc) (k := fun z => rieszKernel d s z)
      (h := fun y => ρ y * (-Laplacian.laplacian χ y + β * ⟪a • y + gradient U y, v y⟫))
      hgm.aestronglyMeasurable (hρ1.continuous.mul hrc) zero_le_one hkB
      (by positivity) hbd x
    exact this.congr (Filter.Eventually.of_forall fun y => by simp only; ring)
  have hI2 : ∀ b ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun y => v x b * (rieszKernel d s (x - y) * gradient ρ y b)) := by
    intro b _
    have hbd : ∀ y, |gradient ρ y b| ≤ C * Real.exp (-c * ‖y‖ ^ 2) := fun y =>
      (s45_abs_coord_le _ _).trans (by rw [s45_norm_gradient]; exact h1 y)
    have := s45_LI hd1 hs0 hsd hc (k := fun z => rieszKernel d s z) (h := fun y => gradient ρ y b)
      hgm.aestronglyMeasurable ((EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).continuous.comp hgρ)
      zero_le_one hkB hC hbd x
    exact this.const_mul (v x b)
  rw [integral_add hI1 (integrable_finsetSum _ hI2), integral_finsetSum _ hI2, add_comm]
  congr 1
  rw [s45_inner_eq_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, s45_gradU_apply hd1 hs0 hsd hc hC hρp hρ1 h0 h1 hUd x b]

/-- **The pointwise corrector identity** (symmetrised integration by parts against `μ`), thermal form. -/
theorem s45_corr_identity (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β C c BU : ℝ}
    (hT : ThermalData d s a β C c BU) {χ : Euc d → ℝ}
    (hχ : ContDiff ℝ 2 χ) {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1)
    (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) (x : Euc d) :
    ∫ y, commutatorKernel d s (gradient χ) x y ∂(thermalMeasure d s a β) =
      ⟪gradient χ x, gradient (convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x⟫ +
        ∫ y, rieszKernel d s (x - y) * thermalGen d s a β χ y ∂(thermalMeasure d s a β) := by
  have hUd : Differentiable ℝ (convMeasure (rieszKernel d s) (thermalMeasure d s a β)) :=
    hT.Usmooth.differentiable (by simp)
  have hμ : thermalMeasure d s a β = withDensityReal (thermalDensity d s a β) := rfl
  have h := s45_corr_abstract hd hs0 hsd (a := a) (β := β) hT.prob
    (hT.smooth.of_le (by exact_mod_cast le_top)) hT.C0 hT.hc hT.h0 hT.h1
    (hT.Usmooth.of_le (by exact_mod_cast le_top)) hT.BU0 hT.gradU_le hT.grad_rho hχ hB1 hB2 x
  rw [hμ, HRS.MS.TcR.tc2_integral_nu hT.prob, HRS.MS.TcR.tc2_integral_nu hT.prob]
  simp_rw [s45_gen_eq hUd]
  exact h

end S45

end
