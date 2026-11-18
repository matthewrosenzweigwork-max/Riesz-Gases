import HRS.MS.TiltAux4

/-!
# S4.7 packet P5a: the corrector identity, the weighted integration by parts, the log moment

Ports of `s45_corr_abstract`, `s45_corr_identity`, `s45_ibp_mu`, `s45_thermal_logmoment2` to a reference density
with `∇ρ = ρ (-q x + Bd)` (`TRef`): the weighted generator is `L_ρ χ = -Δχ + ⟨q x - Bd, ∇χ⟩`, and the thermal drift
`β ∇(V + g*μ)` is replaced by the abstract drift `q x - Bd`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S47

open S45
open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- `L_ρ χ = -Δχ + ⟨q x - Bd, ∇χ⟩`. -/
theorem s47_gen_eq {s : ℝ} {ρ : Euc d → ℝ} {q C c BU BB : ℝ} {Bd : Euc d → Euc d}
    (hT : TRef d s ρ q C c BU BB Bd) {χ : Euc d → ℝ} (y : Euc d) :
    weightedGen ρ χ y = -Laplacian.laplacian χ y + ⟪q • y - Bd y, gradient χ y⟫ := by
  unfold weightedGen
  rw [s47_gradient_log hT y]
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_neg_left]
  ring

/-- The corrector identity for a reference density (`∇ρ = ρ (-q x + Bd)`). -/
theorem s47_corr_abstract (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ}
    {q C c BU BB : ℝ} {Bd : Euc d → Euc d} (hT : TRef d s ρ q C c BU BB Bd)
    {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ) {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1)
    (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) (x : Euc d) :
    ∫ y, ρ y * commutatorKernel d s (gradient χ) x y =
      ⟪gradient χ x, gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) x⟫ +
        ∫ y, ρ y * (rieszKernel d s (x - y) * (-Laplacian.laplacian χ y +
          ⟪q • y - Bd y, gradient χ y⟫)) := by
  have hd1 : 1 ≤ d := by omega
  have hρp := hT.prob
  have hρ1 : ContDiff ℝ 1 ρ := hT.smooth.of_le (by exact_mod_cast le_top)
  have hC := hT.C0
  have hc := hT.hc
  have h0 := hT.h0
  have h1 := hT.h1
  have hUs : ContDiff ℝ 1 (convMeasure (rieszKernel d s) (withDensityReal ρ)) :=
    hT.Usmooth.of_le (by exact_mod_cast le_top)
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
  have hay : Continuous fun y : Euc d => q • y - Bd y :=
    (continuous_id.const_smul q).sub hT.Bd_cont
  have hrc : Continuous (fun y => -Laplacian.laplacian χ y + ⟪q • y - Bd y, v y⟫) :=
    hlapc.neg.add (hay.inner hvc)
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
      ρ y * (rieszKernel d s (x - y) * (-Laplacian.laplacian χ y + ⟪q • y - Bd y, v y⟫)) +
        ∑ b : Fin d, v x b * (rieszKernel d s (x - y) * gradient ρ y b) := by
    intro y
    rw [s45_div_gradient hχ y]
    have e2 : ⟪gradient ρ y, v y⟫ = ρ y * ⟪-q • y + Bd y, v y⟫ := by
      rw [hT.grad_rho y, real_inner_smul_left]
    have e3 : ⟪-q • y + Bd y, v y⟫ = -⟪q • y - Bd y, v y⟫ := by
      simp only [inner_sub_left, inner_add_left, real_inner_smul_left, neg_mul]
      ring
    have hsum : rieszKernel d s (x - y) * ∑ b : Fin d, gradient ρ y b * v x b =
        ∑ b : Fin d, v x b * (rieszKernel d s (x - y) * gradient ρ y b) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
    rw [inner_sub_right, e2, e3, s45_inner_eq_sum (gradient ρ y) (v x), ← hsum]
    ring
  have hsplit : (fun y => rieszKernel d s (x - y) * (⟪gradient ρ y, v x - v y⟫ - ρ y * s45_div v y)) =
      fun y => ρ y * (rieszKernel d s (x - y) * (-Laplacian.laplacian χ y + ⟪q • y - Bd y, v y⟫)) +
        ∑ b : Fin d, v x b * (rieszKernel d s (x - y) * gradient ρ y b) := funext hdecomp
  rw [hsplit]
  -- integrability
  obtain ⟨Cp, hCp0, hCp⟩ := s45_poly_le (half_pos hc)
  have hI1 : Integrable (fun y => ρ y * (rieszKernel d s (x - y) *
      (-Laplacian.laplacian χ y + ⟪q • y - Bd y, v y⟫))) := by
    have hbd : ∀ y, |ρ y * (-Laplacian.laplacian χ y + ⟪q • y - Bd y, v y⟫)| ≤
        (C * (max (d * B2 + BB * B1) (|q| * B1) * Cp)) * Real.exp (-(c / 2) * ‖y‖ ^ 2) := by
      intro y
      rw [abs_mul]
      have hr : |-Laplacian.laplacian χ y + ⟪q • y - Bd y, v y⟫| ≤
          max (d * B2 + BB * B1) (|q| * B1) * (1 + ‖y‖) := by
        have e1 : |Laplacian.laplacian χ y| ≤ d * B2 := by
          rw [← s45_div_gradient hχ y]; exact s45_div_le hB2 y
        have e2 : |⟪q • y - Bd y, v y⟫| ≤ (|q| * ‖y‖ + BB) * B1 := by
          calc |⟪q • y - Bd y, v y⟫| ≤ ‖q • y - Bd y‖ * ‖v y‖ := abs_real_inner_le_norm _ _
            _ ≤ (|q| * ‖y‖ + BB) * B1 := by
                refine mul_le_mul ?_ (hB1 y) (norm_nonneg _) (by have := hT.BB0; positivity)
                calc ‖q • y - Bd y‖ ≤ ‖q • y‖ + ‖Bd y‖ := norm_sub_le _ _
                  _ ≤ |q| * ‖y‖ + BB := by
                      rw [norm_smul, Real.norm_eq_abs]; exact add_le_add le_rfl (hT.Bd_le y)
        have e3 : |-Laplacian.laplacian χ y + ⟪q • y - Bd y, v y⟫| ≤
            (d * B2) + ((|q| * ‖y‖ + BB) * B1) := by
          calc _ ≤ |-Laplacian.laplacian χ y| + |⟪q • y - Bd y, v y⟫| := abs_add_le _ _
            _ ≤ (d * B2) + ((|q| * ‖y‖ + BB) * B1) := by
                rw [abs_neg]
                exact add_le_add e1 e2
        refine e3.trans ?_
        have hm1 := le_max_left (d * B2 + BB * B1) (|q| * B1)
        have hm2 := le_max_right (d * B2 + BB * B1) (|q| * B1)
        have hn := norm_nonneg y
        nlinarith [mul_le_mul_of_nonneg_right hm2 hn, abs_nonneg q]
      have hp := hCp ‖y‖ (norm_nonneg _)
      have e : Real.exp (c / 2 * ‖y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2) =
          Real.exp (-(c / 2) * ‖y‖ ^ 2) := by rw [← Real.exp_add]; congr 1; ring
      calc |ρ y| * |-Laplacian.laplacian χ y + ⟪q • y - Bd y, v y⟫|
          ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (max (d * B2 + BB * B1) (|q| * B1) * (1 + ‖y‖)) :=
            mul_le_mul (h0 y) hr (abs_nonneg _) (by positivity)
        _ ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (max (d * B2 + BB * B1) (|q| * B1) *
              (Cp * Real.exp (c / 2 * ‖y‖ ^ 2))) := by gcongr
        _ = (C * (max (d * B2 + BB * B1) (|q| * B1) * Cp)) *
              (Real.exp (c / 2 * ‖y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2)) := by ring
        _ = _ := by rw [e]
    have := s45_LI hd1 hs0 hsd (half_pos hc) (k := fun z => rieszKernel d s z)
      (h := fun y => ρ y * (-Laplacian.laplacian χ y + ⟪q • y - Bd y, v y⟫))
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



/-- **The pointwise corrector identity** (symmetrised integration by parts against `μ`). -/
theorem s47_corr_identity (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ}
    {q C c BU BB : ℝ} {Bd : Euc d → Euc d} (hT : TRef d s ρ q C c BU BB Bd) {χ : Euc d → ℝ}
    (hχ : ContDiff ℝ 2 χ) {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1)
    (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) (x : Euc d) :
    ∫ y, commutatorKernel d s (gradient χ) x y ∂(withDensityReal ρ) =
      ⟪gradient χ x, gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) x⟫ +
        ∫ y, rieszKernel d s (x - y) * weightedGen ρ χ y ∂(withDensityReal ρ) := by
  have h := s47_corr_abstract hd hs0 hsd hT hχ hB1 hB2 x
  rw [HRS.MS.TcR.tc2_integral_nu hT.prob, HRS.MS.TcR.tc2_integral_nu hT.prob]
  simp_rw [s47_gen_eq hT]
  exact h

theorem s47_logmoment2 {s : ℝ} {ρ : Euc d → ℝ} {q C c BU BB : ℝ} {Bd : Euc d → Euc d}
    (hT : TRef d s ρ q C c BU BB Bd) : ∃ L, HasLogMoment2 (withDensityReal ρ) L := by
  have hμ : withDensityReal ρ = withDensityReal (ρ) := rfl
  have hc := hT.hc
  obtain ⟨Cp, hCp0, hCp⟩ := s45_poly_le (c := c / 4) (by positivity)
  have hint : Integrable (fun x : Euc d => Real.log (2 + ‖x‖) ^ 2) (withDensityReal ρ) := by
    rw [hμ, HRS.MS.TcR.tc2_integrable_nu hT.prob]
    have hg := HRS.MP.SelfSimP4Impl.p4g_integrable_gauss d (b := c / 2) (by positivity)
    refine Integrable.mono' (hg.const_mul (C * Cp ^ 2))
      ((hT.prob.measurable.mul (((Real.measurable_log.comp
        (measurable_const.add measurable_norm))).pow_const 2)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    have hn := norm_nonneg y
    have hl0 : 0 ≤ Real.log (2 + ‖y‖) := Real.log_nonneg (by linarith)
    have hl1 : Real.log (2 + ‖y‖) ≤ 1 + ‖y‖ := by
      have := Real.log_le_sub_one_of_pos (x := 2 + ‖y‖) (by positivity); linarith
    have hl2 : Real.log (2 + ‖y‖) ^ 2 ≤ (Cp * Real.exp (c / 4 * ‖y‖ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ hl0 (hl1.trans (hCp ‖y‖ hn)) 2
    have e : (Cp * Real.exp (c / 4 * ‖y‖ ^ 2)) ^ 2 = Cp ^ 2 * Real.exp (c / 2 * ‖y‖ ^ 2) := by
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    have e2 : Real.exp (c / 2 * ‖y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2) =
        Real.exp (-(c / 2 * ‖y‖ ^ 2)) := by rw [← Real.exp_add]; congr 1; ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hT.prob.nonneg y) (sq_nonneg _))]
    calc ρ y * Real.log (2 + ‖y‖) ^ 2
        ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * (Cp ^ 2 * Real.exp (c / 2 * ‖y‖ ^ 2)) := by
          refine mul_le_mul ?_ (hl2.trans e.le) (sq_nonneg _) (by have := hT.C0; positivity)
          exact (le_abs_self _).trans (hT.h0 y)
      _ = (C * Cp ^ 2) * (Real.exp (c / 2 * ‖y‖ ^ 2) * Real.exp (-c * ‖y‖ ^ 2)) := by ring
      _ = _ := by rw [e2]
  exact ⟨_, hint, le_rfl⟩

/-- Integration by parts against the thermal measure: `∫ φ (Lχ) dμ = ∫ ⟨∇φ, ∇χ⟩ dμ`. -/
theorem s47_ibp_mu {s : ℝ} {ρ : Euc d → ℝ} {q C c BU BB : ℝ} {Bd : Euc d → Euc d}
    (hT : TRef d s ρ q C c BU BB Bd) {χ : Euc d → ℝ}
    (hχ : ContDiff ℝ 2 χ) {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1)
    (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) {φ : Euc d → ℝ} (hφ : ContDiff ℝ 1 φ) {Bφ Dφ : ℝ}
    (hBφ : ∀ x, |φ x| ≤ Bφ) (hDφ : ∀ x, ‖fderiv ℝ φ x‖ ≤ Dφ) :
    ∫ y, φ y * weightedGen ρ χ y ∂(withDensityReal ρ) =
      ∫ y, ⟪gradient φ y, gradient χ y⟫ ∂(withDensityReal ρ) := by
  set U := convMeasure (rieszKernel d s) (withDensityReal ρ) with hUdef
  set v := gradient χ with hvdef
  have hc := hT.hc
  have hC := hT.C0
  have hμ : withDensityReal ρ = withDensityReal ρ := rfl
  have hρ1 : ContDiff ℝ 1 ρ := hT.smooth.of_le (by exact_mod_cast le_top)
  have hv1 : ContDiff ℝ 1 v := s45_contDiff_gradient hχ
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  have hBφ0 : 0 ≤ Bφ := (abs_nonneg _).trans (hBφ 0)
  have hDφ0 : 0 ≤ Dφ := (norm_nonneg _).trans (hDφ 0)
  have hg := HRS.MP.SelfSimP4Impl.p4g_integrable_gauss d hc
  have hgE : ∀ y : Euc d, Real.exp (-c * ‖y‖ ^ 2) = Real.exp (-(c * ‖y‖ ^ 2)) := fun y => by rw [neg_mul]
  have hρd : Differentiable ℝ ρ := hρ1.differentiable (by norm_num)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hfd : Differentiable ℝ (fun y => φ y * ρ y) := hφd.mul hρd
  -- bounds
  have hfb : ∀ y, |φ y * ρ y| ≤ (Bφ * C) * Real.exp (-(c * ‖y‖ ^ 2)) := by
    intro y; rw [abs_mul, ← hgE]
    calc |φ y| * |ρ y| ≤ Bφ * (C * Real.exp (-c * ‖y‖ ^ 2)) :=
          mul_le_mul (hBφ y) (hT.h0 y) (abs_nonneg _) hBφ0
      _ = _ := by ring
  have hρ' : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-(c * ‖y‖ ^ 2)) := fun y => by rw [← hgE]; exact hT.h1 y
  have hρ0 : ∀ y, |ρ y| ≤ C * Real.exp (-(c * ‖y‖ ^ 2)) := fun y => by rw [← hgE]; exact hT.h0 y
  have hfd' : ∀ y, HasFDerivAt (fun y => φ y * ρ y) (φ y • fderiv ℝ ρ y + ρ y • fderiv ℝ φ y) y :=
    fun y => (hφd y).hasFDerivAt.mul (hρd y).hasFDerivAt
  have hdf : ∀ y, ‖fderiv ℝ (fun y => φ y * ρ y) y‖ ≤ (Dφ * C + Bφ * C) * Real.exp (-(c * ‖y‖ ^ 2)) := by
    intro y
    rw [(hfd' y).fderiv]
    calc ‖φ y • fderiv ℝ ρ y + ρ y • fderiv ℝ φ y‖ ≤ ‖φ y • fderiv ℝ ρ y‖ + ‖ρ y • fderiv ℝ φ y‖ :=
          norm_add_le _ _
      _ ≤ (Bφ * (C * Real.exp (-(c * ‖y‖ ^ 2)))) + ((C * Real.exp (-(c * ‖y‖ ^ 2))) * Dφ) := by
          refine add_le_add ?_ ?_
          · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hBφ y) (hρ' y) (norm_nonneg _) hBφ0
          · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hρ0 y) (hDφ y) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hfC : ContDiff ℝ 1 (fun y => φ y * ρ y) := hφ.mul hρ1
  have hnb : ∀ b : Fin d, ‖(EuclideanSpace.single b (1 : ℝ) : Euc d)‖ ≤ 1 := fun b => by simp
  have hgb : ∀ b : Fin d, ContDiff ℝ 1 (fun y => v y b) := fun b =>
    (EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).contDiff.comp hv1
  have hgbd : ∀ (b : Fin d) (y : Euc d), HasFDerivAt (fun y => v y b)
      ((EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).comp (fderiv ℝ v y)) y := fun b y =>
    (EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).hasFDerivAt.comp y
      ((hv1.differentiable (by norm_num)) y).hasFDerivAt
  have hgbB : ∀ (b : Fin d) (y : Euc d), |v y b| ≤ B1 := fun b y => (s45_abs_coord_le _ _).trans (hB1 y)
  have hgbD : ∀ (b : Fin d) (y : Euc d), |fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1)| ≤ B2 := by
    intro b y
    rw [(hgbd b y).fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    refine (s45_abs_coord_le _ _).trans ?_
    calc ‖fderiv ℝ v y (EuclideanSpace.single b (1 : ℝ))‖
        ≤ ‖fderiv ℝ v y‖ * ‖(EuclideanSpace.single b (1 : ℝ) : Euc d)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ B2 * 1 := mul_le_mul (hB2 y) (hnb b) (norm_nonneg _) hB20
      _ = B2 := mul_one _
  have key : ∀ b : Fin d,
      Integrable (fun y => φ y * ρ y * fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1)) ∧
      Integrable (fun y => fderiv ℝ (fun y => φ y * ρ y) y (EuclideanSpace.single b 1) * v y b) ∧
      ∫ y, φ y * ρ y * fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1) =
        -∫ y, fderiv ℝ (fun y => φ y * ρ y) y (EuclideanSpace.single b 1) * v y b := by
    intro b
    have hgd : Differentiable ℝ (fun y => v y b) := (hgb b).differentiable (by norm_num)
    have hI1 : Integrable (fun y => φ y * ρ y * fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1)) := by
      refine Integrable.mono' (hg.const_mul ((Bφ * C) * B2))
        ((hfC.continuous.mul ((hgb b).continuous_fderiv one_ne_zero |>.clm_apply continuous_const)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      calc |φ y * ρ y| * |fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1)|
          ≤ ((Bφ * C) * Real.exp (-(c * ‖y‖ ^ 2))) * B2 := mul_le_mul (hfb y) (hgbD b y) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hI2 : Integrable (fun y => fderiv ℝ (fun y => φ y * ρ y) y (EuclideanSpace.single b 1) * v y b) := by
      refine Integrable.mono' (hg.const_mul ((Dφ * C + Bφ * C) * B1))
        ((((hfC.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul (hgb b).continuous).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |fderiv ℝ (fun y => φ y * ρ y) y (EuclideanSpace.single b 1)| ≤
          (Dφ * C + Bφ * C) * Real.exp (-(c * ‖y‖ ^ 2)) := by
        refine le_trans ?_ (hdf y)
        calc |fderiv ℝ (fun y => φ y * ρ y) y (EuclideanSpace.single b 1)|
            = ‖fderiv ℝ (fun y => φ y * ρ y) y (EuclideanSpace.single b 1)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ (fun y => φ y * ρ y) y‖ * ‖(EuclideanSpace.single b (1 : ℝ) : Euc d)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖fderiv ℝ (fun y => φ y * ρ y) y‖ * 1 := by gcongr; exact hnb b
          _ = _ := mul_one _
      calc _ ≤ ((Dφ * C + Bφ * C) * Real.exp (-(c * ‖y‖ ^ 2))) * B1 :=
            mul_le_mul h1 (hgbB b y) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hI3 : Integrable (fun y => φ y * ρ y * v y b) := by
      refine Integrable.mono' (hg.const_mul ((Bφ * C) * B1))
        ((hfC.continuous.mul (hgb b).continuous).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      calc |φ y * ρ y| * |v y b| ≤ ((Bφ * C) * Real.exp (-(c * ‖y‖ ^ 2))) * B1 :=
            mul_le_mul (hfb y) (hgbB b y) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    exact ⟨hI1, hI2, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
      (f := fun y => φ y * ρ y) (g := fun y => v y b) (v := EuclideanSpace.single b 1)
      hI2 hI1 hI3 (fun y _ => hfd y) (fun y _ => hgd y)⟩
  -- sum over the coordinates
  have hsum : ∑ b : Fin d, ∫ y, φ y * ρ y * fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1) =
      -∑ b : Fin d, ∫ y, fderiv ℝ (fun y => φ y * ρ y) y (EuclideanSpace.single b 1) * v y b := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun b _ => (key b).2.2
  rw [← integral_finsetSum _ (fun b _ => (key b).1), ← integral_finsetSum _ (fun b _ => (key b).2.1),
    ← integral_neg] at hsum
  have hdivp : ∀ y, ∑ b : Fin d, φ y * ρ y * fderiv ℝ (fun y => v y b) y (EuclideanSpace.single b 1) =
      φ y * ρ y * s45_div v y := by
    intro y
    rw [← Finset.mul_sum]
    congr 1
    unfold s45_div
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [(hgbd b y).fderiv]; rfl
  have hgrad : ∀ y, ∑ b : Fin d, fderiv ℝ (fun y => φ y * ρ y) y (EuclideanSpace.single b 1) * v y b =
      φ y * ⟪gradient ρ y, v y⟫ + ρ y * ⟪gradient φ y, v y⟫ := by
    intro y
    rw [s45_inner_eq_sum, s45_inner_eq_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [(hfd' y).fderiv]
    simp only [movtr_gradient_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  simp_rw [hdivp, hgrad] at hsum
  -- integrability of the two pieces
  have hgρ : Continuous (gradient ρ) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hρ1.continuous_fderiv one_ne_zero)
  have hgφ : Continuous (gradient φ) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
  have hA : Integrable (fun y => φ y * ⟪gradient ρ y, v y⟫) := by
    refine Integrable.mono' (hg.const_mul (Bφ * (C * B1)))
      ((hφ.continuous.mul (hgρ.inner hv1.continuous)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |φ y| * |⟪gradient ρ y, v y⟫| ≤ Bφ * ((C * Real.exp (-(c * ‖y‖ ^ 2))) * B1) := by
          refine mul_le_mul (hBφ y) ?_ (abs_nonneg _) hBφ0
          calc |⟪gradient ρ y, v y⟫| ≤ ‖gradient ρ y‖ * ‖v y‖ := abs_real_inner_le_norm _ _
            _ ≤ (C * Real.exp (-(c * ‖y‖ ^ 2))) * B1 := by
                refine mul_le_mul ?_ (hB1 y) (norm_nonneg _) (by positivity)
                rw [s45_norm_gradient]; exact hρ' y
      _ = _ := by ring
  have hB : Integrable (fun y => ρ y * ⟪gradient φ y, v y⟫) := by
    refine Integrable.mono' (hg.const_mul (C * (Dφ * B1)))
      ((hρ1.continuous.mul (hgφ.inner hv1.continuous)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |ρ y| * |⟪gradient φ y, v y⟫| ≤ (C * Real.exp (-(c * ‖y‖ ^ 2))) * (Dφ * B1) := by
          refine mul_le_mul (hρ0 y) ?_ (abs_nonneg _) (by positivity)
          calc |⟪gradient φ y, v y⟫| ≤ ‖gradient φ y‖ * ‖v y‖ := abs_real_inner_le_norm _ _
            _ ≤ Dφ * B1 := by
                refine mul_le_mul ?_ (hB1 y) (norm_nonneg _) hDφ0
                rw [s45_norm_gradient]; exact hDφ y
      _ = _ := by ring
  have hdivI : Integrable (fun y => φ y * ρ y * s45_div v y) :=
    (integrable_finsetSum _ fun b _ => (key b).1).congr (Filter.Eventually.of_forall hdivp)
  rw [integral_neg, integral_add hA hB] at hsum
  have hgenp : ∀ y, ρ y * (φ y * weightedGen ρ χ y) =
      -(φ y * ρ y * s45_div v y) - φ y * ⟪gradient ρ y, v y⟫ := by
    intro y
    rw [s47_gen_eq hT y, s45_div_gradient hχ y, hT.grad_rho y]
    simp only [real_inner_smul_left, inner_add_left, inner_sub_left]
    ring
  rw [hμ, HRS.MS.TcR.tc2_integral_nu hT.prob (fun y => φ y * weightedGen ρ χ y),
    HRS.MS.TcR.tc2_integral_nu hT.prob (fun y => ⟪gradient φ y, gradient χ y⟫)]
  show ∫ x, ρ x * (φ x * weightedGen ρ χ x) = ∫ x, ρ x * ⟪gradient φ x, v x⟫
  simp_rw [hgenp]
  have hdivI' : Integrable (fun y => -(φ y * ρ y * s45_div v y)) := hdivI.neg
  rw [integral_sub hdivI' hA, integral_neg, hsum]
  ring


end S47

end
