import HRS.Whole.MovtrAux4

/-!
# MOVTR auxiliary 5: the thermal equation gives `ν∇log ρ + qx + ∇g*ρ = 0`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

lemma movtr_gradient_apply (f : Euc d → ℝ) (x : Euc d) (i : Fin d) :
    gradient f x i = fderiv ℝ f x (EuclideanSpace.single i 1) := by
  have := EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ) (gradient f x)
  simp at this
  rw [← this]

/-- Joint Gaussian bound for `ρ` and `Dρ` from the bounds on every derivative. -/
lemma movtr_gauss01 {ρ : Euc d → ℝ}
    (hgauss : ∀ k : ℕ, ∃ C c : ℝ, 0 < c ∧ ∀ x, ‖iteratedFDeriv ℝ k ρ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2)) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ (∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2)) ∧
      (∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) := by
  obtain ⟨C0, c0, hc0, h0⟩ := hgauss 0
  obtain ⟨C1, c1, hc1, h1⟩ := hgauss 1
  have hC0 : 0 ≤ C0 := by
    have := h0 0
    simp at this
    exact le_trans (abs_nonneg _) this
  have hC1 : 0 ≤ C1 := by
    have := h1 0
    simp at this
    exact le_trans (norm_nonneg _) this
  refine ⟨max C0 C1, min c0 c1, le_max_of_le_left hC0, lt_min hc0 hc1, ?_, ?_⟩
  · intro y
    have := h0 y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    refine this.trans ?_
    have hexp : Real.exp (-c0 * ‖y‖ ^ 2) ≤ Real.exp (-(min c0 c1) * ‖y‖ ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [min_le_left c0 c1, sq_nonneg ‖y‖]
    calc C0 * Real.exp (-c0 * ‖y‖ ^ 2) ≤ max C0 C1 * Real.exp (-c0 * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (le_max_of_le_left hC0)
  · intro y
    have := h1 y
    rw [norm_iteratedFDeriv_one] at this
    refine this.trans ?_
    have hexp : Real.exp (-c1 * ‖y‖ ^ 2) ≤ Real.exp (-(min c0 c1) * ‖y‖ ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [min_le_right c0 c1, sq_nonneg ‖y‖]
    calc C1 * Real.exp (-c1 * ‖y‖ ^ 2) ≤ max C0 C1 * Real.exp (-c1 * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (le_max_of_le_left hC0)

lemma movtr_convMeasure_eq (g : Euc d → ℝ) {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) (x : Euc d) :
    convMeasure g (withDensityReal ρ) x = ∫ y, g (x - y) * ρ y := by
  unfold convMeasure withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul hρ.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (hρ.nonneg y), mul_comm]


/-- The thermal equation yields the pointwise Euler equation `β⁻¹∇log ρ + qx + ∇g*ρ = 0`
(`∇g*ρ` by the cancellation convention). -/
theorem movtr_thermal_force (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β q : ℝ}
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ)
    (hsmooth : ContDiff ℝ ∞ ρ)
    (hgauss : ∀ k : ℕ, ∃ C c : ℝ, 0 < c ∧ ∀ x, ‖iteratedFDeriv ℝ k ρ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2))
    (x : Euc d) :
    β⁻¹ • gradient (fun y => Real.log (ρ y)) x + q • x + convGradConvW (rieszKernelGrad d s) ρ x = 0 := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C, c, hC, hc, h0, h1⟩ := movtr_gauss01 hgauss
  have hρ1 : ContDiff ℝ 1 ρ := hsmooth.of_le (mod_cast le_top)
  have hdiff : Differentiable ℝ ρ := hρ1.differentiable (by norm_num)
  obtain ⟨_, hprob, hth⟩ := hρ
  set Z : ℝ := ∫ y, Real.exp (-β * (confinement q y + convMeasure (rieszKernel d s) (withDensityReal ρ) y))
    with hZ
  have hZpos : 0 < Z := by
    have hZ0 : Z ≠ 0 := by
      intro h
      have hzero : ∀ y, ρ y = 0 := fun y => by rw [hth y]; simp [← hZ, h]
      have := hprob.integral_one
      simp [hzero] at this
    rcases lt_or_gt_of_ne hZ0 with hneg | hpos
    · exfalso
      have h := hprob.nonneg (0 : Euc d)
      rw [hth (0 : Euc d)] at h
      have := div_neg_of_pos_of_neg (Real.exp_pos
        (-β * (confinement q (0 : Euc d) +
          convMeasure (rieszKernel d s) (withDensityReal ρ) (0 : Euc d)))) hneg
      linarith
    · exact hpos
  have hρpos : ∀ y, 0 < ρ y := fun y => by
    rw [hth y]; exact div_pos (Real.exp_pos _) hZpos
  have hlog : ∀ y, Real.log (ρ y) =
      -β * (confinement q y + ∫ u, rieszKernel d s (y - u) * ρ u) - Real.log Z := by
    intro y
    have := hth y
    rw [← movtr_convMeasure_eq _ hprob y]
    conv_lhs => rw [this]
    rw [Real.log_div (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
  ext i
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he_def
  have hQ := movtr_hasDerivAt_potential hd1 hs0 hsd hc hC hρ1 h0 h1 x i
  have hline : HasDerivAt (fun h : ℝ => x + h • e) e 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const e).const_add x
    simpa using this
  have hV : HasDerivAt (fun h : ℝ => confinement q (x + h • e)) (q * x i) 0 := by
    have h2 := ((hasStrictFDerivAt_norm_sq (x + (0:ℝ) • e)).hasFDerivAt).comp_hasDerivAt (0:ℝ) hline
    have h3 := (h2.const_mul q).div_const 2
    unfold confinement
    refine h3.congr_deriv ?_
    simp [he_def, EuclideanSpace.inner_single_right]
    ring
  have hL : HasDerivAt (fun h : ℝ => Real.log (ρ (x + h • e)))
      (-β * (q * x i + (convGradConvW (rieszKernelGrad d s) ρ x) i)) 0 := by
    have h4 := (hV.add hQ).const_mul (-β)
    have h5 := h4.sub_const (Real.log Z)
    refine h5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun h => ?_) |>.congr_deriv (by ring)
    exact hlog _
  have hL2 : HasDerivAt (fun h : ℝ => Real.log (ρ (x + h • e)))
      (fderiv ℝ (fun y => Real.log (ρ y)) x e) 0 := by
    have hf := ((hdiff x).hasFDerivAt.log (hρpos x).ne').differentiableAt
    have hf' : HasFDerivAt (fun y => Real.log (ρ y)) (fderiv ℝ (fun y => Real.log (ρ y)) x)
        (x + (0 : ℝ) • e) := by simpa using hf.hasFDerivAt
    exact hf'.comp_hasDerivAt (0:ℝ) hline
  have hEq := hL2.unique hL
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
  rw [movtr_gradient_apply, hEq]
  field_simp
  ring

end HRS.Whole
