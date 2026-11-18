import HRS.MS.S82UB2

/-!
# S8.2 A01 (S82U): the nonlocal term `oneJ` in grouped form and its `μ`-mean
`J ψ (x) = ∑_j (conv (ρ ψ_j)) (x)_j = ∫ ρ(z) <∇g(x-z), ψ(z) - ψ(x)> dz + <ψ(x), F_μ(x)>`, and
`∫ ρ J ψ = - ∫ ρ <ψ, F_μ>`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T HRS.MH.PairingRd

lemma u_pointwise {d : ℕ} (rho : Euc d → ℝ) (ψ : Euc d → Euc d) (x y : Euc d) :
    ∑ j : Fin d, (convInt (rieszKernelGrad d (criticalS d)) (fun w => rho w * ψ w j) x y) j =
      rho y * inner ℝ (rieszKernelGrad d (criticalS d) (x - y)) (ψ y - ψ x) +
        inner ℝ (ψ x) (convInt (rieszKernelGrad d (criticalS d)) rho x y) := by
  unfold convInt
  by_cases h : ‖x - y‖ ≤ 1 / 4
  · simp only [if_pos h, PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply, PiLp.sub_apply,
      RCLike.inner_apply, conj_trivial, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp only [if_neg h, PiLp.smul_apply, smul_eq_mul, PiLp.inner_apply, PiLp.sub_apply,
      RCLike.inner_apply, conj_trivial, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

lemma u_conv_norm_le {d : ℕ} {rho : Euc d → ℝ} (hρ0 : ∀ x, 0 ≤ rho x) (ψ : Euc d → Euc d) (x y : Euc d)
    (j : Fin d) :
    ‖convInt (rieszKernelGrad d (criticalS d)) (fun w => rho w * ψ w j) x y‖ ≤
      rho y * (‖rieszKernelGrad d (criticalS d) (x - y)‖ * ‖ψ y - ψ x‖) +
        ‖ψ x‖ * ‖convInt (rieszKernelGrad d (criticalS d)) rho x y‖ := by
  have hj : ∀ v : Euc d, |v j| ≤ ‖v‖ := fun v => by
    have := PiLp.norm_apply_le v j
    rwa [Real.norm_eq_abs] at this
  have hG := norm_nonneg (rieszKernelGrad d (criticalS d) (x - y))
  have hψ := norm_nonneg (ψ y - ψ x)
  have hψx := norm_nonneg (ψ x)
  have hry := hρ0 y
  unfold convInt
  by_cases h : ‖x - y‖ ≤ 1 / 4
  · simp only [if_pos h, norm_smul, Real.norm_eq_abs]
    have e1 : rho y * ψ y j - rho x * ψ x j = rho y * (ψ y j - ψ x j) + (rho y - rho x) * ψ x j := by ring
    have e2 : |rho y * ψ y j - rho x * ψ x j| ≤ rho y * ‖ψ y - ψ x‖ + |rho y - rho x| * ‖ψ x‖ := by
      rw [e1]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hry]
      have a1 : |ψ y j - ψ x j| ≤ ‖ψ y - ψ x‖ := by
        have := hj (ψ y - ψ x); simpa using this
      have a2 := hj (ψ x)
      gcongr
    calc |rho y * ψ y j - rho x * ψ x j| * ‖rieszKernelGrad d (criticalS d) (x - y)‖
        ≤ (rho y * ‖ψ y - ψ x‖ + |rho y - rho x| * ‖ψ x‖) * ‖rieszKernelGrad d (criticalS d) (x - y)‖ :=
          mul_le_mul_of_nonneg_right e2 hG
      _ = _ := by ring
  · simp only [if_neg h, norm_smul, Real.norm_eq_abs]
    have e2 : |rho y * ψ y j| ≤ rho y * ‖ψ y - ψ x‖ + rho y * ‖ψ x‖ := by
      rw [abs_mul, abs_of_nonneg hry]
      have a1 : |ψ y j| ≤ ‖ψ y - ψ x‖ + ‖ψ x‖ := by
        refine (hj (ψ y)).trans ?_
        have := norm_le_norm_add_norm_sub' (ψ y) (ψ x)
        linarith
      nlinarith
    calc |rho y * ψ y j| * ‖rieszKernelGrad d (criticalS d) (x - y)‖
        ≤ (rho y * ‖ψ y - ψ x‖ + rho y * ‖ψ x‖) * ‖rieszKernelGrad d (criticalS d) (x - y)‖ :=
          mul_le_mul_of_nonneg_right e2 hG
      _ = _ := by rw [abs_of_nonneg hry]; ring

lemma u_JE {d : ℕ} (hd : 2 ≤ d) {rho : Euc d → ℝ} {Λ : ℝ} (hF : UForce d rho Λ)
    {ψ : Euc d → Euc d} (hψm : Measurable ψ) {x : Euc d}
    (hx : Integrable (fun z => rho z * (‖rieszKernelGrad d (criticalS d) (x - z)‖ * ‖ψ z - ψ x‖))) :
    ∑ j : Fin d, (convGradConvW (rieszKernelGrad d (criticalS d)) (fun w => rho w * ψ w j) x) j =
      (∫ z, rho z * inner ℝ (rieszKernelGrad d (criticalS d) (x - z)) (ψ z - ψ x)) +
        inner ℝ (ψ x) (forceMean rho x) := by
  set Gf := rieszKernelGrad d (criticalS d) with hGf
  have hρm := hF.prob.measurable
  have hρ0 := hF.prob.nonneg
  obtain ⟨hcint, -⟩ := u_conv_unif hd hF
  have hG : Measurable Gf := HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)
  have hsubx : Measurable (fun y : Euc d => x - y) := measurable_const.sub measurable_id
  have hmeasj : ∀ j : Fin d, Measurable (convInt Gf (fun w => rho w * ψ w j) x) := by
    intro j
    have hh : Measurable (fun w : Euc d => rho w * ψ w j) :=
      hρm.mul ((EuclideanSpace.proj j).continuous.measurable.comp hψm)
    unfold convInt
    refine Measurable.ite (measurableSet_le (measurable_norm.comp hsubx) measurable_const) ?_ ?_
    · exact (hh.sub measurable_const).smul (hG.comp hsubx)
    · exact hh.smul (hG.comp hsubx)
  have hintj : ∀ j : Fin d, Integrable (convInt Gf (fun w => rho w * ψ w j) x) := by
    intro j
    refine Integrable.mono' (hx.add ((hcint x).norm.const_mul ‖ψ x‖))
      (hmeasj j).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    exact u_conv_norm_le hρ0 ψ x y j
  have hcomp : ∀ j : Fin d, (convGradConvW Gf (fun w => rho w * ψ w j) x) j =
      ∫ y, (convInt Gf (fun w => rho w * ψ w j) x y) j := by
    intro j
    have h1 := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integral_comp_comm (hintj j)
    simp only [PiLp.proj_apply] at h1
    exact h1.symm
  have hintc : ∀ j : Fin d, Integrable (fun y => (convInt Gf (fun w => rho w * ψ w j) x y) j) :=
    fun j => ContinuousLinearMap.integrable_comp (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) (hintj j)
  simp_rw [hcomp]
  rw [← integral_finset_sum _ fun j _ => hintc j]
  have hpw : ∀ y, ∑ j : Fin d, (convInt Gf (fun w => rho w * ψ w j) x y) j =
      rho y * inner ℝ (Gf (x - y)) (ψ y - ψ x) + inner ℝ (ψ x) (convInt Gf rho x y) :=
    fun y => u_pointwise rho ψ x y
  simp_rw [hpw]
  -- integrability of the two pieces
  have hA : Integrable (fun y => rho y * inner ℝ (Gf (x - y)) (ψ y - ψ x)) := by
    refine Integrable.mono' hx ?_ (Eventually.of_forall fun y => ?_)
    · exact (hρm.mul (Measurable.inner (hG.comp hsubx) (hψm.sub measurable_const))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 y)]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (hρ0 y)
  have hB : Integrable (fun y => inner ℝ (ψ x) (convInt Gf rho x y)) :=
    ContinuousLinearMap.integrable_comp (innerSL ℝ (ψ x)) (hcint x)
  rw [integral_add hA hB, integral_inner (hcint x) (ψ x)]
  rfl

end HRS.MS.S82U
