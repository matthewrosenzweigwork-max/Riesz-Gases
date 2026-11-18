import HRS.MS.QprepAux3

/-!
# S4.6 packet A4: calculus of the tilted test functionals

`s46_S X = ∑ ‖X i‖²`, `Θ_R = θ(S/R²)`, `G = F e^{-c ∑ U(x_i)}`, `G̃_R = G Θ_R`: smoothness, compact support, the
derivative formulas, and `G̃_R = G` near every `X` once `R² > S X`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S46

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

/-- `S(X) = ∑ ‖x_i‖²`. -/
def s46_S (X : EucConfig d N) : ℝ := ∑ i, ‖X i‖ ^ 2

/-- The cutoff `Θ_R(X) = θ(S(X)/R²)`. -/
def s46_Theta (R : ℝ) (X : EucConfig d N) : ℝ := s46_theta (s46_S X / R ^ 2)

/-- `G = F e^{-c ∑ U(x_i)}`. -/
def s46_G (c : ℝ) (U : Euc d → ℝ) (F : EucConfig d N → ℝ) (X : EucConfig d N) : ℝ :=
  F X * Real.exp (-c * ∑ i, U (X i))

theorem s46_S_nonneg (X : EucConfig d N) : 0 ≤ s46_S X := Finset.sum_nonneg fun i _ => sq_nonneg _

theorem s46_S_contDiff : ContDiff ℝ ∞ (s46_S : EucConfig d N → ℝ) := by
  unfold s46_S
  refine ContDiff.sum fun i _ => ?_
  exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (Euc d) i)

theorem s46_hasFDerivAt_S (X : EucConfig d N) :
    HasFDerivAt (s46_S : EucConfig d N → ℝ)
      (∑ i, (2 : ℝ) • ((innerSL ℝ (X i)).comp (ContinuousLinearMap.proj i : EucConfig d N →L[ℝ] Euc d))) X := by
  unfold s46_S
  have h := HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N)))
    (A := fun i (Y : EucConfig d N) => ‖Y i‖ ^ 2)
    (A' := fun i => (2 : ℝ) • ((innerSL ℝ (X i)).comp (ContinuousLinearMap.proj i : EucConfig d N →L[ℝ] Euc d)))
    (x := X) (fun i _ => by
      have := ((ContinuousLinearMap.proj i : EucConfig d N →L[ℝ] Euc d).hasFDerivAt (x := X)).norm_sq
      simpa [two_smul] using this)
  exact h

theorem s46_fderiv_S_apply (X w : EucConfig d N) :
    fderiv ℝ (s46_S : EucConfig d N → ℝ) X w = ∑ i, 2 * ⟪X i, w i⟫ := by
  rw [(s46_hasFDerivAt_S X).fderiv]
  simp

theorem s46_Theta_contDiff {R : ℝ} : ContDiff ℝ ∞ (s46_Theta R : EucConfig d N → ℝ) :=
  s46_theta_contDiff.comp (s46_S_contDiff.div_const _)

theorem s46_fderiv_Theta_apply {R : ℝ} (X w : EucConfig d N) :
    fderiv ℝ (s46_Theta R : EucConfig d N → ℝ) X w =
      deriv s46_theta (s46_S X / R ^ 2) * ((∑ i, 2 * ⟪X i, w i⟫) / R ^ 2) := by
  have h1 : HasFDerivAt (fun Y : EucConfig d N => s46_S Y / R ^ 2)
      ((1 / R ^ 2) • fderiv ℝ (s46_S : EucConfig d N → ℝ) X) X := by
    have := (s46_hasFDerivAt_S X).mul_const ((R ^ 2)⁻¹)
    rw [(s46_hasFDerivAt_S X).fderiv]
    simpa [div_eq_mul_inv] using this
  have h2 := (s46_theta_contDiff.differentiable (by simp) (s46_S X / R ^ 2)).hasDerivAt.comp_hasFDerivAt X h1
  unfold s46_Theta
  rw [show (s46_theta ∘ fun Y : EucConfig d N => s46_S Y / R ^ 2) = fun Y => s46_theta (s46_S Y / R ^ 2)
    from rfl] at h2
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, s46_fderiv_S_apply]
  ring

theorem s46_Theta_zero {R : ℝ} (hR : 0 < R) {X : EucConfig d N} (hX : 2 * R ^ 2 ≤ s46_S X) :
    s46_Theta R X = 0 := by
  unfold s46_Theta
  refine s46_theta_zero ?_
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem s46_Theta_one {R : ℝ} (hR : 0 < R) {X : EucConfig d N} (hX : s46_S X ≤ R ^ 2) :
    s46_Theta R X = 1 := by
  unfold s46_Theta
  refine s46_theta_one ?_
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem s46_Theta_compact {R : ℝ} (hR : 0 < R) : HasCompactSupport (s46_Theta R : EucConfig d N → ℝ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : EucConfig d N) (2 * R)) fun X hX => ?_
  rw [mem_closedBall_zero_iff, not_le] at hX
  refine s46_Theta_zero hR ?_
  have h1 : ‖X‖ ^ 2 ≤ s46_S X := S45.s45_norm_sq_le_sum X
  nlinarith [norm_nonneg X]

theorem s46_G_contDiff {c : ℝ} {U : Euc d → ℝ} (hU : ContDiff ℝ ∞ U) {F : EucConfig d N → ℝ}
    (hF : ContDiff ℝ 1 F) : ContDiff ℝ 1 (s46_G c U F) := by
  unfold s46_G
  refine hF.mul (Real.contDiff_exp.comp (contDiff_const.mul ?_)) |>.of_le le_rfl
  · exact ContDiff.sum fun i _ => (hU.of_le (by simp)).comp (contDiff_apply ℝ (Euc d) i)

theorem s46_fderiv_G_apply {c : ℝ} {U : Euc d → ℝ} (hU : ContDiff ℝ ∞ U) {F : EucConfig d N → ℝ}
    (hF : Differentiable ℝ F) (X w : EucConfig d N) :
    fderiv ℝ (s46_G c U F) X w = Real.exp (-c * ∑ i, U (X i)) *
      (fderiv ℝ F X w - c * F X * ∑ i, fderiv ℝ U (X i) (w i)) := by
  have hUd : Differentiable ℝ U := hU.differentiable (by simp)
  have hs : HasFDerivAt (fun Y : EucConfig d N => ∑ i, U (Y i))
      (∑ i, (fderiv ℝ U (X i)).comp (ContinuousLinearMap.proj i : EucConfig d N →L[ℝ] Euc d)) X := by
    refine HasFDerivAt.fun_sum (𝕜 := ℝ) (u := (Finset.univ : Finset (Fin N)))
      (A := fun i (Y : EucConfig d N) => U (Y i)) (x := X) (fun i _ => ?_)
    exact (hUd (X i)).hasFDerivAt.comp X (ContinuousLinearMap.proj i : EucConfig d N →L[ℝ] Euc d).hasFDerivAt
  have he := (hs.const_mul (-c)).exp
  have hG := (hF X).hasFDerivAt.fun_mul he
  unfold s46_G
  rw [hG.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply]
  ring

end S46

end
