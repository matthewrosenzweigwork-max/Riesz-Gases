import HRS.MS.SpecAux86
import HRS.MS.SpecAux66
import HRS.MS.SpecAux49
import HRS.MS.Poinc

/-!
# S8M: the LSI constant and the Hessian lower bound of the thermal measure (S8.7, R1-R2)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.
* `s8p_gaussianComparison_eq`: `gaussianComparison d a β x = r^d gd(r x)`, `r = √(βa)`.
* `s8p_lsi_thermal`: a probability density `ρ` on `Euc d` with `c γ_{βa} ≤ ρ ≤ C γ_{βa}` satisfies the log-Sobolev
  inequality with constant `2C/(c β a)`.
* `s8p_W_data`: for `W = -log ρ` (`Mov2eRho`, `Mov2eEll`): `W ∈ C^∞`, `∇ρ = -ρ ∇W`, `D²W ≥ -κ`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec

theorem s8p_gaussianComparison_eq {d : ℕ} {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (x : Euc d) :
    gaussianComparison d a β x =
      Real.sqrt (β * a) ^ Module.finrank ℝ (Euc d) * s8p_gd (Real.sqrt (β * a) • x) := by
  have hba : 0 < β * a := mul_pos hβ ha
  have hfin : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  unfold gaussianComparison s8p_gd
  rw [hfin, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hba.le]
  have e1 : (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) =
      Real.sqrt (β * a) ^ d * (2 * Real.pi) ^ (-(d : ℝ) / 2) := by
    rw [Real.div_rpow hba.le (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hba.le, div_eq_mul_inv, ← Real.rpow_neg (by positivity)]
    congr 2 <;> ring
  have e2 : Real.exp (-β * a * ‖x‖ ^ 2 / 2) = Real.exp (-(β * a * ‖x‖ ^ 2) / 2) := by
    congr 1; ring
  rw [e1, e2]
  ring

theorem s8p_lsi_thermal {d : ℕ} {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρm : Measurable ρ) {c C : ℝ} (hc : 0 < c)
    (hlo : ∀ x, c * gaussianComparison d a β x ≤ ρ x)
    (hhi : ∀ x, ρ x ≤ C * gaussianComparison d a β x) (hone : ∫ x, ρ x = 1) :
    s8p_LSI (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) (2 * C / c / (β * a)) := by
  have hba : 0 < β * a := mul_pos hβ ha
  have hr : 0 < Real.sqrt (β * a) := Real.sqrt_pos.2 hba
  have := s8p_lsi_dilate (V := Euc d) hρm hr hc
    (fun x => by rw [← s8p_gaussianComparison_eq ha hβ]; exact hlo x)
    (fun x => by rw [← s8p_gaussianComparison_eq ha hβ]; exact hhi x) hone
  rwa [Real.sq_sqrt hba.le] at this

/-- `W = -log ρ` and the lower Hessian bound. -/
theorem s8p_W_data {d : ℕ} {ρ : Euc d → ℝ} (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ContDiff ℝ ∞ (fun x => -Real.log (ρ x)) ∧
      (∀ x, fderiv ℝ ρ x = -(ρ x) • fderiv ℝ (fun y => -Real.log (ρ y)) x) ∧
      ∀ x v, -(κ * ‖v‖ ^ 2) ≤ fderiv ℝ (fderiv ℝ (fun y => -Real.log (ρ y))) x v v := by
  obtain ⟨c, a, M0, hc, ha, hM0, hψb, hfs, hM0b, hdlog⟩ := hE.ex
  obtain ⟨Df, hDf⟩ := hdlog 1 le_rfl
  have hρs : ContDiff ℝ ∞ ρ := hρ.data.smooth
  have hlog : ContDiff ℝ ∞ (fun x => Real.log (ρ x)) := hρs.log (fun x => (hρ.pos x).ne')
  have hW : ContDiff ℝ ∞ (fun x => -Real.log (ρ x)) := hlog.neg
  set ℓ : Euc d → Euc d := fun x => gradient (fun y => Real.log (ρ y)) x with hℓ
  have hfdW : fderiv ℝ (fun y => -Real.log (ρ y)) = fun x => -(InnerProductSpace.toDual ℝ (Euc d)) (ℓ x) := by
    funext x
    rw [fderiv_fun_neg]
    simp [hℓ, gradient]
  have hℓd : Differentiable ℝ ℓ := (hfs.differentiable (by simp))
  refine ⟨max Df 0, le_max_right _ _, hW, fun x => ?_, fun x v => ?_⟩
  · have hd : HasFDerivAt ρ (fderiv ℝ ρ x) x := ((hρs.differentiable (by simp)) x).hasFDerivAt
    have h1 := (hd.log (hρ.pos x).ne').fderiv
    have h2 : fderiv ℝ (fun y => -Real.log (ρ y)) x = -((ρ x)⁻¹ • fderiv ℝ ρ x) := by
      rw [fderiv_fun_neg, h1]
    rw [h2, smul_neg, neg_smul, neg_neg, smul_smul, mul_inv_cancel₀ (hρ.pos x).ne', one_smul]
  · have hd2 : HasFDerivAt (fderiv ℝ (fun y => -Real.log (ρ y)))
        (-((InnerProductSpace.toDual ℝ (Euc d)).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (fderiv ℝ ℓ x))) x := by
      rw [hfdW]
      exact ((InnerProductSpace.toDual ℝ (Euc d)).toContinuousLinearEquiv.hasFDerivAt.comp x
        (hℓd x).hasFDerivAt).neg
    rw [hd2.fderiv]
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_comp', Function.comp_apply]
    have h3 : ‖fderiv ℝ ℓ x‖ ≤ Df := by
      have := hDf x
      rwa [norm_iteratedFDeriv_one] at this
    have h4 : inner ℝ (fderiv ℝ ℓ x v) v ≤ ‖fderiv ℝ ℓ x‖ * ‖v‖ ^ 2 := by
      calc _ ≤ ‖fderiv ℝ ℓ x v‖ * ‖v‖ := real_inner_le_norm _ _
        _ ≤ ‖fderiv ℝ ℓ x‖ * ‖v‖ * ‖v‖ := by
          gcongr; exact (fderiv ℝ ℓ x).le_opNorm v
        _ = _ := by ring
    have h5 : ‖fderiv ℝ ℓ x‖ * ‖v‖ ^ 2 ≤ max Df 0 * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (h3.trans (le_max_left _ _)) (sq_nonneg _)
    show -(max Df 0 * ‖v‖ ^ 2) ≤ -(InnerProductSpace.toDual ℝ (Euc d) (fderiv ℝ ℓ x v)) v
    rw [InnerProductSpace.toDual_apply_apply]
    linarith

end HRS.MS.Spec
