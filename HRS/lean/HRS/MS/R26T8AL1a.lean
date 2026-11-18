import HRS.Whole.Q09AAux5

/-!
# Generic helper L1a: integration by parts of a bounded smooth real function against a complex Schwartz function

For `u : ℝⁿ → ℝ` smooth with `u` and `∇u` bounded, and `ψ` complex Schwartz:
`∫ (∂_v u) ψ = -∫ u (∂_v ψ)`.  Used by L1 (weak derivative of `SobSmooth` functions).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff
namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_l1a_fderiv_ofReal (u : Euc d → ℝ) (x : Euc d) (hu : DifferentiableAt ℝ u x)
    (v : Euc d) :
    fderiv ℝ (fun y => ((u y : ℝ) : ℂ)) x v = ((fderiv ℝ u x v : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun y => ((u y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ u x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hu.hasFDerivAt
  rw [h1.fderiv]
  simp

theorem r26t8a_l1a_ibp (u : Euc d → ℝ) (hu : ContDiff ℝ ∞ u) (C0 C1 : ℝ)
    (hC0 : ∀ x, |u x| ≤ C0) (hC1 : ∀ x, ‖fderiv ℝ u x‖ ≤ C1)
    (ψ : SchwartzMap (Euc d) ℂ) (v : Euc d) :
    ∫ x, ((fderiv ℝ u x v : ℝ) : ℂ) * ψ x =
      -∫ x, ((u x : ℝ) : ℂ) * (LineDeriv.lineDerivOp v ψ) x := by
  have hd : ∀ x, DifferentiableAt ℝ u x := fun x => (hu.differentiable (by simp)) x
  set f : Euc d → ℂ := fun x => ((u x : ℝ) : ℂ) with hf
  have hfdiff : ∀ x, DifferentiableAt ℝ f x := fun x =>
    (Complex.ofRealCLM.differentiableAt).comp x (hd x)
  have hfd : ∀ x, fderiv ℝ f x v = ((fderiv ℝ u x v : ℝ) : ℂ) := fun x =>
    r26t8a_l1a_fderiv_ofReal u x (hd x) v
  have hbf : ∀ x, ‖f x‖ ≤ C0 := fun x => by
    simp only [hf, Complex.norm_real, Real.norm_eq_abs]
    exact hC0 x
  have hbd : ∀ x, ‖((fderiv ℝ u x v : ℝ) : ℂ)‖ ≤ C1 * ‖v‖ := fun x => by
    rw [Complex.norm_real]
    exact (ContinuousLinearMap.le_opNorm (fderiv ℝ u x) v).trans
      (mul_le_mul_of_nonneg_right (hC1 x) (norm_nonneg v))
  have hcont : Continuous f := Complex.continuous_ofReal.comp hu.continuous
  have hcontd : Continuous (fun x => ((fderiv ℝ u x v : ℝ) : ℂ)) := by
    have : Continuous (fun x => fderiv ℝ u x v) :=
      (hu.continuous_fderiv (by simp)).clm_apply continuous_const
    exact Complex.continuous_ofReal.comp this
  have hψi : Integrable (fun x => ψ x) volume := ψ.integrable
  have hψdi : Integrable (fun x => (LineDeriv.lineDerivOp v ψ) x) volume :=
    (LineDeriv.lineDerivOp v ψ).integrable
  have I1 : Integrable (fun x => ((fderiv ℝ u x v : ℝ) : ℂ) * ψ x) volume :=
    hψi.bdd_mul (hcontd.aestronglyMeasurable) (Eventually.of_forall fun x => hbd x)
  have I2 : Integrable (fun x => f x * (LineDeriv.lineDerivOp v ψ) x) volume :=
    hψdi.bdd_mul hcont.aestronglyMeasurable (Eventually.of_forall fun x => hbf x)
  have I3 : Integrable (fun x => f x * ψ x) volume :=
    hψi.bdd_mul hcont.aestronglyMeasurable (Eventually.of_forall fun x => hbf x)
  have I4 : Integrable (fun x => fderiv ℝ f x v * ψ x) volume := by
    simp only [hfd]
    exact I1
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := f)
    (g := ψ) (v := v) I4 I2 I3 (fun x _ => hfdiff x) (fun x _ => ψ.differentiableAt)
  have hdef : (∫ x, ((u x : ℝ) : ℂ) * (LineDeriv.lineDerivOp v ψ) x) =
      ∫ x, f x * fderiv ℝ ψ x v := rfl
  rw [hdef, key, neg_neg]
  simp only [hfd]

end HRS.MS.R26T8A

end
