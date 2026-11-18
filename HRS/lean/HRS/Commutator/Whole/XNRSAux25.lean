import HRS.Commutator.Whole.XNRSAux24

/-!
# Packet X-NRS, part 25: `L¹` bounds for convolutions
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xconv_int {f g : Euc d → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun p : Euc d × Euc d => f p.2 * g (p.1 - p.2)) (volume.prod volume) := by
  simpa using hf.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hg

lemma xL1_conv {f g : Euc d → ℝ} (hf : Integrable f) (hg : Integrable g) :
    ∫ x, |∫ y, f y * g (x - y)| ≤ (∫ y, |f y|) * ∫ y, |g y| := by
  have P : Integrable (fun p : Euc d × Euc d => |f p.2| * |g (p.1 - p.2)|) (volume.prod volume) :=
    xconv_int hf.abs hg.abs
  have P1 : Integrable (fun x : Euc d => ∫ y, |f y| * |g (x - y)|) := P.integral_prod_left
  calc ∫ x, |∫ y, f y * g (x - y)|
      ≤ ∫ x, ∫ y, |f y| * |g (x - y)| := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) P1
          (Eventually.of_forall fun x => ?_)
        refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp [abs_mul]
    _ = ∫ y, ∫ x, |f y| * |g (x - y)| := integral_integral_swap (f := fun x y => |f y| * |g (x - y)|) P
    _ = (∫ y, |f y|) * ∫ y, |g y| := by
        have : ∀ y : Euc d, ∫ x, |f y| * |g (x - y)| = |f y| * ∫ x, |g x| := by
          intro y
          rw [integral_const_mul, integral_sub_right_eq_self (fun x => |g x|) y]
        simp_rw [this]
        rw [integral_mul_const]

/-- `‖f * Θ - (∫Θ) f‖₁ ≤ ∫ |Θ(w)| τ(w)`, where `τ(w) ≥ ‖f(· - w) - f‖₁`. -/
lemma xmollify_L1 {f Θ : Euc d → ℝ} (hf : Integrable f) (hfc : Continuous f) {M : ℝ}
    (hfb : ∀ x, |f x| ≤ M) (hΘ : Integrable Θ) (hΘc : Continuous Θ) (τ : Euc d → ℝ)
    (hτ : ∀ w, ∫ x, |f (x - w) - f x| ≤ τ w) (hτi : Integrable (fun w => |Θ w| * τ w)) :
    ∫ x, |(∫ w, f (x - w) * Θ w) - (∫ w, Θ w) * f x| ≤ ∫ w, |Θ w| * τ w := by
  have hint1 : ∀ x : Euc d, Integrable (fun w => f (x - w) * Θ w) := by
    intro x
    exact hΘ.bdd_mul (f := fun w => f (x - w)) (c := M)
      (hfc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun w => by simpa using hfb (x - w))
  have hint2 : ∀ x : Euc d, Integrable (fun w => f x * Θ w) := fun x => hΘ.const_mul _
  have hkey : ∀ x : Euc d, |(∫ w, f (x - w) * Θ w) - (∫ w, Θ w) * f x| ≤
      ∫ w, |f (x - w) - f x| * |Θ w| := by
    intro x
    have e : (∫ w, f (x - w) * Θ w) - (∫ w, Θ w) * f x = ∫ w, (f (x - w) - f x) * Θ w := by
      rw [show (∫ w, Θ w) * f x = ∫ w, f x * Θ w by rw [integral_const_mul]; ring,
        ← integral_sub (hint1 x) (hint2 x)]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      simp only; ring
    rw [e]
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp [abs_mul]
  have P : Integrable (fun p : Euc d × Euc d => |f (p.1 - p.2) - f p.1| * |Θ p.2|)
      (volume.prod volume) := by
    have h1 : Integrable (fun p : Euc d × Euc d => |Θ p.2| * |f (p.1 - p.2)|) (volume.prod volume) :=
      xconv_int hΘ.abs hf.abs
    have h2 : Integrable (fun p : Euc d × Euc d => |f p.1| * |Θ p.2|) (volume.prod volume) :=
      Integrable.mul_prod (f := fun x => |f x|) (g := fun w => |Θ w|) hf.abs hΘ.abs
    refine (h1.add h2).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have : Continuous (fun p : Euc d × Euc d => |f (p.1 - p.2) - f p.1| * |Θ p.2|) := by
        fun_prop
      exact this.aestronglyMeasurable
    · simp only [Real.norm_eq_abs]
      rw [abs_mul, abs_abs, abs_abs]
      calc |f (p.1 - p.2) - f p.1| * |Θ p.2|
          ≤ (|f (p.1 - p.2)| + |f p.1|) * |Θ p.2| := by
            gcongr; exact abs_sub _ _
        _ = _ := by simp only [Pi.add_apply]; ring
  have P1 : Integrable (fun x : Euc d => ∫ w, |f (x - w) - f x| * |Θ w|) := P.integral_prod_left
  calc ∫ x, |(∫ w, f (x - w) * Θ w) - (∫ w, Θ w) * f x|
      ≤ ∫ x, ∫ w, |f (x - w) - f x| * |Θ w| :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) P1
          (Eventually.of_forall hkey)
    _ = ∫ w, ∫ x, |f (x - w) - f x| * |Θ w| :=
        integral_integral_swap (f := fun x w => |f (x - w) - f x| * |Θ w|) P
    _ ≤ ∫ w, |Θ w| * τ w := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun w => ?_) hτi
          (Eventually.of_forall fun w => ?_)
        · exact integral_nonneg fun x => by positivity
        · dsimp only
          rw [integral_mul_const, mul_comm]
          exact mul_le_mul_of_nonneg_left (hτ w) (abs_nonneg _)

end HRS.Commutator.Whole.XNRS
