import HRS.MS.SA16Y10Gi1
import HRS.MS.SA16Y4Fam1
import HRS.MS.SA16Y4Ip1
import HRS.MS.SA16SOp3

/-!
# S.A.16 (SA16Y10) Bd1: truncated mollification `sa16y4_tm` is linear; scaling of `SA16BddCoef`
-/

set_option autoImplicit false

noncomputable section
open scoped ContDiff
open Filter MeasureTheory

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

variable {d : ℕ}

lemma sa16y10_tm_smul (n : ℕ) (c : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    sa16y4_tm d n (fun y => c * f y) = fun x => c * sa16y4_tm d n f x := by
  funext x
  unfold sa16y4_tm
  have : ∫ y, (c * f y) * sa16y_rho d n (x - y) = c * ∫ y, f y * sa16y_rho d n (x - y) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  rw [this]; ring

lemma sa16y10_tm_sub (n : ℕ) {f g : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    sa16y4_tm d n (fun y => f y - g y) = fun x => sa16y4_tm d n f x - sa16y4_tm d n g x := by
  funext x
  unfold sa16y4_tm
  have hρc : Continuous (sa16y_rho d n) := sa16y_rho_smooth n |>.continuous
  have hint : ∀ h : EuclideanSpace ℝ (Fin d) → ℝ, Continuous h →
      Integrable (fun y => h y * sa16y_rho d n (x - y)) := fun h hc =>
    (hc.mul (hρc.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (by
        have h0 : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin d) => sa16y_rho d n (x - y)) :=
          (sa16y_rho_compact n).comp_homeomorph ((Homeomorph.subLeft x))
        exact h0.mul_left)
  have : ∫ y, (f y - g y) * sa16y_rho d n (x - y) = (∫ y, f y * sa16y_rho d n (x - y)) -
      ∫ y, g y * sa16y_rho d n (x - y) := by
    rw [← integral_sub (hint f hf) (hint g hg)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  rw [this]; ring

lemma sa16y10_BddCoef_smul {k : ℕ} {B : ℝ} {bc : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (h : SA16BddCoef k B bc)
    (c : ℝ) : SA16BddCoef k (|c| * B) (fun i x => c * bc i x) where
  nonneg := mul_nonneg (abs_nonneg c) h.nonneg
  smooth := fun i => contDiff_const.mul (h.smooth i)
  bound := fun i j hj x => by
    have hc : ContDiffAt ℝ j (fun y => bc i y) x := ((h.smooth i).of_le (by exact_mod_cast le_top)).contDiffAt
    have e : iteratedFDeriv ℝ j (fun y => c * bc i y) x = c • iteratedFDeriv ℝ j (bc i) x :=
      iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := c) (f := bc i) (x := x) (i := j) hc
    rw [e, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (h.bound i j hj x) (abs_nonneg c)

end HRS.Whole.AppendixA.Phase2SA16R

end
