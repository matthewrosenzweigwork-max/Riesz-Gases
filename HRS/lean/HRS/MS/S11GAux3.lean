import HRS.MS.S11GAux2

/-!
# S11G: first and second derivative growth, and the Hessian contraction `Q_γ`
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S11G

open HRS ProbabilityTheory

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

/-- The Hessian contraction `Q_γ F (w) = ∫ D²F(w)[z,z] dγ(z)`. -/
def Qγ (γ : Measure B) (F : B → ℝ) (w : B) : ℝ := ∫ z, fderiv ℝ (fderiv ℝ F) w z z ∂γ

theorem s11g_fderiv2_bound {F : B → ℝ} {Mb : ℝ} (h2 : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ Mb) (w : B) :
    ‖fderiv ℝ (fderiv ℝ F) w‖ ≤ Mb := by
  have := h2 w
  rwa [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F) (n := 1), norm_iteratedFDeriv_one] at this

theorem s11g_fderiv_growth {F : B → ℝ} (hF : ContDiff ℝ 2 F) {Mb : ℝ}
    (h2 : ∀ w, ‖fderiv ℝ (fderiv ℝ F) w‖ ≤ Mb) (w : B) :
    ‖fderiv ℝ F w‖ ≤ ‖fderiv ℝ F 0‖ + Mb * ‖w‖ := by
  have hdiff : Differentiable ℝ (fderiv ℝ F) :=
    ((hF.fderiv_right (by norm_num : ((1 : ℕ) : WithTop ℕ∞) + 1 ≤ 2))).differentiable (by norm_num)
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ F) (s := Set.univ)
    (fun x _ => hdiff x) (fun x _ => h2 x) convex_univ (Set.mem_univ 0) (Set.mem_univ w)
  have h3 : ‖fderiv ℝ F w‖ ≤ ‖fderiv ℝ F 0‖ + ‖fderiv ℝ F w - fderiv ℝ F 0‖ := by
    have := norm_le_norm_add_norm_sub' (fderiv ℝ F w) (fderiv ℝ F 0)
    linarith
  rw [sub_zero] at this
  linarith

theorem s11g_value_growth {F : B → ℝ} (hF : ContDiff ℝ 2 F) {Mb : ℝ}
    (h2 : ∀ w, ‖fderiv ℝ (fderiv ℝ F) w‖ ≤ Mb) (w : B) :
    ‖F w‖ ≤ ‖F 0‖ + (‖fderiv ℝ F 0‖ + Mb * ‖w‖) * ‖w‖ := by
  have hMb : 0 ≤ Mb := (norm_nonneg (fderiv ℝ (fderiv ℝ F) 0)).trans (h2 0)
  have hd1 : Differentiable ℝ F := hF.differentiable (by norm_num)
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := F) (s := Metric.closedBall (0 : B) ‖w‖) (x := 0) (y := w)
    (C := ‖fderiv ℝ F 0‖ + Mb * ‖w‖) (fun x _ => hd1 x)
    (fun x hx => by
      have hx' : ‖x‖ ≤ ‖w‖ := by simpa using hx
      have := s11g_fderiv_growth hF h2 x
      nlinarith [mul_le_mul_of_nonneg_left hx' hMb])
    (convex_closedBall _ _) (Metric.mem_closedBall_self (norm_nonneg w)) (by simp)
  have h3 : ‖F w‖ ≤ ‖F 0‖ + ‖F w - F 0‖ := by
    have := norm_le_norm_add_norm_sub' (F w) (F 0)
    linarith
  simp only [sub_zero] at this
  linarith

end HRS.MS.S11G
