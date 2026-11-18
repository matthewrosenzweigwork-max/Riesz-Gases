import HRS.MH.ScreenedK3Aux2

/-! Packet K3 (`gk_weak`), auxiliary 3: integration by parts for the smooth kernel `g_ε(· - y)`. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- For `0 < ε ≤ 1`: `∫ g_ε(x-y) ∂_iφ(x) dx = -∫ ∂_i g_ε(x-y) φ(x) dx` for Schwartz `φ`. -/
lemma k3_ibp_eps (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s + 1 < d) (i : Fin d) (y : Euc d)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (φ : SchwartzMap (Euc d) ℝ) :
    ∫ x, movtr_gEps d s ε (x - y) * fderiv ℝ φ x (EuclideanSpace.single i 1) =
      -∫ x, movtr_dEps d s ε (EuclideanSpace.single i 1) (x - y) * φ x := by
  have hsd' : s < d := by linarith
  obtain ⟨hcφ, hbφ, h0φ, h1φ⟩ := k3_sch_props φ
  obtain ⟨hcD, hbD, h0D, h1D⟩ := k3_sch_deriv_props φ i
  have hdiff : ∀ x, DifferentiableAt ℝ (fun z => movtr_gEps d s ε (z - y)) x := fun x => by
    have hu : 0 < ‖x - y‖ ^ 2 + ε ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hε0 2)
    exact ((movtr_gEps_hasFDerivAt s ε (x - y) hu).differentiableAt).comp x
      ((hasFDerivAt_id x).sub_const y).differentiableAt
  have hf'g : Integrable (fun x => fderiv ℝ (fun z => movtr_gEps d s ε (z - y)) x
      (EuclideanSpace.single i 1) * φ x) := by
    simp only [k3_fderiv_gEps s ε hε0 y]
    exact k3_dEps_integrable hd hs0 hsd hε0.le (EuclideanSpace.single i 1)
      (movtr_norm_single i) y hcφ hbφ h0φ
  have hfg' : Integrable (fun x => movtr_gEps d s ε (x - y) * fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    k3_gEps_integrable hd hs0 hsd' hε0.le hε1 y hcD hbD h0D h1D
  have hfg : Integrable (fun x => movtr_gEps d s ε (x - y) * φ x) :=
    k3_gEps_integrable hd hs0 hsd' hε0.le hε1 y hcφ hbφ h0φ h1φ
  have IBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg
    (fun x _ => hdiff x) (fun x _ => φ.differentiableAt)
  rw [IBP]
  simp only [k3_fderiv_gEps s ε hε0 y]

end HRS.MH.Screened
