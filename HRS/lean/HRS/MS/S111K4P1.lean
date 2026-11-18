import HRS.MS.S111X2Aux12
import HRS.MD.DOMCalc

/-!
# S11.1 / T03 (S11K4), packet `R26-T6C.P04`: weighted integration by parts with a product of two responses
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole
open HRS.MS.TcR (tc2_integrable_nu tc2_integral_nu)
open HRS.MS.S111X2

variable {d : ℕ}

theorem k4_cb1_of_cb2 {h : Euc d → ℝ} (H : MemCb 2 h) : MemCb 1 h :=
  ⟨H.1.of_le (by norm_num), fun j hj => H.2 j (hj.trans (by norm_num))⟩

/-- Pro `R26-T6C.P04`: `∫ (L f) h k dμ = ∫ ⟨∇f,∇h⟩ k + ⟨∇f,∇k⟩ h dμ`. -/
theorem k4_weighted_triple_ibp (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ) (f h k : Euc d → ℝ)
    (hf : MemCb 2 f) (hh : MemCb 2 h) (hk : MemCb 2 k) :
    (∫ x, s111x2_L ρ f x * h x * k x ∂(HRS.Whole.withDensityReal ρ)) =
      ∫ x, (inner ℝ (gradient f x) (gradient h x) * k x + inner ℝ (gradient f x) (gradient k x) * h x)
        ∂(HRS.Whole.withDensityReal ρ) := by
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  obtain ⟨B1f, B2f, Hf⟩ := s111x2_cbD_of_memCb2 hf
  obtain ⟨hhc, B0h, B1h, h0h, h1h⟩ := s111x2_cb1_bounds (k4_cb1_of_cb2 hh)
  obtain ⟨hkc, B0k, B1k, h0k, h1k⟩ := s111x2_cb1_bounds (k4_cb1_of_cb2 hk)
  set u : Euc d → ℝ := fun x => h x * k x with hu
  have hhd : Differentiable ℝ h := hhc.differentiable (by norm_num)
  have hkd : Differentiable ℝ k := hkc.differentiable (by norm_num)
  have huc : ContDiff ℝ 1 u := hhc.mul hkc
  have hfd : ∀ x, fderiv ℝ u x = h x • fderiv ℝ k x + k x • fderiv ℝ h x := fun x =>
    (hhd.differentiableAt.hasFDerivAt.mul hkd.differentiableAt.hasFDerivAt).fderiv
  have h0u : ∀ x, ‖u x‖ ≤ B0h * B0k := fun x => by
    simp only [hu, norm_mul]
    exact mul_le_mul (h0h x) (h0k x) (norm_nonneg _) ((norm_nonneg _).trans (h0h x))
  have h1u : ∀ x, ‖fderiv ℝ u x‖ ≤ B0h * B1k + B0k * B1h := fun x => by
    rw [hfd]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul]
      exact mul_le_mul (h0h x) (h1k x) (norm_nonneg _) ((norm_nonneg _).trans (h0h x))
    · rw [norm_smul]
      exact mul_le_mul (h0k x) (h1h x) (norm_nonneg _) ((norm_nonneg _).trans (h0k x))
  have hibp := s111x2_ibp_bilinear (u := u) T.en.smooth T.en.K.int (s111x2_grad_integrable T.en) huc Hf.smooth
    h0u h1u Hf.d1 Hf.d2
  have hgu : ∀ x, gradient u x = h x • gradient k x + k x • gradient h x := fun x =>
    HRS.MD.DOMProof.domp_gradient_mul hhd.differentiableAt hkd.differentiableAt
  have hL : ∫ x, s111x2_L ρ f x * h x * k x ∂(HRS.Whole.withDensityReal ρ) = ∫ x, ρ x * inner ℝ (gradient u x) (gradient f x) := by
    rw [tc2_integral_nu T.prob]
    have : ∀ x, ρ x * (s111x2_L ρ f x * h x * k x) =
        -(u x * (ρ x * Laplacian.laplacian f x + inner ℝ (gradient ρ x) (gradient f x))) := by
      intro x
      have := s111x2_rhoL T f x
      simp only [hu]
      calc ρ x * (s111x2_L ρ f x * h x * k x) = (ρ x * s111x2_L ρ f x) * (h x * k x) := by ring
        _ = _ := by rw [this]; ring
    simp_rw [this, integral_neg, hibp, neg_neg]
  rw [hL, tc2_integral_nu T.prob]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hgu, inner_add_left, inner_smul_left, conj_trivial, real_inner_comm]
  ring

end HRS.MS.S111K4
