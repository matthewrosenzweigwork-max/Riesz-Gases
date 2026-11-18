import HRS.MS.SA12X5D4C
import HRS.MS.SA12K7
import HRS.MS.SA12V2

/-!
# S.A.12 X5 D4D: the difference of two periodic drifts with the same potential

`torusDriftL M L γ μ₁ VL - torusDriftL M L γ μ₂ VL = M ∇γ ⊛ (μ₁ - μ₂)` (linearity of the cancellation convolution) and
`sa12k_drift_F` applied to `μ₁ - μ₂` at level `m'`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MS.ToriCoefA HRS.MS.ToriCoefB HRS.MS.ToriConv HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x5_tcbT_sub {L : ℝ} {k : Euc d → ℝ} {Kf : ℝ} (hk : tcb_Kern L k Kf) {μ₁ μ₂ : Euc d → ℝ}
    (h₁ : ContDiff ℝ 1 μ₁) (h₂ : ContDiff ℝ 1 μ₂) {B : ℝ} (hB₁ : ∀ y, ‖μ₁ y‖ ≤ B)
    (hB₁' : ∀ y, ‖fderiv ℝ μ₁ y‖ ≤ B) (hB₂ : ∀ y, ‖μ₂ y‖ ≤ B) (hB₂' : ∀ y, ‖fderiv ℝ μ₂ y‖ ≤ B)
    (x : Euc d) :
    tcb_T L k (fun y => μ₁ y - μ₂ y) x = tcb_T L k μ₁ x - tcb_T L k μ₂ x := by
  unfold tcb_T
  rw [← integral_sub (tcb_F_integrable hk μ₁ (h₁.differentiable (by norm_num)) B B hB₁ hB₁' x)
    (tcb_F_integrable hk μ₂ (h₂.differentiable (by norm_num)) B B hB₂ hB₂' x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [tcb_F]
  by_cases hz : z ∈ tcb_N d
  · simp only [Set.indicator_of_mem hz, ← smul_sub]
    congr 1; ring
  · simp only [Set.indicator_of_notMem hz, ← smul_sub]
    congr 1; ring

theorem sa12x5_conv_sub {L Kf : ℝ} (G : Euc d → Euc d) (hk : ∀ i, tcb_Kern L (fun z => G z i) Kf)
    {μ₁ μ₂ : Euc d → ℝ} (h₁ : ContDiff ℝ 1 μ₁) (h₂ : ContDiff ℝ 1 μ₂) {B : ℝ}
    (hB₁ : ∀ y, ‖μ₁ y‖ ≤ B) (hB₁' : ∀ y, ‖fderiv ℝ μ₁ y‖ ≤ B) (hB₂ : ∀ y, ‖μ₂ y‖ ≤ B)
    (hB₂' : ∀ y, ‖fderiv ℝ μ₂ y‖ ≤ B) (x : Euc d) :
    convGradConvL L G (fun y => μ₁ y - μ₂ y) x = convGradConvL L G μ₁ x - convGradConvL L G μ₂ x := by
  have h12 : ContDiff ℝ 1 (fun y => μ₁ y - μ₂ y) := h₁.sub h₂
  have hB12 : ∀ y, ‖(fun y => μ₁ y - μ₂ y) y‖ ≤ B + B := fun y =>
    (norm_sub_le _ _).trans (add_le_add (hB₁ y) (hB₂ y))
  have hB12' : ∀ y, ‖fderiv ℝ (fun y => μ₁ y - μ₂ y) y‖ ≤ B + B := fun y => by
    have e : (fun y => μ₁ y - μ₂ y) = μ₁ - μ₂ := rfl
    rw [e, fderiv_sub (h₁.differentiable (by norm_num) y) (h₂.differentiable (by norm_num) y)]
    exact (norm_sub_le _ _).trans (add_le_add (hB₁' y) (hB₂' y))
  ext i
  rw [PiLp.sub_apply, tcb_conv_coord G hk _ h12 (B + B) (B + B) hB12 hB12' x i,
    tcb_conv_coord G hk μ₁ h₁ B B hB₁ hB₁' x i, tcb_conv_coord G hk μ₂ h₂ B B hB₂ hB₂' x i]
  exact sa12x5_tcbT_sub (hk i) h₁ h₂ hB₁ hB₁' hB₂ hB₂' x

theorem sa12x5_drift_diff (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m' : ℕ) (MB : ℝ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (L : ℝ), 1 ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ M : Matrix (Fin d) (Fin d) ℝ, PDE.MatBound MB M → ∀ (μ₁ μ₂ VL : Euc d → ℝ) (B A : ℝ), 0 ≤ A →
      ContDiff ℝ ((m' + 3 : ℕ) : WithTop ℕ∞) μ₁ → ContDiff ℝ ((m' + 3 : ℕ) : WithTop ℕ∞) μ₂ →
      (∀ i ≤ 1, ∀ y, ‖iteratedFDeriv ℝ i μ₁ y‖ ≤ B) → (∀ i ≤ 1, ∀ y, ‖iteratedFDeriv ℝ i μ₂ y‖ ≤ B) →
      (∀ i ≤ m' + 3, ∀ y, ‖iteratedFDeriv ℝ i (fun x => μ₁ x - μ₂ x) y‖ ≤ A) →
      (∀ i ≤ m' + 1, ∀ x, ∫ z in tcb_Q d L, ‖iteratedFDeriv ℝ i (fun x => μ₁ x - μ₂ x) (x - z)‖ ≤ A) →
      ∀ j ≤ m' + 1, ∀ x, ‖iteratedFDeriv ℝ j (fun x => torusDriftL M L γ μ₁ VL x - torusDriftL M L γ μ₂ VL x) x‖ ≤
        P * (A + A) := by
  obtain ⟨P, hP0, hPF⟩ := sa12k_drift_F hd hs0 hsd m' MB
  obtain ⟨Kf, hKf⟩ := sa12v_kern hd hs0 hsd
  refine ⟨P, hP0, ?_⟩
  intro L hL γ hγ M hM μ₁ μ₂ VL B A hA hc₁ hc₂ hB₁ hB₂ hAj hAc j hj x
  have hμ1 : ∀ μ : Euc d → ℝ, ContDiff ℝ ((m' + 3 : ℕ) : WithTop ℕ∞) μ → ContDiff ℝ 1 μ := fun μ h =>
    h.of_le (by exact_mod_cast (by omega : 1 ≤ m' + 3))
  have hb0 : ∀ μ : Euc d → ℝ, (∀ i ≤ 1, ∀ y, ‖iteratedFDeriv ℝ i μ y‖ ≤ B) → ∀ y, ‖μ y‖ ≤ B := fun μ h y => by
    have := h 0 (by omega) y
    rwa [norm_iteratedFDeriv_zero] at this
  have hb1 : ∀ μ : Euc d → ℝ, (∀ i ≤ 1, ∀ y, ‖iteratedFDeriv ℝ i μ y‖ ≤ B) → ∀ y, ‖fderiv ℝ μ y‖ ≤ B := fun μ h y => by
    have := h 1 (by omega) y
    rwa [norm_iteratedFDeriv_one] at this
  have hfun : (fun x => torusDriftL M L γ μ₁ VL x - torusDriftL M L γ μ₂ VL x) =
      fun x => Torus.matVec M (convGradConvL L (gradient γ) (fun y => μ₁ y - μ₂ y) x) := by
    funext y
    unfold torusDriftL
    rw [sa12x5_conv_sub (gradient γ) (hKf L hL γ hγ) (hμ1 μ₁ hc₁) (hμ1 μ₂ hc₂) (hb0 μ₁ hB₁)
      (hb1 μ₁ hB₁) (hb0 μ₂ hB₂) (hb1 μ₂ hB₂) y]
    unfold Torus.matVec
    rw [map_sub]
    abel
  rw [hfun]
  exact (hPF L hL γ hγ M hM (fun y => μ₁ y - μ₂ y) A A hA hA (hc₁.sub hc₂) hAj hAc).2 j hj x

end HRS.MH.AdjointRd.Phase2SA12X5
