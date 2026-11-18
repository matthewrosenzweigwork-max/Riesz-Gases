import HRS.MS.SA12K13

/-!
# S.A.12 C1, drift data of a periodic density and potential

`ContDiff (m+1)`, the derivative bounds and the linear growth (everywhere) of
`torusDriftL M L γ μ VL = M ∇γ ⊛ μ - ∇VL`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MS.ToriCoefA HRS.MS.ToriCoefB HRS.MS.ToriConv

variable {d : ℕ}

/-- Linear growth of `∇ V_L` everywhere. -/
theorem sa12k_gradVL_growth {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (L : ℝ) (hL : 1 ≤ L)
    (V : Euc d → ℝ) (hV1 : ContDiff ℝ ∞ V) (ΛV G₀ : ℝ) (hΛ0 : 0 ≤ ΛV) (hG0 : 0 ≤ G₀)
    (hV2 : ∀ x : Euc d, ‖iteratedFDeriv ℝ 2 V x‖ ≤ ΛV) (hV3 : ‖gradient V 0‖ ≤ G₀) (hV0 : V 0 = 0)
    (Kz : ℕ → ℝ) (hKz : ∀ (i : ℕ) (y : Euc d), ‖iteratedFDeriv ℝ i ζ y‖ ≤ Kz i)
    (hKz0 : ∀ i, 0 ≤ Kz i) (MV : ℝ) (hM : G₀ + ΛV ≤ MV) (x : Euc d) :
    ‖gradient (perL L fun y => ζ (L⁻¹ • y) * V y) x‖ ≤ (Kz 0 + Kz 1) * MV * (1 + ‖x‖) := by
  have hL0 : 0 < L := by linarith
  have hvan : ∀ y : Euc d, L / 3 ≤ ‖y‖ → ζ (L⁻¹ • y) * V y = 0 := fun y hy => by
    rw [tca_zeta_far_val hζ L hL0 y hy, zero_mul]
  obtain ⟨k, hk, hkn⟩ := sa12k_near L hL0 x
  have hU : x ∈ tca_U L k := by
    intro i
    have := hk i
    show |x i - L * (k i : ℝ)| < 2 * L / 3
    linarith
  rw [tcb_norm_gradient]
  rw [tca_perL_iter_norm L hL0 _ hvan k x hU 1]
  have h := tcb_VL_grad_central hζ L hL V hV1 ΛV G₀ 0 hΛ0 hG0 le_rfl hV2 hV3 (by rw [hV0]; simp) Kz hKz
    hKz0 MV (by linarith) (x - L • latticePt k)
  refine h.trans ?_
  have : 0 ≤ (Kz 0 + Kz 1) * MV := by
    have hMV : 0 ≤ MV := by linarith
    exact mul_nonneg (add_nonneg (hKz0 0) (hKz0 1)) hMV
  exact mul_le_mul_of_nonneg_left (by linarith) this

/-- Regularity, derivative bounds and growth of the periodic drift. -/
theorem sa12k_drift_data {m : ℕ} {L : ℝ} {γ : Euc d → ℝ} {M : Matrix (Fin d) (Fin d) ℝ}
    {μ VL : Euc d → ℝ} {Q ΛA CV : ℝ} (hCV : 0 ≤ CV)
    (hFcd : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞)
      (fun x => Torus.matVec M (convGradConvL L (gradient γ) μ x)))
    (hFb : ∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j
      (fun x => Torus.matVec M (convGradConvL L (gradient γ) μ x)) x‖ ≤ Q)
    (hVcd : ContDiff ℝ ∞ VL)
    (hVbd : ∀ j : ℕ, 2 ≤ j → j ≤ m + 3 → ∀ x, ‖iteratedFDeriv ℝ j VL x‖ ≤ ΛA)
    (hVg : ∀ x, ‖gradient VL x‖ ≤ CV * (1 + ‖x‖)) :
    ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (torusDriftL M L γ μ VL) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ j (torusDriftL M L γ μ VL) x‖ ≤ Q + |ΛA|) ∧
    (∀ x, ‖torusDriftL M L γ μ VL x‖ ≤ (Q + CV) * (1 + ‖x‖)) := by
  have hgrad_cd : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (gradient VL) := tcb_grad_contDiff VL m hVcd
  have hdrift : torusDriftL M L γ μ VL =
      fun x => Torus.matVec M (convGradConvL L (gradient γ) μ x) - gradient VL x := rfl
  rw [hdrift]
  have hQ : 0 ≤ Q := (norm_nonneg _).trans (by simpa using hFb 0 (by omega) 0)
  refine ⟨hFcd.sub hgrad_cd, fun j hj1 hjm x => ?_, fun x => ?_⟩
  · have e : iteratedFDeriv ℝ j (fun x => Torus.matVec M (convGradConvL L (gradient γ) μ x) -
        gradient VL x) x =
        iteratedFDeriv ℝ j (fun x => Torus.matVec M (convGradConvL L (gradient γ) μ x)) x -
          iteratedFDeriv ℝ j (gradient VL) x :=
      iteratedFDeriv_sub_apply ((hFcd.of_le (by exact_mod_cast hjm)).contDiffAt)
        ((hgrad_cd.of_le (by exact_mod_cast hjm)).contDiffAt)
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h1 := hFb j hjm x
    have h2 : ‖iteratedFDeriv ℝ j (gradient VL) x‖ ≤ ΛA := by
      rw [tcb_grad_iter_norm]
      exact hVbd (j + 1) (by omega) (by omega) x
    have h3 : ΛA ≤ |ΛA| := le_abs_self _
    linarith
  · refine (norm_sub_le _ _).trans ?_
    have h1 : ‖Torus.matVec M (convGradConvL L (gradient γ) μ x)‖ ≤ Q := by
      have := hFb 0 (by omega) x
      rwa [norm_iteratedFDeriv_zero] at this
    have hx1 : 0 ≤ ‖x‖ := norm_nonneg x
    have h4 : Q ≤ Q * (1 + ‖x‖) := le_mul_of_one_le_right hQ (by linarith)
    have h6 : (Q + CV) * (1 + ‖x‖) = Q * (1 + ‖x‖) + CV * (1 + ‖x‖) := by ring
    rw [h6]
    linarith [hVg x]

end HRS.MH.AdjointRd.Phase2SA12Construction
