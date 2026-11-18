import HRS.MS.SA12C19

/-!
# S.A.12(c), packet E7.04 (part 4): derivatives of a convolution with a smooth compactly supported kernel

`T(x) = ∫ f(t) A(x - t) dt` with `f` locally integrable, `A ∈ C_c^∞`: `T ∈ C^∞` and
`∂^β T(x) = ∫ f(t) ∂^β A(x - t) dt` for every ordered multi-index `β`.
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

/-- `T = f ⋆ A`. -/
def sa12cConv (f A : Euc d → ℝ) (x : Euc d) : ℝ := ∫ t, f t * A (x - t)

theorem sa12cConv_eq (f A : Euc d → ℝ) :
    sa12cConv f A = MeasureTheory.convolution f A (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext x
  simp [sa12cConv, MeasureTheory.convolution_def]

theorem sa12c_conv_contDiff {f A : Euc d → ℝ} (hf : LocallyIntegrable f volume) (hA : ContDiff ℝ ∞ A)
    (hAc : HasCompactSupport A) : ContDiff ℝ ∞ (sa12cConv f A) := by
  rw [sa12cConv_eq]
  exact hAc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hA

theorem sa12c_conv_fderiv {f A : Euc d → ℝ} (hf : LocallyIntegrable f volume) (hA : ContDiff ℝ ∞ A)
    (hAc : HasCompactSupport A) (x v : Euc d) :
    fderiv ℝ (sa12cConv f A) x v = ∫ t, f t * fderiv ℝ A (x - t) v := by
  have hA1 : ContDiff ℝ 1 A := hA.of_le (by exact_mod_cast le_top)
  have h := hAc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hA1 x
  rw [sa12cConv_eq, h.fderiv,
    MeasureTheory.convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf (hAc.fderiv ℝ)
      (hA1.continuous_fderiv one_ne_zero)]
  simp [MeasureTheory.convolution_def]

theorem sa12c_pd_compact {A : Euc d → ℝ} (hAc : HasCompactSupport A) {n : ℕ} (β : Fin n → Fin d) :
    HasCompactSupport (partialDeriv β A) := by
  have h := (hAc.iteratedFDeriv (𝕜 := ℝ) n).comp_left
    (g := fun T : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euc d) ℝ =>
      T (fun l => (EuclideanSpace.single (β l) (1 : ℝ) : Euc d))) (by simp)
  exact h

theorem sa12c_conv_pd {f A : Euc d → ℝ} (hf : LocallyIntegrable f volume) (hA : ContDiff ℝ ∞ A)
    (hAc : HasCompactSupport A) : ∀ (n : ℕ) (β : Fin n → Fin d) (x : Euc d),
    partialDeriv β (sa12cConv f A) x = ∫ t, f t * partialDeriv β A (x - t) := by
  intro n
  induction n with
  | zero =>
    intro β x
    have h0 : ∀ (g : Euc d → ℝ) (i : Fin 0 → Fin d), partialDeriv i g = g := by
      intro g i
      funext y
      unfold partialDeriv
      rw [iteratedFDeriv_zero_apply]
    rw [h0, h0]; rfl
  | succ n ih =>
    intro β x
    have hT := sa12c_conv_contDiff hf hA hAc
    have hTn : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (sa12cConv f A) := hT.of_le (by exact_mod_cast le_top)
    have hAn : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) A := hA.of_le (by exact_mod_cast le_top)
    have hβ : β = Fin.snoc (Fin.init β) (β (Fin.last n)) := (Fin.snoc_init_self β).symm
    rw [hβ, ← sa12x2_pd_snoc n _ hTn (Fin.init β) (β (Fin.last n)) x]
    have hfun : partialDeriv (Fin.init β) (sa12cConv f A) =
        sa12cConv f (partialDeriv (Fin.init β) A) := by
      funext y
      rw [ih (Fin.init β) y]; rfl
    rw [hfun]
    have hAd : ContDiff ℝ ∞ (partialDeriv (Fin.init β) A) := sa12z3_pd_contDiff_inf hA _
    rw [sa12c_conv_fderiv hf hAd (sa12c_pd_compact hAc _) x]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [sa12x2_pd_snoc n A hAn (Fin.init β) (β (Fin.last n)) (x - t)]

end HRS.MH.AdjointRd.Phase2SA12C
