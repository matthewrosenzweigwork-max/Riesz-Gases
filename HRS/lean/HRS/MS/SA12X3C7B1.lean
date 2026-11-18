import HRS.MS.SA12X3C7A

/-!
# S.A.12 C7 (SA12X3), part B1: tuple partials of a convolution with an arbitrary locally integrable kernel

`∂^idx (K ⋆ Q) = K ⋆ ∂^idx Q` for `Q ∈ C^n_c` (the proof of `sa12z3_pd_conv` with a general kernel).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}


theorem sa12x3_pd_conv_gen {K : Euc d → ℝ} (hK : LocallyIntegrable K (volume : Measure (Euc d))) :
    ∀ (n : ℕ) (Q : Euc d → ℝ), ContDiff ℝ n Q → HasCompactSupport Q → ∀ (idx : Fin n → Fin d) (x : Euc d),
      partialDeriv idx (HRS.Whole.convFun (K) Q) x =
        HRS.Whole.convFun (K) (partialDeriv idx Q) x := by
  have hfun : ∀ Q : Euc d → ℝ, HRS.Whole.convFun (K) Q =
      K ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] Q := by
    intro Q
    funext x'
    have h := integral_sub_left_eq_self (μ := volume) (fun t => K t * Q (x' - t)) x'
    simp only [sub_sub_cancel] at h
    simpa [convolution_def, HRS.Whole.convFun] using h
  have hcd : ∀ (n : ℕ) (Q : Euc d → ℝ), ContDiff ℝ n Q → HasCompactSupport Q →
      ContDiff ℝ n (HRS.Whole.convFun (K) Q) := by
    intro n Q hQ hQc
    rw [hfun]
    exact hQc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hK hQ
  intro n
  induction n with
  | zero =>
    intro Q hQ hQc idx x
    simp only [sa12z3_pd_zero_fun]
  | succ n ih =>
    intro Q hQ hQc idx x
    obtain ⟨i, idx', rfl⟩ : ∃ i idx', idx = (Fin.cons i idx' : Fin (n + 1) → Fin d) :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    have hQn : ContDiff ℝ n Q := hQ.of_le (by exact_mod_cast Nat.le_succ n)
    have e1 : partialDeriv (Fin.cons i idx' : Fin (n + 1) → Fin d) (HRS.Whole.convFun (K) Q) x =
        D1 i (partialDeriv idx' (HRS.Whole.convFun (K) Q)) x :=
      sa12z3_pd_cons idx' i (hcd (n + 1) Q hQ hQc) x
    have e2 : D1 i (partialDeriv idx' (HRS.Whole.convFun (K) Q)) =
        D1 i (HRS.Whole.convFun (K) (partialDeriv idx' Q)) :=
      congrArg (D1 i) (funext fun y => ih Q hQn hQc idx' y)
    have hPQ : ContDiff ℝ 1 (partialDeriv idx' Q) := by
      have := sa12z3_pd_contDiff (k := n + 1) (n := n) hQ (by omega) idx'
      simpa using this
    have e3 : D1 i (HRS.Whole.convFun (K) (partialDeriv idx' Q)) x =
        HRS.Whole.convFun (K) (D1 i (partialDeriv idx' Q)) x :=
      convFun_D1 hK hPQ (sa12z3_pd_compact hQc idx') i x
    have e4 : partialDeriv (Fin.cons i idx' : Fin (n + 1) → Fin d) Q x = D1 i (partialDeriv idx' Q) x :=
      sa12z3_pd_cons idx' i hQ x
    rw [e1, e2, e3]
    unfold HRS.Whole.convFun
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [sa12z3_pd_cons idx' i hQ y]


end HRS.MH.AdjointRd.Phase2SA12Near
