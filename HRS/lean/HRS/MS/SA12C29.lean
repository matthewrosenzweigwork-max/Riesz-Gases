import HRS.MS.SA12C28
import HRS.MS.SA12X3C6

/-!
# S.A.12(c), packet E7.05 (part 1): helper facts

* the zero drift / identity flow data for `near_local_regimes`,
* `advCutoff χ id τ z x = χ (x - z)`,
* `perNonlocal` is `L`-periodic, `eucNonlocal(χ̂_c μ)` is smooth,
* `∫ χ² > 0`.
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

theorem sa12c_advCutoff_id (χ : Euc d → ℝ) (τ : ℝ) (z x : Euc d) :
    advCutoff χ (fun _ x => x) τ z x = χ (x - z) := by
  unfold advCutoff
  have : Function.invFun (fun x : Euc d => x) x = x := by
    have := Function.invFun_eq (f := fun x : Euc d => x) (b := x) ⟨x, rfl⟩
    simpa using this
  rw [this]

theorem sa12c_drift_zero (m : ℕ) : IsAdvectingDrift m 1 1 (fun (_ : ℝ) (_ : Euc d) => (0 : Euc d)) where
  cont := continuousOn_const
  smooth := fun _ _ => contDiff_const
  deriv_bdd := fun _ _ j hj _ x => by
    rw [iteratedFDeriv_const_of_ne (by omega)]
    simp
  growth := fun _ _ x => by simp; positivity

theorem sa12c_flow_id : HRS.Whole.IsNegDriftFlow 1 (fun (_ : ℝ) (_ : Euc d) => (0 : Euc d)) (fun _ x => x) where
  init := fun x => rfl
  ode := fun x τ _ => by simpa using hasDerivWithinAt_const τ (Set.Icc (0 : ℝ) 1) x
  bij := fun τ _ => Function.bijective_id

theorem sa12c_perNonlocal_periodic {L : ℝ} {γ : Euc d → ℝ}
    (hγ : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x)
    (M : Matrix (Fin d) (Fin d) ℝ) (μ F : Euc d → ℝ) (x : Euc d) (k : Fin d → ℤ) :
    perNonlocal L γ M μ F (x + L • latticePt k) = perNonlocal L γ M μ F x := by
  have hconv : ∀ (h : Euc d → ℝ), perConv L γ h (x + L • latticePt k) = perConv L γ h x := by
    intro h
    unfold perConv
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    have := hγ (x - y) k
    rw [show x + L • latticePt k - y = x - y + L • latticePt k by abel, this]
  unfold perNonlocal
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hfun : perConv L γ (fun y => μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) =
      fun x' => perConv L γ (fun y => μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) x' := rfl
  have hper : ∀ (x' : Euc d) (k' : Fin d → ℤ),
      perConv L γ (fun y => μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) (x' + L • latticePt k') =
        perConv L γ (fun y => μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) x' := fun x' k' => by
    have := hconv (fun y => μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))
    unfold perConv
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    have := hγ (x' - y) k'
    rw [show x' + L • latticePt k' - y = x' - y + L • latticePt k' by abel, this]
  exact sa12v_fderiv_periodic L hper _ x k

theorem sa12c_chi_sq_pos {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) (hd : 1 ≤ d) :
    0 < ∫ x, χ x ^ 2 := by
  have hc : Continuous fun x : Euc d => χ x ^ 2 := hχ.1.1.continuous.pow 2
  have hint : Integrable (fun x : Euc d => χ x ^ 2) volume := by
    refine hc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) 2) fun v hv => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hv
    have : χ v = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := hχ.1.2.2.1 hmem
      rw [Metric.mem_ball, dist_zero_right] at this
      linarith
    simp [this]
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hpos : 0 < ∫ x, χ x ^ 2 := by
    refine (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _) hint).2 ?_
    have hsub : Metric.closedBall (0 : Euc d) 1 ⊆ Function.support fun x : Euc d => χ x ^ 2 := by
      intro x hx
      have := hχ.1.2.2.2.2 x hx
      simp [Function.mem_support, this]
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    exact Metric.measure_closedBall_pos _ _ one_pos
  exact hpos

end HRS.MH.AdjointRd.Phase2SA12C
