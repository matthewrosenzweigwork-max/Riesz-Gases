import HRS.MS.SA12X3P2B
import HRS.MS.SA12CellC8

/-!
# S.A.12 P2 (SA12X3), part C: a classical solution has Lipschitz-in-time pairings against a test function
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Assembly

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3p_lip {m : ℕ} (hm : 0 ≤ m) {Cb T t ν : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsAdvectingDrift m Cb T b) {G F : ℝ → Euc d → ℝ} (hF : IsClassicalSol m ν b G t F) (htT : t ≤ T)
    {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    ∃ K : ℝ, ∀ τ ∈ Icc (0 : ℝ) t, ∀ σ ∈ Icc (0 : ℝ) t,
      |(∫ x, F τ x * ψ x) - ∫ x, F σ x * ψ x| ≤ K * |τ - σ| := by
  obtain ⟨R0, hR0⟩ := hψ.2.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set R : ℝ := max R0 0 with hR
  have hR0' : 0 ≤ R := le_max_right _ _
  have hsupp : ∀ x : Euc d, R < ‖x‖ → ψ x = 0 := by
    intro x hx
    by_contra h
    have := hR0 (subset_tsupport ψ h)
    rw [mem_closedBall, dist_zero_right] at this
    linarith [le_max_left R0 0]
  obtain ⟨Bψ0, hBψ0⟩ := hψ.1.continuous.bounded_above_of_compact_support hψ.2
  set Bψ : ℝ := |Bψ0| with hBψ
  have hψb : ∀ x, |ψ x| ≤ Bψ := fun x => by
    have := hBψ0 x; rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self _)
  obtain ⟨KF, hKF⟩ := sa12y_jet_bound hF.contF 0 R
  obtain ⟨KD, hKD⟩ := sa12y_rate_bound hb hF htT R hR0' 0 (Nat.zero_le m)
  set K1 : ℝ := |KF| * Bψ with hK1
  set K2 : ℝ := |KD| * Bψ with hK2
  set K : ℝ := max K1 K2 with hK
  set Rr : ℝ → Euc d → ℝ := fun σ x => ν * Laplacian.laplacian (F σ) x +
    inner ℝ (b σ x) (gradient (F σ) x) + G σ x with hRr
  have hFb : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R → |F σ x| ≤ |KF| := by
    intro σ hσ x hx
    have := hKF σ hσ x hx
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  have hRb : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R → |Rr σ x| ≤ |KD| := by
    intro σ hσ x hx
    have := hKD (fun i => Fin.elim0 i) σ hσ x hx
    rw [HRS.MH.AdjointRd.Phase2SA12Near.sa12z3_pd_zero_fun] at this
    exact this.trans (le_abs_self _)
  have hpar : ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt (fun τ' => ∫ x, F τ' x * ψ x)
      (∫ x, Rr τ x * ψ x) (Icc (0 : ℝ) t) τ := by
    intro τ hτ
    refine sa12y_param_deriv (K := K) (R := R) (f := fun σ x => F σ x * ψ x) (f' := fun σ x => Rr σ x * ψ x)
      ?_ ?_ ?_ ?_ ?_ hτ
    · intro σ hσ
      exact ((hF.smooth σ hσ).1.continuous.mul hψ.1.continuous).aestronglyMeasurable
    · intro σ hσ x hx
      show F σ x * ψ x = 0
      rw [hsupp x hx, mul_zero]
    · intro σ hσ x
      show |F σ x * ψ x| ≤ K
      by_cases hx : ‖x‖ ≤ R
      · rw [abs_mul]
        exact (mul_le_mul (hFb σ hσ x hx) (hψb x) (abs_nonneg _) (abs_nonneg _)).trans (le_max_left _ _)
      · rw [hsupp x (not_le.1 hx)]
        simp only [mul_zero, abs_zero]
        exact (by positivity : 0 ≤ K1).trans (le_max_left _ _)
    · intro x σ hσ
      have h := hF.deriv_t 0 (Nat.zero_le m) (fun i => Fin.elim0 i) x σ hσ
      simp only [HRS.MH.AdjointRd.Phase2SA12Near.sa12z3_pd_zero_fun] at h
      exact h.mul_const (ψ x)
    · intro σ hσ x hx
      show |Rr σ x * ψ x| ≤ K
      rw [abs_mul]
      exact (mul_le_mul (hRb σ hσ x hx) (hψb x) (abs_nonneg _) (abs_nonneg _)).trans (le_max_right _ _)
  have hderb : ∀ τ ∈ Icc (0 : ℝ) t, ‖∫ x, Rr τ x * ψ x‖ ≤ K * (volume (closedBall (0 : Euc d) R)).toReal := by
    intro τ hτ
    rw [Real.norm_eq_abs]
    refine sa12x3n_int_le (x := 0) (R := R) (A := K) (by positivity) (fun x hx => ?_) (fun x hx => ?_)
    · show |Rr τ x * ψ x| ≤ K
      rw [abs_mul]
      have hx' : ‖x‖ ≤ R := by simpa [mem_closedBall_zero_iff] using hx
      exact (mul_le_mul (hRb τ hτ x hx') (hψb x) (abs_nonneg _) (abs_nonneg _)).trans (le_max_right _ _)
    · show Rr τ x * ψ x = 0
      rw [hsupp x (by simpa [mem_closedBall_zero_iff, not_le] using hx), mul_zero]
  refine ⟨K * (volume (closedBall (0 : Euc d) R)).toReal, fun τ hτ σ hσ => ?_⟩
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun τ' => ∫ x, F τ' x * ψ x)
    (f' := fun τ' => ∫ x, Rr τ' x * ψ x) (s := Icc (0 : ℝ) t) (C := K * (volume (closedBall (0 : Euc d) R)).toReal)
    hpar hderb (convex_Icc 0 t) hσ hτ
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  exact this

end HRS.MH.AdjointRd.Phase2SA12Assembly
