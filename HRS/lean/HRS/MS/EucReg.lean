import HRS.MS.EucRegAux3

/-!
# C-REG-e: regularity of the thermal density in the easy regime `0 < s < d - 1`

`euc_thermal_regularity_easy` has exactly the hypotheses and conclusion of the frozen
`HRS.Whole.euc_thermal_regularity` (`HRS/Whole/Static.lean`) plus `hs1 : s < d - 1`.  No tie to the frozen statement
is made (the frozen statement is stronger: it also covers `d - 1 ≤ s < d`, which needs a Hölder gain).

Route.  `ρ = thermalDensity` solves `ρ = exp(-β(a‖x‖²/2 + U))/Z` pointwise with `U = ∫ ‖x-y‖^{-s} ρ(y) dy = g * μ_β`
(`rege_data`), and `ρ ≤ C₀ e^{-βa‖x‖²/2}` (`cb_thermal_two_sided`).  Since `∇g = -s κ_s ∈ L¹_loc` exactly when `s + 1 < d`,
`U ∈ C¹` (`rege_potential`) and the bootstrap `rege_bootstrap` gives `U ∈ C^∞` with bounded derivatives of positive order;
the order-zero bound is `rege_U_bound`.  Faà di Bruno for `exp ∘ φ` (`rege_rho_deriv`) yields
`‖D^k ρ‖ ≤ C_k (1+‖x‖)^k e^{-βa‖x‖²/2}`, and the integrability conjuncts follow from this envelope.

No statement was adjusted.  Namespace `HRS.MS.Thm`, helper prefix `rege_`.
-/

open MeasureTheory Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace HRS.MS.Thm

open HRS HRS.Whole HRS.MS.LogReg

/-- **C-REG-e.**  `euc_thermal_regularity` for `0 < s < d - 1`. -/
theorem euc_thermal_regularity_easy {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    (hs1 : s < (d : ℝ) - 1) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) :
    ContDiff ℝ ∞ (thermalDensity d s a β) ∧
    ContDiff ℝ ∞ (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) ∧
    (∀ k : ℕ, ∃ C : ℝ, ∀ x,
      ‖iteratedFDeriv ℝ k (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x‖ ≤ C) ∧
    (∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k (thermalDensity d s a β) x‖ ≤
      C * (1 + ‖x‖) ^ k * Real.exp (-β * a * ‖x‖ ^ 2 / 2)) ∧
    (∀ k : ℕ, Integrable (fun x => ‖iteratedFDeriv ℝ k (thermalDensity d s a β) x‖) ∧
      ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k (thermalDensity d s a β) x‖ ≤ C) ∧
    ∀ (k : ℕ) (p : ℝ), 0 ≤ p →
      Integrable (fun x => ‖x‖ ^ p * ‖iteratedFDeriv ℝ k (thermalDensity d s a β) x‖) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Z, C0, hZ, hC0, hρ0, hρm, heq, hup, hU⟩ := rege_data hd hs0 hsd ha hβ
  set ρ := thermalDensity d s a β with hρdef
  -- the exponent `θ`
  obtain ⟨θ, hθ0, hθ1, hθd⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ s + 1 + θ < d := by
    refine ⟨min 1 (((d : ℝ) - s - 1) / 2), lt_min one_pos (by linarith), min_le_left _ _, ?_⟩
    have := min_le_right (1 : ℝ) (((d : ℝ) - s - 1) / 2)
    linarith
  have hb2 : 0 < β * a / 2 := by positivity
  have boot := rege_bootstrap hd1 hs0 hθ0 hθ1 hθd ha hβ hZ hρm heq hup
  have hfun : HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) = rege_U s ρ := funext hU
  have hρn : ∀ n : ℕ, ContDiff ℝ n ρ ∧ ∀ j ≤ n, ∃ K : ℝ, 0 ≤ K ∧ ∀ x,
      ‖iteratedFDeriv ℝ j ρ x‖ ≤ K * (1 + ‖x‖) ^ j * Real.exp (-β * a * ‖x‖ ^ 2 / 2) := by
    intro n
    obtain ⟨hUn, M, hM0, hM⟩ := boot n
    obtain ⟨C, hC, hD⟩ := rege_exponent_bound a β hUn hM0 hM
    have hφ : ContDiff ℝ n (fun x : Euc d => -β * (a * ‖x‖ ^ 2 / 2 + rege_U s ρ x)) :=
      contDiff_const.mul (((contDiff_const.mul (contDiff_norm_sq ℝ)).div_const 2).add hUn)
    exact rege_rho_deriv hZ heq hup hφ hC hD
  have hρinf : ContDiff ℝ ∞ ρ := contDiff_infty.2 fun n => (hρn n).1
  -- Gaussian envelope for every `k`
  have henv : ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖iteratedFDeriv ℝ k ρ x‖ ≤
      K * (1 + ‖x‖) ^ k * Real.exp (-(β * a / 2) * ‖x‖ ^ 2) := by
    intro k
    obtain ⟨K, hK, hKb⟩ := (hρn k).2 k le_rfl
    exact ⟨K, hK, fun x => by rw [← rege_exp_form]; exact hKb x⟩
  rw [hfun]
  refine ⟨hρinf, contDiff_infty.2 fun k => (boot k).1, fun k => ?_, fun k => ?_, fun k => ?_,
    fun k p hp => ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · obtain ⟨Cb, hCb, h0⟩ := lreg_bound_of_rdec
        (rege_rdec_of_gauss (j := 0) hb2 (K := max C0 0) (le_max_right _ _) (fun x => by
          rw [Real.norm_of_nonneg (hρ0 x), pow_zero, mul_one, ← rege_exp_form]
          exact (hup x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)))
        0
      refine ⟨Cb * lreg_A d s, fun x => ?_⟩
      rw [norm_iteratedFDeriv_zero]
      exact rege_U_bound hd1 hs0 hsd hρm.aestronglyMeasurable hCb (fun y => by simpa using h0 y) x
    · obtain ⟨_, M, _, hM⟩ := boot k
      exact ⟨M, fun x => hM k hk le_rfl x⟩
  · obtain ⟨K, hK, hKb⟩ := (hρn k).2 k le_rfl
    exact ⟨K, hKb⟩
  · obtain ⟨K, hK, hKb⟩ := henv k
    have hcont : Continuous (iteratedFDeriv ℝ k ρ) := (hρn k).1.continuous_iteratedFDeriv le_rfl
    refine ⟨?_, ?_⟩
    · have := rege_weighted_integrable hb2 (G := iteratedFDeriv ℝ k ρ) (j := k) (K := K)
        hcont.aestronglyMeasurable hKb 0 le_rfl
      simpa using this
    · obtain ⟨C, hC, hCb⟩ := rege_poly_gauss_bdd hb2 k
      refine ⟨K * C, fun x => ?_⟩
      calc ‖iteratedFDeriv ℝ k ρ x‖ ≤ K * (1 + ‖x‖) ^ k * Real.exp (-(β * a / 2) * ‖x‖ ^ 2) := hKb x
        _ = K * ((1 + ‖x‖) ^ k * Real.exp (-(β * a / 2) * ‖x‖ ^ 2)) := by ring
        _ ≤ K * C := mul_le_mul_of_nonneg_left (hCb _ (norm_nonneg x)) hK
  · obtain ⟨K, hK, hKb⟩ := henv k
    have hcont : Continuous (iteratedFDeriv ℝ k ρ) := (hρn k).1.continuous_iteratedFDeriv le_rfl
    exact rege_weighted_integrable hb2 (G := iteratedFDeriv ℝ k ρ) (j := k) (K := K)
      hcont.aestronglyMeasurable hKb p hp

end HRS.MS.Thm

end
