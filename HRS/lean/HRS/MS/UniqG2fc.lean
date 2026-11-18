import HRS.MS.UniqG2eB
import HRS.MS.UniqG2fa
import HRS.MS.UniqG2fb
import HRS.MS.UniqN4bJ

/-!
# G2fc: Gronwall closing for the regime `R3`

`g2fc_neigh_real`: real-integral form of `g2fb_neighbours` for `G = |∇f|²`.
`g2f_decay`: the `R3` analogue of `g2e_decay`: `∫ ς_c^τ z_ε² ≤ C0 ε`.  The nonlocal term is estimated
by `n4b_r3_core` with `δ = ν₀ / (8 (N+1))`, the local gradient mass is bounded by the dissipations of
the `N` neighbouring cells (`g2fb_neighbours`), and `g2b_closing_gronwall` absorbs them
(`δ' N ≤ ν/2`, `δ' = 2δ`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal Interval ContDiff

namespace HRS.MS.UniqG2fc

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqT3
  HRS.MS.UniqE1 HRS.MS.UniqC3 HRS.MS.UniqE2 HRS.MS.UniqE3 HRS.MS.UniqE4 HRS.MS.UniqG2a
  HRS.MS.UniqNDefs HRS.MS.UniqG2e

variable {d : ℕ}

/-- Real-integral form of the neighbour estimate, for `G = |∇f|²`. -/
theorem g2fc_neigh_real {m : ℕ} {Cb t : ℝ} {χ χh : Euc d → ℝ} {b : ℝ → Euc d → Euc d}
    {Ψ : ℝ → Euc d → Euc d} {K : ℝ} (hF : FlowBundle d m Cb t χ χh b Ψ K)
    {S : Euc d → Finset (Euc d)}
    (hS : ∀ σ ∈ Set.Icc (0:ℝ) t, ∀ c : Euc d, ∀ G : Euc d → ℝ≥0∞, Measurable G →
        ∫⁻ x in closedBall (Ψ σ c) (8 * Real.exp (Cb * t)), G x ≤
          ∑ c' ∈ S c, ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ σ c' x) * G x)
    {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {σ : ℝ} (hσ : σ ∈ Set.Icc (0:ℝ) t) (c : Euc d) :
    ∫ y in closedBall (Ψ σ c) (8 * Real.exp (Cb * t)), ‖fderiv ℝ f y‖ ^ 2 ≤
      ∑ c' ∈ S c, ∫ x, varsigma χ Ψ σ c' x * ‖fderiv ℝ f x‖ ^ 2 := by
  have hcont : Continuous (fun x => ‖fderiv ℝ f x‖ ^ 2) :=
    ((hf.continuous_fderiv (by simp)).norm).pow 2
  have h := hS σ hσ c (fun x => ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2))
    hcont.measurable.ennreal_ofReal
  have hL : ∫⁻ x in closedBall (Ψ σ c) (8 * Real.exp (Cb * t)), ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) =
      ENNReal.ofReal (∫ y in closedBall (Ψ σ c) (8 * Real.exp (Cb * t)), ‖fderiv ℝ f y‖ ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal
      (hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
      (Eventually.of_forall fun x => sq_nonneg _)).symm
  have hR : ∀ c' : Euc d, ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ σ c' x) *
      ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) =
      ENNReal.ofReal (∫ x, varsigma χ Ψ σ c' x * ‖fderiv ℝ f x‖ ^ 2) := fun c' => by
    have hint : Integrable (fun x => varsigma χ Ψ σ c' x * ‖fderiv ℝ f x‖ ^ 2) volume :=
      ((hF.contDiff σ hσ c').continuous.mul hcont).integrable_of_hasCompactSupport
        ((hF.compact_supp σ hσ c').mul_right)
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x => mul_nonneg (hF.range σ hσ c' x).1 (sq_nonneg _))]
    exact lintegral_congr fun x => (ENNReal.ofReal_mul (hF.range σ hσ c' x).1).symm
  simp only [hL, hR] at h
  rw [← ENNReal.ofReal_sum_of_nonneg fun c' _ => integral_nonneg fun x =>
    mul_nonneg (hF.range σ hσ c' x).1 (sq_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun c' _ =>
    integral_nonneg fun x => mul_nonneg (hF.range σ hσ c' x).1 (sq_nonneg _))).1 h

end HRS.MS.UniqG2fc
