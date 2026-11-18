import HRS.MS.ThCorrRespAux3
import HRS.MS.S111X2Aux5
import HRS.MS.S21F_D02

/-!
# S21F, packet R26-T3.C09: initial susceptibility contracts the actual-reference `L²` norm

At the ACTUAL initial reference `μ₀ = (1+εψ)ρ_β dx` (`TcRef` at order `0` from `r26t3_reference_data`), `Kop` is represented by a bounded
symmetric nonnegative operator (`s111x2_krep_of_tcref`, both `s = 0` and `s > 0`), so `ResponseForm` holds at `θ = γ ≥ 0`
(including `γ = 0`), and its Schwarz clause `|C(f,g)| ≤ ‖P f‖ ‖P g‖` gives the claim since `‖P f‖² = Var f ≤ ∫ f²`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole

theorem s21f_centered_le {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ] {f : Euc d → ℝ}
    (hf : MemLp f 2 μ) :
    HRS.MS.S111X2.s111x2_centeredSquare μ f ≤ ∫ x, f x ^ 2 ∂μ := by
  have h1 := variance_eq_integral (μ := μ) hf.aemeasurable
  have h2 := variance_le_expectation_sq (μ := μ) hf.aestronglyMeasurable
  unfold HRS.MS.S111X2.s111x2_centeredSquare HRS.Whole.projMean HRS.Whole.pair
  simp only [Pi.pow_apply] at h1 h2 ⊢
  simpa [h1] using h2

theorem r26t3_initial_cov_bound {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1/2)
    (R : Trajectory p δ) (f g : Euc p.d → ℝ)
    (hf : MemLp f 2 (r26t3_mu R 0)) (hg : MemLp g 2 (r26t3_mu R 0)) :
    |HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ f g| ≤
      Real.sqrt (∫ x, f x ^ 2 ∂(r26t3_mu R 0)) * Real.sqrt (∫ x, g x ^ 2 ∂(r26t3_mu R 0)) := by
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M, c, S, hc, hTc⟩ := href 0
  have hd := p.hd
  have hsd : p.s < (p.d : ℝ) := by
    have := p.hs
    have : (0 : ℝ) < p.d := by exact_mod_cast (by omega : 0 < p.d)
    linarith
  have hP : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  have hP' : IsProbabilityMeasure (r26t3_mu R 0) := hP
  obtain ⟨Mg, K, hK⟩ := HRS.MS.S111X2.s111x2_krep_of_tcref (by omega) p.hs0 hsd hc hTc
  have hform := HRS.MS.S111X2.s111x2_responseForm hK p.hγ le_rfl
  refine (hform.schwarz f g hf hg).trans ?_
  exact mul_le_mul (Real.sqrt_le_sqrt (s21f_centered_le _ hf)) (Real.sqrt_le_sqrt (s21f_centered_le _ hg))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end HRS.MS.R26T3
