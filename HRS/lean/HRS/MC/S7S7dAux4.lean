import HRS.MC.S7S7dAux1
import HRS.MC.S7S7c

/-!
# Packet `s7_S7d_uniform_limits`, helper 4: the class of Stein solutions

For `Phi` in the `C_b^5` unit ball and `G` centred Gaussian, `f = steinSolG G Phi` is `C^4` (indeed `C^5`) with
`||D^j f|| <= 1` for `1 <= j <= 4`.  Everything downstream is stated for the class `s7d_Cl`, so that the
uniformity in `Phi` is uniformity over this class.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ}

/-- The class of functions with `D^j f` bounded by `1` for `1 <= j <= 4`. -/
def s7d_Cl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) : Prop :=
  ContDiff ℝ 4 f ∧ ∀ j, 1 ≤ j → j ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ 1

theorem s7d_cbSup_le_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    {Φ : E → ℝ} (hΦ : Φ ∈ CbUnitBall E 5) {j : ℕ} (hj : j ≤ 5) : cbSup Φ j ≤ 1 := by
  obtain ⟨-, -, hc⟩ := hΦ
  unfold cbNorm at hc
  have hnn : ∀ i ∈ Finset.range (5 + 1), 0 ≤ ⨆ z : E, ‖iteratedFDeriv ℝ i Φ z‖ :=
    fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have := Finset.single_le_sum hnn (Finset.mem_range.2 (by omega : j < 5 + 1))
  exact this.trans hc

theorem s7d_stein_cl {r : ℝ} (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussian G) {Φ : NegSobolev d r → ℝ} (hΦ : Φ ∈ CbUnitBall (NegSobolev d r) 5) :
    s7d_Cl (steinSolG G Φ) := by
  have hmem : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  haveI := hG.1
  have hγ1 : Integrable (fun y : NegSobolev d r => ‖y‖) G := (IsGaussian.integrable_id (μ := G)).norm
  refine ⟨(contDiff_steinSolG hmem hγ1).of_le (by norm_num), fun j hj1 hj4 x => ?_⟩
  refine (norm_iteratedFDeriv_steinSolG_le hmem hγ1 j hj1 (by omega) x).trans ?_
  have h1 := s7d_cbSup_le_one hΦ (j := j) (by omega)
  have h2 : (j : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hj1)
  have h3 : 0 ≤ cbSup Φ j := cbSup_nonneg hmem (by omega)
  nlinarith

end HRS.MC.Sec7.S7d

end
