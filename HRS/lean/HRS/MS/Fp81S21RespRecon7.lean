import HRS.MS.Fp81S21RespRecon6
import HRS.MS.R26T8AS04a

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2

/-- The actual response commutes almost everywhere with any pointwise
integral whose L² curve and joint representatives satisfy the stated
Bochner and Fubini hypotheses. -/
theorem fp81s21_respRecon_response_interchange_ae
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [SFinite ν]
    (g : A → Euc p.d → ℝ)
    (hg : AEStronglyMeasurable (Function.uncurry g) (ν.prod (r26t3_mu R 0)))
    (hr : AEStronglyMeasurable (Function.uncurry (fun t => r26t3_a R (g t)))
      (ν.prod (r26t3_mu R 0)))
    (hmem : ∀ᵐ t ∂ν, MemLp (g t) 2 (r26t3_mu R 0))
    (hV : Integrable (fun t => s111x2_toLp (r26t3_mu R 0) (g t)) ν)
    (hq : MemLp (fun x => ∫ t, g t x ∂ν) 2 (r26t3_mu R 0)) :
    r26t3_a R (fun x => ∫ t, g t x ∂ν) =ᵐ[r26t3_mu R 0]
      fun x => ∫ t, r26t3_a R (g t) x ∂ν := by
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M, c, S, hc, hTc⟩ := href 0
  haveI : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  obtain ⟨T, hT⟩ := fp81s21_respRecon_response_L2 hδ hδh R
  have hVg : ∀ᵐ t ∂ν, ⇑(s111x2_toLp (r26t3_mu R 0) (g t)) =ᵐ[r26t3_mu R 0] g t := by
    filter_upwards [hmem] with t ht
    exact s111x2_toLp_ae ht
  have hTh : ∀ᵐ t ∂ν, ⇑(T (s111x2_toLp (r26t3_mu R 0) (g t))) =ᵐ[r26t3_mu R 0]
      r26t3_a R (g t) := by
    filter_upwards [hmem] with t ht
    have heq : ht.toLp (g t) = s111x2_toLp (r26t3_mu R 0) (g t) := by
      apply Lp.ext
      exact ht.coeFn_toLp.trans (s111x2_toLp_ae ht).symm
    rw [← heq]
    exact hT (g t) ht
  have hinter := fp81s21_respRecon_interchange_L2 ν (r26t3_mu R 0) T
    (fun t => s111x2_toLp (r26t3_mu R 0) (g t)) hV g
    (fun t => r26t3_a R (g t)) hg hr hVg hTh hq
  exact (hT _ hq).symm.trans hinter

#print axioms fp81s21_respRecon_response_interchange_ae

end HRS.Fp81.S21
end
