import HRS.MS.Fp81S21RespRecon5
import HRS.MS.S111X2Aux15
import HRS.MS.S21F_S02a

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2 HRS.Whole.Q34

/-- The actual response is represented by a single bounded linear map on L²,
including at zero coupling. -/
theorem fp81s21_respRecon_response_L2
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) :
    ∃ T : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0),
      ∀ f : Euc p.d → ℝ, ∀ hf : MemLp f 2 (r26t3_mu R 0),
        ⇑(T (hf.toLp f)) =ᵐ[r26t3_mu R 0] r26t3_a R f := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M, c, S, hc, hTc⟩ := href 0
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  haveI : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  have hd : 1 ≤ p.d := by have := p.hd; omega
  obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref hd p.hs0 hsd hc hTc
  change KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg at hK
  refine ⟨(s111x2_Rm hK.posOp p.hγ).comp (Pc (r26t3_mu R 0)), ?_⟩
  intro f hf
  have heq : hf.toLp f = s111x2_toLp (r26t3_mu R 0) f := by
    apply Lp.ext
    exact hf.coeFn_toLp.trans (s111x2_toLp_ae hf).symm
  rw [heq]
  change ⇑(s111x2_Rm hK.posOp p.hγ (Pc (r26t3_mu R 0)
    (s111x2_toLp (r26t3_mu R 0) f))) =ᵐ[_] _
  rw [← s111x2_cl_eq_Pc hf]
  change ⇑(s111x2_Res hK.posOp p.hγ (s111x2_cl hf)) =ᵐ[_] _
  exact (s111x2_responseInverse_ae hK p.hγ hf).symm.trans
    (r26t3_response_ae hδ hδh R f hf).symm

#print axioms fp81s21_respRecon_response_L2

end HRS.Fp81.S21
end
