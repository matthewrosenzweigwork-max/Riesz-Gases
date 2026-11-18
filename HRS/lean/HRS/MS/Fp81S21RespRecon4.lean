import HRS.MS.Fp81S21RespRecon3
import HRS.MS.S111X2Aux3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory
namespace HRS.Fp81.S21
open HRS.MS.S111X2

/-- The positive-operator resolvent is a bounded linear map, with norm at most one. -/
theorem fp81s21_respRecon_resolvent_clm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {K : H →L[ℝ] H} {M θ : ℝ} (hK : PosOp K M) (hθ : 0 ≤ θ) :
    ∃ T : H →L[ℝ] H, ‖T‖ ≤ 1 ∧ ∀ f, T f = s111x2_Res hK hθ f := by
  let L : H →ₗ[ℝ] H :=
    { toFun := s111x2_Res hK hθ
      map_add' := s111x2_Res_add hK hθ
      map_smul' := fun c f => s111x2_Res_smul hK hθ c f }
  have hbound : ∀ f, ‖L f‖ ≤ 1 * ‖f‖ := by
    intro f
    simpa [L] using (s111x2_Res_bounds hK hθ f).2.2
  let T : H →L[ℝ] H := LinearMap.mkContinuous L 1 hbound
  refine ⟨T, ?_, fun _ => rfl⟩
  exact LinearMap.mkContinuous_norm_le L (by norm_num) hbound

#print axioms fp81s21_respRecon_resolvent_clm

end HRS.Fp81.S21
end
