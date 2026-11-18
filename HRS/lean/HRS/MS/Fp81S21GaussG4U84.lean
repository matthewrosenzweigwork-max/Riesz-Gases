import HRS.MS.Fp81S21GaussFeature

/-!
# HRS S2.1(iii), G4 U84: centered response estimate

The response square root acts on the centered L² class.  This adapter records
its exact centered norm bound; the reference-measure L² estimate needed to
remove the endpoint integrability hypotheses is a separate step.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Whole.Q34 HRS.MS.R26T3 HRS.MS.S111X2

/-- The response square root contracts the centered increment.  Endpoint
integrability is explicit here so this lemma isolates the centered response
step used by the full G4 initial adapter. -/
theorem fp81s21_g4_initial_increment_centered_response_bound
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ}
    {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ]
      Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    {f : Euc p.d → ℝ} {v w : ℝ}
    (hW : MemLp (propagatorW (r26t3_coeff R) 0 w f) 2 (r26t3_mu R 0))
    (hV : MemLp (propagatorW (r26t3_coeff R) 0 v f) 2 (r26t3_mu R 0)) :
    ‖fp81s21_initialGaussianFeature p R hK w f -
      fp81s21_initialGaussianFeature p R hK v f‖ ^ 2 ≤
        HRS.MS.S111X2.s111x2_centeredSquare (r26t3_mu R 0)
          (fun x => propagatorW (r26t3_coeff R) 0 w f x -
            propagatorW (r26t3_coeff R) 0 v f x) := by
  let μ := r26t3_mu R 0
  let Uw : Euc p.d → ℝ := propagatorW (r26t3_coeff R) 0 w f
  let Uv : Euc p.d → ℝ := propagatorW (r26t3_coeff R) 0 v f
  let D : Euc p.d → ℝ := fun x => Uw x - Uv x
  have hD : MemLp D 2 μ := hW.sub hV
  have htoLp :
      HRS.MS.S111X2.s111x2_toLp μ D =
        HRS.MS.S111X2.s111x2_toLp μ Uw -
          HRS.MS.S111X2.s111x2_toLp μ Uv := by
    apply Lp.ext
    filter_upwards
      [HRS.MS.S111X2.s111x2_toLp_ae hD,
        HRS.MS.S111X2.s111x2_toLp_ae hW,
        HRS.MS.S111X2.s111x2_toLp_ae hV,
        Lp.coeFn_sub (HRS.MS.S111X2.s111x2_toLp μ Uw)
          (HRS.MS.S111X2.s111x2_toLp μ Uv)] with x hDx hWx hVx hsub
    rw [hDx, hsub, Pi.sub_apply, hWx, hVx]
  have hfeature :
      fp81s21_initialGaussianFeature p R hK w f -
          fp81s21_initialGaussianFeature p R hK v f =
        HRS.MS.ProClosureS111.responseSqrt hK.posOp p.hγ
          (Pc μ (HRS.MS.S111X2.s111x2_toLp μ D)) := by
    change
      HRS.MS.ProClosureS111.responseSqrt hK.posOp p.hγ
          (Pc μ (HRS.MS.S111X2.s111x2_toLp μ Uw)) -
        HRS.MS.ProClosureS111.responseSqrt hK.posOp p.hγ
          (Pc μ (HRS.MS.S111X2.s111x2_toLp μ Uv)) = _
    rw [← map_sub, ← map_sub, ← htoLp]
  have hresponse := HRS.MS.ProClosureS111.responseSqrt_norm_le
    hK.posOp p.hγ (Pc μ (HRS.MS.S111X2.s111x2_toLp μ D))
  calc
    ‖fp81s21_initialGaussianFeature p R hK w f -
        fp81s21_initialGaussianFeature p R hK v f‖ ^ 2 =
      ‖HRS.MS.ProClosureS111.responseSqrt hK.posOp p.hγ
          (Pc μ (HRS.MS.S111X2.s111x2_toLp μ D))‖ ^ 2 := by rw [hfeature]
    _ ≤ ‖Pc μ (HRS.MS.S111X2.s111x2_toLp μ D)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hresponse 2
    _ = HRS.MS.S111X2.s111x2_centeredSquare μ D := by
      rw [← HRS.MS.S111X2.s111x2_cl_eq_Pc hD,
        HRS.MS.S111X2.s111x2_cl_norm_sq hD]

#print axioms fp81s21_g4_initial_increment_centered_response_bound

end HRS.Fp81.S21
