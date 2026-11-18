import HRS.MS.Fp81S21FutureIndep36
import HRS.MS.Fp81S21GaussFeature2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111X1 HRS.MS.S111X2

/-- The retained initial-plus-noise feature is linear in oscillator tests. -/
def fp81s21_combinedFeatureLinear
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) H) :
    oscSub p.d (wholeSpaceIndex p.d : ℝ) →ₗ[ℝ] Fp81S21GaussFeatureHilbert p R where
  toFun := fun φ => fp81s21_combinedFeature p R hK t (φ : Euc p.d → ℝ)
  map_add' := by
    intro φ ψ
    have h := fp81s21_combinedFeature_add_smul p R hδ hδhalf hH hK ht φ.property ψ.property 1
    change fp81s21_combinedFeature p R hK t
      (fun x => (φ : Euc p.d → ℝ) x + (ψ : Euc p.d → ℝ) x) = _
    simpa only [one_mul, one_smul] using h
  map_smul' := by
    intro c φ
    have hz : fp81s21_combinedFeature p R hK t (0 : Euc p.d → ℝ) = 0 := by
      have h := fp81s21_combinedFeature_add_smul p R hδ hδhalf hH hK ht
        (oscSub p.d (wholeSpaceIndex p.d : ℝ)).zero_mem
        (oscSub p.d (wholeSpaceIndex p.d : ℝ)).zero_mem 1
      simp only [Pi.zero_apply, add_zero, mul_zero, one_smul] at h
      change fp81s21_combinedFeature p R hK t (0 : Euc p.d → ℝ) =
        fp81s21_combinedFeature p R hK t (0 : Euc p.d → ℝ) +
          fp81s21_combinedFeature p R hK t (0 : Euc p.d → ℝ) at h
      have h' : fp81s21_combinedFeature p R hK t (0 : Euc p.d → ℝ) + 0 =
        fp81s21_combinedFeature p R hK t (0 : Euc p.d → ℝ) +
          fp81s21_combinedFeature p R hK t (0 : Euc p.d → ℝ) := by simpa using h
      exact (add_left_cancel h').symm
    have h := fp81s21_combinedFeature_add_smul p R hδ hδhalf hH hK ht
      (oscSub p.d (wholeSpaceIndex p.d : ℝ)).zero_mem φ.property c
    change fp81s21_combinedFeature p R hK t (fun x => c * (φ : Euc p.d → ℝ) x) = _
    simpa only [Pi.zero_apply, zero_add, hz, smul_eq_mul, RingHom.id_apply] using h

#print axioms fp81s21_combinedFeatureLinear
end HRS.Fp81.S21
end
