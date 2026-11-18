import HRS.MS.Fp81S21FutureIndep22
import HRS.MS.Fp81S21MovingFuture

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111X1

/-- Linear future feature map into the retained source's Hilbert space. -/
def fp81s21_futureFeatureLinear
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert) :
    oscSub p.d (wholeSpaceIndex p.d : ℝ) →ₗ[ℝ] GaussianFeatureHilbert where
  toFun := fun φ => J (fp81s21_futureNoiseSourceFeature p R r t (φ : Euc p.d → ℝ))
  map_add' := by
    intro φ ψ
    have h := fp81s21_movingNoiseFeature_add_smul p R hδ hδhalf hH hr ht
      φ.property ψ.property 1
    change J (WithLp.toLp 2 (0, movingNoiseFeature R r t
      (fun x => (φ : Euc p.d → ℝ) x + (ψ : Euc p.d → ℝ) x))) = _
    simp only [one_mul, one_smul] at h
    rw [h]
    simp only [← map_add, fp81s21_futureNoiseSourceFeature]
    congr 1
    apply WithLp.ofLp_injective
    simp
  map_smul' := by
    intro c φ
    have hz : movingNoiseFeature R r t (0 : Euc p.d → ℝ) = 0 := by
      have h := fp81s21_movingNoiseFeature_add_smul p R hδ hδhalf hH hr ht
        (oscSub p.d (wholeSpaceIndex p.d : ℝ)).zero_mem
        (oscSub p.d (wholeSpaceIndex p.d : ℝ)).zero_mem 1
      simp only [Pi.zero_apply, add_zero, mul_zero, one_smul] at h
      change movingNoiseFeature R r t (0 : Euc p.d → ℝ) =
        movingNoiseFeature R r t (0 : Euc p.d → ℝ) +
          movingNoiseFeature R r t (0 : Euc p.d → ℝ) at h
      have h' : movingNoiseFeature R r t (0 : Euc p.d → ℝ) + 0 =
          movingNoiseFeature R r t (0 : Euc p.d → ℝ) +
            movingNoiseFeature R r t (0 : Euc p.d → ℝ) := by simpa using h
      exact (add_left_cancel h').symm
    have h := fp81s21_movingNoiseFeature_add_smul p R hδ hδhalf hH hr ht
      (oscSub p.d (wholeSpaceIndex p.d : ℝ)).zero_mem φ.property c
    change J (WithLp.toLp 2 (0, movingNoiseFeature R r t
      (fun x => c * (φ : Euc p.d → ℝ) x))) = _
    simp only [Pi.zero_apply, zero_add, hz] at h
    rw [h]
    simp only [← map_smul, fp81s21_futureNoiseSourceFeature]
    congr 1
    apply WithLp.ofLp_injective
    simp

/-- The retained embedding preserves the norm of the future noise feature. -/
theorem fp81s21_futureFeatureLinear_norm
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
    (φ : oscSub p.d (wholeSpaceIndex p.d : ℝ)) :
    ‖fp81s21_futureFeatureLinear p R hδ hδhalf hH hr ht J φ‖ =
      ‖movingNoiseFeature R r t (φ : Euc p.d → ℝ)‖ := by
  change ‖J (fp81s21_futureNoiseSourceFeature p R r t (φ : Euc p.d → ℝ))‖ = _
  rw [J.norm_map]
  have hp := WithLp.prod_inner_apply (𝕜 := ℝ)
    (fp81s21_futureNoiseSourceFeature p R r t (φ : Euc p.d → ℝ))
    (fp81s21_futureNoiseSourceFeature p R r t (φ : Euc p.d → ℝ))
  have hs : ‖fp81s21_futureNoiseSourceFeature p R r t (φ : Euc p.d → ℝ)‖ ^ 2 =
      ‖movingNoiseFeature R r t (φ : Euc p.d → ℝ)‖ ^ 2 := by
    simpa [fp81s21_futureNoiseSourceFeature, real_inner_self_eq_norm_sq] using hp
  nlinarith [norm_nonneg (fp81s21_futureNoiseSourceFeature p R r t (φ : Euc p.d → ℝ)),
    norm_nonneg (movingNoiseFeature R r t (φ : Euc p.d → ℝ))]

#print axioms fp81s21_futureFeatureLinear
#print axioms fp81s21_futureFeatureLinear_norm
end HRS.Fp81.S21
end
