import HRS.MS.Fp81S21BV05

/-! The continuous inclusion into the supremum-norm path space. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set
namespace HRS.Fp81.S21
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : ℝ} (hH : 0 ≤ H)

def fp81s21_bvPathLinear : fp81s21_BV0 (E := E) hH →ₗ[ℝ] C(Icc (0 : ℝ) H, E) where
  toFun := fp81s21_BV0.path
  map_add' := by intro v w; rfl
  map_smul' := by intro c v; rfl

theorem fp81s21_bvPath_norm_le (v : fp81s21_BV0 (E := E) hH) :
    ‖v.path‖ ≤ ‖v‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg v)).2
  intro t
  exact fp81s21_bvPath_norm_le_variation hH v t

/-- The canonical inclusion, with operator norm at most one. -/
def fp81s21_bvPath : fp81s21_BV0 (E := E) hH →L[ℝ] C(Icc (0 : ℝ) H, E) :=
  (fp81s21_bvPathLinear hH).mkContinuous 1 (by
    intro v
    change ‖v.path‖ ≤ 1 * ‖v‖
    simpa using fp81s21_bvPath_norm_le hH v)

theorem fp81s21_bvPath_apply (v : fp81s21_BV0 (E := E) hH) :
    fp81s21_bvPath hH v = v.path := rfl

theorem fp81s21_bvPath_opNorm_le : ‖fp81s21_bvPath (E := E) hH‖ ≤ 1 := by
  apply LinearMap.mkContinuous_norm_le _ (by norm_num)

#print axioms fp81s21_bvPathLinear
#print axioms fp81s21_bvPath_norm_le
#print axioms fp81s21_bvPath
#print axioms fp81s21_bvPath_apply
#print axioms fp81s21_bvPath_opNorm_le
end HRS.Fp81.S21
end
