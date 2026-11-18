import HRS.MS.Fp81S21BV03

/-! Scalar homogeneity of total variation. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fp81s21_eVariationOn_smul (c : ℝ) (f : ℝ → E) (s : Set ℝ) :
    eVariationOn (fun x => c • f x) s = ‖c‖₊ • eVariationOn f s := by
  unfold eVariationOn
  simp_rw [edist_smul₀, ← Finset.smul_sum]
  rw [ENNReal.smul_iSup]

#print axioms fp81s21_eVariationOn_smul
end HRS.Fp81.S21
end
