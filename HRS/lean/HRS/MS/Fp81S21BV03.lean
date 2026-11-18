import HRS.MS.Fp81S21BV02
import Mathlib.Algebra.Module.TransferInstance

/-! The linear structure on continuous anchored bounded-variation paths. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set
open scoped ENNReal
namespace HRS.Fp81.S21
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : ℝ} (hH : 0 ≤ H)

/-- The anchored BV paths form a linear subspace of the continuous paths. -/
def fp81s21_bvSubmodule : Submodule ℝ C(Icc (0 : ℝ) H, E) where
  carrier := {f | f ⟨0, ⟨le_rfl, hH⟩⟩ = 0 ∧
    BoundedVariationOn (fun t : ℝ => f (projIcc 0 H hH t)) (Icc 0 H)}
  zero_mem' := by
    constructor
    · rfl
    · simp [BoundedVariationOn, eVariationOn]
  add_mem' := by
    intro f g hf hg
    constructor
    · simp [hf.1, hg.1]
    · exact fp81s21_boundedVariationOn_add hf.2 hg.2
  smul_mem' := by
    intro c f hf
    constructor
    · simp [hf.1]
    · exact ((ContinuousLinearMap.lsmul ℝ ℝ (E := E)) c).lipschitz.comp_boundedVariationOn hf.2

def fp81s21_bvEquiv : fp81s21_BV0 (E := E) hH ≃ fp81s21_bvSubmodule (E := E) hH where
  toFun v := ⟨v.path, v.zero_at_left, v.bv⟩
  invFun v := ⟨v.1, v.2.1, v.2.2⟩
  left_inv := by intro v; cases v; rfl
  right_inv := by intro v; cases v; rfl

instance : AddCommGroup (fp81s21_BV0 (E := E) hH) := (fp81s21_bvEquiv hH).addCommGroup

def fp81s21_bvAddEquiv : fp81s21_BV0 (E := E) hH ≃+ fp81s21_bvSubmodule (E := E) hH where
  toEquiv := fp81s21_bvEquiv hH
  map_add' := by intro x y; rfl

instance : Module ℝ (fp81s21_BV0 (E := E) hH) := (fp81s21_bvAddEquiv hH).module ℝ

#print axioms fp81s21_bvSubmodule
#print axioms fp81s21_bvEquiv
#print axioms fp81s21_bvAddEquiv
end HRS.Fp81.S21
end
