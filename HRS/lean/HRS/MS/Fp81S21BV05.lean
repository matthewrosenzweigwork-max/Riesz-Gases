import HRS.MS.Fp81S21BV04

/-! The variation norm on anchored continuous BV paths. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set
open scoped ENNReal
namespace HRS.Fp81.S21
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : ℝ} (hH : 0 ≤ H)

instance : Norm (fp81s21_BV0 (E := E) hH) :=
  ⟨fun v => (eVariationOn (fp81s21_bvExt hH v) (Icc 0 H)).toReal⟩

theorem fp81s21_bv_norm_eq (v : fp81s21_BV0 (E := E) hH) :
    ‖v‖ = (eVariationOn (fp81s21_bvExt hH v) (Icc 0 H)).toReal := rfl

theorem fp81s21_bvExt_add (v w : fp81s21_BV0 (E := E) hH) :
    fp81s21_bvExt hH (v + w) = fun t => fp81s21_bvExt hH v t + fp81s21_bvExt hH w t := rfl

theorem fp81s21_bvExt_smul (c : ℝ) (v : fp81s21_BV0 (E := E) hH) :
    fp81s21_bvExt hH (c • v) = fun t => c • fp81s21_bvExt hH v t := rfl

theorem fp81s21_bvPath_injective : Function.Injective (fp81s21_BV0.path (E := E) (hH := hH)) := by
  intro v w h
  cases v
  cases w
  cases h
  rfl

def fp81s21_bvNormCore : NormedSpace.Core ℝ (fp81s21_BV0 (E := E) hH) where
  norm_nonneg v := ENNReal.toReal_nonneg
  norm_smul c v := by
    change (eVariationOn (fp81s21_bvExt hH (c • v)) (Icc 0 H)).toReal = _
    rw [fp81s21_bvExt_smul, fp81s21_eVariationOn_smul, ENNReal.toReal_smul]
    rfl
  norm_triangle v w := by
    change (eVariationOn (fp81s21_bvExt hH (v + w)) (Icc 0 H)).toReal ≤ _
    rw [fp81s21_bvExt_add]
    calc
      (eVariationOn (fun t => fp81s21_bvExt hH v t + fp81s21_bvExt hH w t) (Icc 0 H)).toReal
          ≤ (eVariationOn (fp81s21_bvExt hH v) (Icc 0 H) +
              eVariationOn (fp81s21_bvExt hH w) (Icc 0 H)).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨v.bv, w.bv⟩)
            (fp81s21_eVariationOn_add_le _ _ _)
      _ = _ := ENNReal.toReal_add v.bv w.bv
  norm_eq_zero_iff v := by
    constructor
    · intro hv
      apply fp81s21_bvPath_injective hH
      ext t
      have hle := fp81s21_bvPath_norm_le_variation hH v t
      change ‖v.path t‖ ≤ ‖v‖ at hle
      rw [hv] at hle
      have hz : (0 : fp81s21_BV0 (E := E) hH).path = 0 := rfl
      rw [hz]
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    · intro hv
      subst v
      change (eVariationOn (fp81s21_bvExt hH 0) (Icc 0 H)).toReal = 0
      have hz : (0 : fp81s21_BV0 (E := E) hH).path = 0 := rfl
      simp [fp81s21_bvExt, hz, eVariationOn]

instance : NormedAddCommGroup (fp81s21_BV0 (E := E) hH) :=
  NormedAddCommGroup.ofCore (fp81s21_bvNormCore hH)
instance : NormedSpace ℝ (fp81s21_BV0 (E := E) hH) :=
  NormedSpace.ofCore (fp81s21_bvNormCore hH)

#print axioms fp81s21_bv_norm_eq
#print axioms fp81s21_bvExt_add
#print axioms fp81s21_bvExt_smul
#print axioms fp81s21_bvPath_injective
#print axioms fp81s21_bvNormCore
end HRS.Fp81.S21
end
