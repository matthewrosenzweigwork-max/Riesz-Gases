import HRS.MS.Fp81S21IntervalBV

/-! Continuous linear transport from interval increments to anchored BV paths. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set
open scoped ENNReal
namespace HRS.Fp81.S21

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H K : ℝ} (hH : 0 ≤ H)

/-- Data for an interval-additive family with a scalar cumulative variation control.
The control can depend on the input; it need not be linear in it. -/
structure fp81s21_IntervalBVData (K : ℝ) where
  delta : ℝ → ℝ → X →L[ℝ] E
  zero : delta 0 0 = 0
  add : ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H, s ≤ t →
    delta 0 t = delta 0 s + delta s t
  cont : ∀ x, ContinuousOn (fun t => delta 0 t x) (Icc 0 H)
  control : X → ℝ → ℝ
  control_mono : ∀ x, MonotoneOn (control x) (Icc 0 H)
  inc_le : ∀ x s, s ∈ Icc (0 : ℝ) H → ∀ t, t ∈ Icc (0 : ℝ) H → s ≤ t →
    ‖delta s t x‖ ≤ control x t - control x s
  total_le : ∀ x, control x H - control x 0 ≤ K * ‖x‖

variable (D : fp81s21_IntervalBVData (X := X) (E := E) (H := H) K)

/-- The variation of each cumulative path is bounded by the scalar control. -/
theorem fp81s21_intervalVariation_le (hH : 0 ≤ H) (x : X) :
    eVariationOn (fun t => D.delta 0 t x) (Icc 0 H) ≤
      ENNReal.ofReal (K * ‖x‖) := by
  apply (fp81s21_variation_le_control hH _ _ (D.control_mono x) ?_).trans
    (ENNReal.ofReal_le_ofReal (D.total_le x))
  intro s hs t ht hst
  have ha := D.add s hs t ht hst
  have ha' := congrArg (fun A : X →L[ℝ] E => A x) ha
  simp only [ContinuousLinearMap.add_apply] at ha'
  rw [ha', add_sub_cancel_left]
  exact D.inc_le x s hs t ht hst

/-- The anchored continuous BV path associated with one input. -/
def fp81s21_intervalBVValue (x : X) : fp81s21_BV0 (E := E) hH where
  path := ⟨fun t => D.delta 0 t x, by
    change Continuous (fun t : Icc (0 : ℝ) H => D.delta 0 t x)
    exact continuousOn_iff_continuous_restrict.mp (D.cont x)⟩
  zero_at_left := by
    change D.delta 0 0 x = 0
    rw [D.zero]
    rfl
  bv := by
    have heq : EqOn (fun t : ℝ => D.delta 0 (projIcc 0 H hH t) x)
        (fun t => D.delta 0 t x) (Icc 0 H) := by
      intro t ht
      simp [projIcc_of_mem hH ht]
    change eVariationOn (fun t : ℝ => D.delta 0 (projIcc 0 H hH t) x) (Icc 0 H) ≠ ⊤
    rw [eVariationOn.eq_of_eqOn heq]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (fp81s21_intervalVariation_le D hH x)

theorem fp81s21_intervalBVValue_norm_le (hK : 0 ≤ K) (x : X) :
    ‖fp81s21_intervalBVValue hH D x‖ ≤ K * ‖x‖ := by
  rw [fp81s21_bv_norm_eq]
  have heq : EqOn (fp81s21_bvExt hH (fp81s21_intervalBVValue hH D x))
      (fun t => D.delta 0 t x) (Icc 0 H) := by
    intro t ht
    change D.delta 0 (projIcc 0 H hH t) x = D.delta 0 t x
    rw [projIcc_of_mem hH ht]
  rw [eVariationOn.eq_of_eqOn heq]
  calc
    _ ≤ (ENNReal.ofReal (K * ‖x‖)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (fp81s21_intervalVariation_le D hH x)
    _ = _ := ENNReal.toReal_ofReal (mul_nonneg hK (norm_nonneg x))

/-- Cumulative interval operators as a bounded linear map into variation norm. -/
def fp81s21_intervalBV (hK : 0 ≤ K) : X →L[ℝ] fp81s21_BV0 (E := E) hH :=
  ({ toFun := fp81s21_intervalBVValue hH D
     map_add' := by
      intro x y
      apply fp81s21_bvPath_injective hH
      ext t
      change D.delta 0 t (x + y) = D.delta 0 t x + D.delta 0 t y
      exact map_add _ _ _
     map_smul' := by
      intro c x
      apply fp81s21_bvPath_injective hH
      ext t
      change D.delta 0 t (c • x) = c • D.delta 0 t x
      exact map_smul _ _ _ } : X →ₗ[ℝ] fp81s21_BV0 (E := E) hH).mkContinuous K
    (fp81s21_intervalBVValue_norm_le hH D hK)

theorem fp81s21_intervalBV_apply (hK : 0 ≤ K) (x : X) (s : Icc (0 : ℝ) H) :
    fp81s21_bvPath hH (fp81s21_intervalBV hH D hK x) s = D.delta 0 s x := rfl

theorem fp81s21_intervalBV_norm_le (hK : 0 ≤ K) :
    ‖fp81s21_intervalBV hH D hK‖ ≤ K := by
  apply LinearMap.mkContinuous_norm_le _ hK

#print axioms fp81s21_intervalVariation_le
#print axioms fp81s21_intervalBVValue
#print axioms fp81s21_intervalBVValue_norm_le
#print axioms fp81s21_intervalBV
#print axioms fp81s21_intervalBV_apply
#print axioms fp81s21_intervalBV_norm_le
end HRS.Fp81.S21
end
