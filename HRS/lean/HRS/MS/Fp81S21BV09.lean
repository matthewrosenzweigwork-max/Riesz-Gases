import HRS.MS.Fp81S21BV08

/-! Pass variation bounds on differences to a uniform path limit. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace HRS.Fp81.S21
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : ℝ} (hH : 0 ≤ H)

theorem fp81s21_bvExt_sub (v w : fp81s21_BV0 (E := E) hH) :
    fp81s21_bvExt hH (v - w) = fun t => fp81s21_bvExt hH v t - fp81s21_bvExt hH w t := rfl

theorem fp81s21_bv_limit_difference_variation
    (u : ℕ → fp81s21_BV0 (E := E) hH) (f : C(Icc (0 : ℝ) H, E))
    (hf : Tendsto (fun n => (u n).path) atTop (𝓝 f)) (m : ℕ) {C : ℝ}
    (hbound : ∀ᶠ n in atTop, ‖u n - u m‖ ≤ C) :
    eVariationOn (fun t : ℝ => f (projIcc 0 H hH t) - fp81s21_bvExt hH (u m) t)
      (Icc 0 H) ≤ ENNReal.ofReal C := by
  apply fp81s21_eVariationOn_le_of_tendsto
    (p := atTop) (F := fun n t => fp81s21_bvExt hH (u n - u m) t)
  · intro x hx
    have ht : Tendsto (fun n => (u n).path (projIcc 0 H hH x)) atTop
        (𝓝 (f (projIcc 0 H hH x))) := ((continuous_eval_const _).tendsto _).comp hf
    change Tendsto (fun n => fp81s21_bvExt hH (u n - u m) x) atTop _
    simp_rw [fp81s21_bvExt_sub]
    exact ht.sub tendsto_const_nhds
  · filter_upwards [hbound] with n hn
    have hfin := fp81s21_bvExt_bv hH (u n - u m)
    have hreal : ENNReal.ofReal ‖u n - u m‖ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hn
    rw [fp81s21_bv_norm_eq, ENNReal.ofReal_toReal hfin] at hreal
    exact hreal

#print axioms fp81s21_bvExt_sub
#print axioms fp81s21_bv_limit_difference_variation
end HRS.Fp81.S21
end
