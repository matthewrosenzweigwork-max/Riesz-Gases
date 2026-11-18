import HRS.MS.Fp81S21BV09

/-! The uniform limit of a variation-Cauchy sequence is of bounded variation. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace HRS.Fp81.S21
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : ℝ} (hH : 0 ≤ H)

theorem fp81s21_bvCauchy_limit_bv (u : ℕ → fp81s21_BV0 (E := E) hH)
    (hu : CauchySeq u) (f : C(Icc (0 : ℝ) H, E))
    (hf : Tendsto (fun n => (u n).path) atTop (𝓝 f)) :
    BoundedVariationOn (fun t : ℝ => f (projIcc 0 H hH t)) (Icc 0 H) := by
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu 1 zero_lt_one
  have hbound : ∀ᶠ n in atTop, ‖u n - u N‖ ≤ (1 : ℝ) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_of_lt (by simpa [dist_eq_norm] using hN n hn N le_rfl)
  have hd := fp81s21_bv_limit_difference_variation hH u f hf N hbound
  have hdiff : BoundedVariationOn
      (fun t : ℝ => f (projIcc 0 H hH t) - fp81s21_bvExt hH (u N) t) (Icc 0 H) :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd
  have hsum := fp81s21_boundedVariationOn_add hdiff (fp81s21_bvExt_bv hH (u N))
  simpa only [sub_add_cancel] using hsum

#print axioms fp81s21_bvCauchy_limit_bv
end HRS.Fp81.S21
end
