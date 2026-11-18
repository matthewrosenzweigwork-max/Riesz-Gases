import HRS.MS.Fp81S21BV010

/-! Completeness for the variation norm. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace HRS.Fp81.S21
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : ℝ} (hH : 0 ≤ H)

theorem fp81s21_bvCauchy_tendsto (u : ℕ → fp81s21_BV0 (E := E) hH)
    (hu : CauchySeq u) : ∃ v, Tendsto u atTop (𝓝 v) := by
  obtain ⟨f, hf, hf0⟩ := fp81s21_bvCauchy_path_limit hH u hu
  let v : fp81s21_BV0 (E := E) hH := ⟨f, hf0, fp81s21_bvCauchy_limit_bv hH u hu f hf⟩
  refine ⟨v, Metric.tendsto_atTop.2 ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε / 2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro m hm
  have hbound : ∀ᶠ n in atTop, ‖u n - u m‖ ≤ ε / 2 := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact le_of_lt (by simpa [dist_eq_norm] using hN n hn m hm)
  have hd := fp81s21_bv_limit_difference_variation hH u f hf m hbound
  have hd' : eVariationOn (fp81s21_bvExt hH (v - u m)) (Icc 0 H) ≤
      ENNReal.ofReal (ε / 2) := by
    rw [fp81s21_bvExt_sub]
    exact hd
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd'
  have hnorm : ‖v - u m‖ ≤ ε / 2 := by
    rw [← fp81s21_bv_norm_eq] at hreal
    simpa [ENNReal.toReal_ofReal (le_of_lt (half_pos hε))] using hreal
  have hlt : ‖v - u m‖ < ε := lt_of_le_of_lt hnorm (half_lt_self hε)
  simpa [dist_eq_norm, norm_sub_rev] using hlt

instance fp81s21_bvCompleteSpace : CompleteSpace (fp81s21_BV0 (E := E) hH) :=
  Metric.complete_of_cauchySeq_tendsto (fp81s21_bvCauchy_tendsto hH)

#print axioms fp81s21_bvCauchy_tendsto
#print axioms fp81s21_bvCompleteSpace
end HRS.Fp81.S21
end
