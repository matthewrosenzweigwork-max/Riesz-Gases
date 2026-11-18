import HRS.MS.SA16StrongLimit

/-!
# S.A.16: dominated convergence in `L^p` for a vanishing weight times a fixed `L^p` function
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

section DomLp
variable {d : ℕ}

lemma sa16y_dom_lp (p : ℝ) (hp : 1 ≤ p) (e : ℕ → Euc d → ℝ) (J : Euc d → ℝ) {E0 : ℝ}
    (hec : ∀ n, Continuous (e n)) (he0 : ∀ n x, 0 ≤ e n x) (heb : ∀ n x, e n x ≤ E0)
    (hel : ∀ x, Tendsto (fun n => e n x) atTop (𝓝 0)) (hJc : Continuous J)
    (hJ : MemLp J (ENNReal.ofReal p) volume) :
    Tendsto (fun n => eLpNorm (fun x => e n x * J x) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hpe0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hpetop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hE0 : 0 ≤ E0 := (he0 0 0).trans (heb 0 0)
  have hmeas : ∀ n, AEStronglyMeasurable (fun x => e n x * J x) volume := fun n =>
    ((hec n).mul hJc).aestronglyMeasurable
  have heq : ∀ n, eLpNorm (fun x => e n x * J x) (ENNReal.ofReal p) volume =
      (∫⁻ x, ‖e n x * J x‖ₑ ^ p) ^ (1 / p) := fun n => by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpe0 hpetop (hmeas n), hpr]
  simp_rw [heq]
  have hJint : ∫⁻ x, ‖J x‖ₑ ^ p < ⊤ := by
    have := hJ.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpe0 hpetop hJ.aestronglyMeasurable, hpr] at this
    have h2 : (∫⁻ x, ‖J x‖ₑ ^ p) ^ (1 / p) < ⊤ := this
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon, ENNReal.top_rpow_of_pos (by positivity)] at h2
    exact lt_irrefl _ h2
  have hlim : Tendsto (fun n => ∫⁻ x, ‖e n x * J x‖ₑ ^ p) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := (volume : Measure (Euc d)))
      (F := fun n x => ‖e n x * J x‖ₑ ^ p) (f := fun _ => 0)
      (bound := fun x => (ENNReal.ofReal E0) ^ p * ‖J x‖ₑ ^ p)
      (fun n => ((hec n).mul hJc).enorm.measurable.pow_const _)
      (fun n => Eventually.of_forall fun x => ?_)
      (by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)]
        exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)
          hJint.ne)
      (Eventually.of_forall fun x => ?_)
    · simpa using this
    · show ‖e n x * J x‖ₑ ^ p ≤ ENNReal.ofReal E0 ^ p * ‖J x‖ₑ ^ p
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
      refine ENNReal.rpow_le_rpow ?_ hp0.le
      rw [enorm_mul, Real.enorm_eq_ofReal (he0 n x)]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (heb n x)) le_rfl
    · have h1 : Tendsto (fun n => e n x * J x) atTop (𝓝 0) := by
        simpa using (hel x).mul_const (J x)
      have h2 : Tendsto (fun n => ‖e n x * J x‖ₑ) atTop (𝓝 0) := by
        simpa using h1.enorm
      have h3 := ((ENNReal.continuous_rpow_const (y := p)).tendsto 0).comp h2
      rw [ENNReal.zero_rpow_of_pos hp0] at h3
      exact h3
  have h4 := ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0).comp hlim
  rw [ENNReal.zero_rpow_of_pos (show 0 < 1 / p by positivity)] at h4
  exact h4

end DomLp

end HRS.Whole.AppendixA.Phase2SA16
