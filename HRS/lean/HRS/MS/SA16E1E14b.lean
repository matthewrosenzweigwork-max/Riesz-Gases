import HRS.MS.SA16E1E14a

/-!
# S.A.16 E14 (part b): joint continuity of a family of probability densities from weak continuity
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Base

variable {d : ℕ}

/-- the mollified family -/
def e14M (n : ℕ) (g : ℝ → Euc d → ℝ) (q : ℝ × Euc d) : ℝ :=
  ∫ y, sa16y_rho d n (q.2 - y) * g q.1 y

lemma e14_rho_shift_int (n : ℕ) (x : Euc d) : ∫ y, sa16y_rho d n (x - y) = 1 := by
  rw [integral_sub_left_eq_self (fun y => sa16y_rho d n y) (μ := (volume : Measure (Euc d))) x]
  exact sa16y_rho_int n

lemma e14_rho_shift_integrable (n : ℕ) (x : Euc d) : Integrable (fun y => sa16y_rho d n (x - y)) :=
  (sa16y_rho_integrable n).comp_sub_left x

theorem e14_unif_approx {g : ℝ → Euc d → ℝ} {r : ℝ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hint : Integrable (g r)) (hgc : Continuous (g r))
    (hlip : ∀ x y, |g r x - g r y| ≤ Λ * ‖x - y‖) (n : ℕ) (x : Euc d) :
    |e14M n g (r, x) - g r x| ≤ Λ / ((n : ℝ) + 1) := by
  have hn1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
  obtain ⟨Cρ, hCρ⟩ := (sa16y_rho_smooth (d := d) n).continuous.bounded_above_of_compact_support
    (sa16y_rho_compact n)
  have hρc : Continuous (fun y => sa16y_rho d n (x - y)) :=
    (sa16y_rho_smooth (d := d) n).continuous.comp (continuous_const.sub continuous_id)
  have hf1 : Integrable (fun y => sa16y_rho d n (x - y) * g r y) :=
    hint.bdd_mul hρc.aestronglyMeasurable (Eventually.of_forall fun y => hCρ _)
  have hf2 : Integrable (fun y => sa16y_rho d n (x - y) * g r x) :=
    (e14_rho_shift_integrable n x).mul_const _
  have hdiff : e14M n g (r, x) - g r x = ∫ y, sa16y_rho d n (x - y) * (g r y - g r x) := by
    have : g r x = ∫ y, sa16y_rho d n (x - y) * g r x := by
      rw [integral_mul_const, e14_rho_shift_int, one_mul]
    conv_lhs => rw [this]
    unfold e14M
    rw [← integral_sub hf1 hf2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [mul_sub]
  rw [hdiff, ← Real.norm_eq_abs]
  have hbd : Integrable (fun y => sa16y_rho d n (x - y) * (Λ / ((n : ℝ) + 1))) :=
    (e14_rho_shift_integrable n x).mul_const _
  refine (norm_integral_le_of_norm_le hbd (Eventually.of_forall fun y => ?_)).trans ?_
  · rw [norm_mul, Real.norm_of_nonneg (sa16y_rho_nonneg n _)]
    by_cases hy : 1 / ((n : ℝ) + 1) < ‖x - y‖
    · rw [sa16y_rho_supp n _ hy]; simp
    · push Not at hy
      refine mul_le_mul_of_nonneg_left ?_ (sa16y_rho_nonneg n _)
      rw [Real.norm_eq_abs]
      refine (hlip y x).trans ?_
      calc Λ * ‖y - x‖ = Λ * ‖x - y‖ := by rw [norm_sub_rev]
        _ ≤ Λ * (1 / ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left hy hΛ
        _ = Λ / ((n : ℝ) + 1) := by ring
  · rw [integral_mul_const, e14_rho_shift_int, one_mul]

theorem e14_M_cont {S : Set ℝ} {g : ℝ → Euc d → ℝ}
    (hint : ∀ r ∈ S, Integrable (g r)) (hnn : ∀ r ∈ S, ∀ x, 0 ≤ g r x)
    (hone : ∀ r ∈ S, ∫ x, g r x = 1)
    (hw : ∀ ψ : Euc d → ℝ, Continuous ψ → (∃ B, ∀ x, |ψ x| ≤ B) →
      ContinuousOn (fun r => ∫ x, ψ x * g r x) S) (n : ℕ) :
    ContinuousOn (e14M n g) (S ×ˢ univ) := by
  intro q hq
  obtain ⟨r0, x0⟩ := q
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hρuc : UniformContinuous (sa16y_rho (d := d) n) :=
    (sa16y_rho_compact n).uniformContinuous_of_continuous (sa16y_rho_smooth (d := d) n).continuous
  obtain ⟨δ1, hδ1, hδ1'⟩ := Metric.uniformContinuous_iff.1 hρuc (ε / 4) (by positivity)
  have hψc : Continuous (fun y => sa16y_rho d n (x0 - y)) :=
    (sa16y_rho_smooth (d := d) n).continuous.comp (continuous_const.sub continuous_id)
  obtain ⟨Cρ, hCρ⟩ := (sa16y_rho_smooth (d := d) n).continuous.bounded_above_of_compact_support
    (sa16y_rho_compact n)
  have hψb : ∃ B, ∀ y, |sa16y_rho d n (x0 - y)| ≤ B := ⟨Cρ, fun y => by
    simpa [Real.norm_eq_abs] using hCρ (x0 - y)⟩
  have hcw := hw _ hψc hψb r0 hq.1
  rw [Metric.continuousWithinAt_iff] at hcw
  obtain ⟨δ2, hδ2, hδ2'⟩ := hcw (ε / 3) (by positivity)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun q' hq' hd => ?_⟩
  obtain ⟨r, x⟩ := q'
  have hd1 : ‖x - x0‖ < δ1 := by
    have : dist x x0 ≤ dist (r, x) (r0, x0) := by
      rw [Prod.dist_eq]; exact le_max_right _ _
    rw [← dist_eq_norm]; exact lt_of_le_of_lt this (lt_of_lt_of_le hd (min_le_left _ _))
  have hd2 : dist r r0 < δ2 := by
    have : dist r r0 ≤ dist (r, x) (r0, x0) := by
      rw [Prod.dist_eq]; exact le_max_left _ _
    exact lt_of_le_of_lt this (lt_of_lt_of_le hd (min_le_right _ _))
  have hrS : r ∈ S := hq'.1
  have hint' := hint r hrS
  have hf : ∀ z : Euc d, Integrable (fun y => sa16y_rho d n (z - y) * g r y) := fun z =>
    hint'.bdd_mul ((sa16y_rho_smooth (d := d) n).continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable (Eventually.of_forall fun y => hCρ _)
  have hf0 : Integrable (fun y => sa16y_rho d n (x0 - y) * g r0 y) :=
    (hint r0 hq.1).bdd_mul hψc.aestronglyMeasurable (Eventually.of_forall fun y => hCρ _)
  have hA : |e14M n g (r, x) - ∫ y, sa16y_rho d n (x0 - y) * g r y| < ε / 3 := by
    unfold e14M
    simp only []
    rw [← integral_sub (hf x) (hf x0)]
    have hb : ∀ y, ‖sa16y_rho d n (x - y) * g r y - sa16y_rho d n (x0 - y) * g r y‖ ≤
        ε / 4 * g r y := by
      intro y
      rw [← sub_mul, norm_mul, Real.norm_of_nonneg (hnn r hrS y)]
      refine mul_le_mul_of_nonneg_right ?_ (hnn r hrS y)
      have := hδ1' (a := x - y) (b := x0 - y) (by
        rw [dist_eq_norm]; simpa using hd1)
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs]; exact this.le
    have hbi : Integrable (fun y => ε / 4 * g r y) := hint'.const_mul _
    have := norm_integral_le_of_norm_le hbi (Eventually.of_forall hb)
    rw [integral_const_mul, hone r hrS, mul_one] at this
    rw [Real.norm_eq_abs] at this
    exact lt_of_le_of_lt this (by linarith)
  have hB : |(∫ y, sa16y_rho d n (x0 - y) * g r y) - e14M n g (r0, x0)| < ε / 3 := by
    have := hδ2' hrS hd2
    rw [Real.dist_eq] at this
    exact this
  rw [Real.dist_eq]
  calc |e14M n g (r, x) - e14M n g (r0, x0)|
      = |(e14M n g (r, x) - ∫ y, sa16y_rho d n (x0 - y) * g r y) +
          ((∫ y, sa16y_rho d n (x0 - y) * g r y) - e14M n g (r0, x0))| := by ring_nf
    _ ≤ |e14M n g (r, x) - ∫ y, sa16y_rho d n (x0 - y) * g r y| +
          |(∫ y, sa16y_rho d n (x0 - y) * g r y) - e14M n g (r0, x0)| := abs_add_le _ _
    _ < ε := by linarith

end Base

end HRS.Whole.AppendixA.Phase2SA16Evolution
