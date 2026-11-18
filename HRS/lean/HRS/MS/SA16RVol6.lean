import HRS.MS.SA16RVol5

/-!
# S.A.16 (SA16R) Vol6: triangle Fubini and integrability of the double integrand

* `sa16r_tri_swap`: for `F` integrable on the triangle `{0 < y ≤ x ≤ a}`,
  `∫_{x ∈ (0,a]} ∫_{y ∈ (0,x]} F x y = ∫_{y ∈ (0,a]} ∫_{x ∈ (y,a]} F x y`.
* `sa16r_tri_int`: `(r,σ) ↦ ℓ (Γ σ (g r))` composed with `(x,y) ↦ (x', y)` is integrable on the triangle when
  `‖Γ σ‖ ≤ C σ^{-1/2}`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16R

lemma sa16r_tri_meas (a : ℝ) : MeasurableSet {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ a} := by
  refine (measurableSet_lt measurable_const measurable_snd).inter
    ((measurableSet_le measurable_snd measurable_fst).inter (measurableSet_le measurable_fst measurable_const))

lemma sa16r_tri_swap {F : ℝ → ℝ → ℝ} {a : ℝ}
    (hF : IntegrableOn (fun q : ℝ × ℝ => F q.1 q.2) {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ a}) :
    ∫ x in Ioc 0 a, ∫ y in Ioc 0 x, F x y = ∫ y in Ioc 0 a, ∫ x in Ioc y a, F x y := by
  set R : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ a} with hR
  set G : ℝ → ℝ → ℝ := fun x y => R.indicator (fun q : ℝ × ℝ => F q.1 q.2) (x, y) with hG
  have hGi : Integrable (Function.uncurry G) (volume.prod volume) := by
    have := (integrable_indicator_iff (sa16r_tri_meas a)).2 hF
    rw [← Measure.volume_eq_prod]
    exact this
  have hswap := integral_integral_swap hGi
  have hL : ∀ x : ℝ, ∫ y, G x y = (Ioc 0 a).indicator (fun x => ∫ y in Ioc 0 x, F x y) x := by
    intro x
    by_cases hx : x ∈ Ioc 0 a
    · rw [indicator_of_mem hx, ← integral_indicator measurableSet_Ioc]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hG, hR]
      by_cases hy : y ∈ Ioc 0 x
      · rw [indicator_of_mem hy, indicator_of_mem]
        exact ⟨hy.1, hy.2, hx.2⟩
      · rw [indicator_of_notMem hy, indicator_of_notMem]
        intro h; exact hy ⟨h.1, h.2.1⟩
    · rw [indicator_of_notMem hx]
      have : ∀ y, G x y = 0 := by
        intro y
        simp only [hG, hR]
        refine indicator_of_notMem ?_ _
        intro h; exact hx ⟨by linarith [h.1, h.2.1], h.2.2⟩
      simp [this]
  have hRr : ∀ y : ℝ, ∫ x, G x y = (Ioc 0 a).indicator (fun y => ∫ x in Ioc y a, F x y) y := by
    intro y
    by_cases hy : y ∈ Ioc 0 a
    · rw [indicator_of_mem hy, ← integral_indicator measurableSet_Ioc]
      refine integral_congr_ae ?_
      filter_upwards [(Set.countable_singleton y).ae_notMem (volume : Measure ℝ)] with x hxy
      simp only [hG, hR]
      by_cases hx : x ∈ Ioc y a
      · rw [indicator_of_mem hx, indicator_of_mem]
        exact ⟨hy.1, hx.1.le, hx.2⟩
      · rw [indicator_of_notMem hx, indicator_of_notMem]
        intro h
        refine hx ⟨lt_of_le_of_ne h.2.1 ?_, h.2.2⟩
        intro heq; exact hxy (by simpa using heq.symm)
    · rw [indicator_of_notMem hy]
      have : ∀ x, G x y = 0 := by
        intro x
        simp only [hG, hR]
        refine indicator_of_notMem ?_ _
        intro h; exact hy ⟨h.1, by linarith [h.2.1, h.2.2]⟩
      simp [this]
  simp only [hL, hRr] at hswap
  rw [integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc] at hswap
  exact hswap

lemma sa16r_tri_int {H : ℝ → ℝ → ℝ} {T c τ : ℝ} (hτ : τ ≤ T)
    (hc : ContinuousOn (fun q : ℝ × ℝ => H q.1 q.2) {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) T ∧ 0 < q.2 ∧ q.2 ≤ T})
    (hb : ∀ r ∈ Icc (0 : ℝ) T, ∀ σ ∈ Ioc (0 : ℝ) T, |H r σ| ≤ c * σ ^ (-(1 / 2 : ℝ)))
    {φ : ℝ × ℝ → ℝ} (hφ : Continuous φ)
    (hmem : ∀ q ∈ {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ τ}, φ q ∈ Icc (0 : ℝ) T) :
    IntegrableOn (fun q : ℝ × ℝ => H (φ q) q.2) {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ τ} := by
  set R : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ τ} with hR
  have hRm : MeasurableSet R := sa16r_tri_meas τ
  have hcont : ContinuousOn (fun q : ℝ × ℝ => H (φ q) q.2) R := by
    have hm : ContinuousOn (fun q : ℝ × ℝ => (φ q, q.2)) R :=
      (hφ.prodMk continuous_snd).continuousOn
    refine hc.comp hm (fun q hq => ⟨hmem q hq, hq.1, hq.2.1.trans (hq.2.2.trans hτ)⟩)
  have hbint : Integrable (fun q : ℝ × ℝ =>
      (Ioc (0 : ℝ) τ).indicator (fun _ => (1 : ℝ)) q.1 *
        (Ioc (0 : ℝ) τ).indicator (fun σ : ℝ => c * σ ^ (-(1 / 2 : ℝ))) q.2) (volume.prod volume) := by
    refine Integrable.mul_prod (f := fun x : ℝ => (Ioc (0 : ℝ) τ).indicator (fun _ => (1 : ℝ)) x)
      (g := fun σ : ℝ => (Ioc (0 : ℝ) τ).indicator (fun σ : ℝ => c * σ ^ (-(1 / 2 : ℝ))) σ) ?_ ?_
    · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioc
    · have hI : IntegrableOn (fun σ : ℝ => c * σ ^ (-(1 / 2 : ℝ))) (Ioc 0 τ) :=
        (sa16r_rpow_int τ).const_mul c
      exact hI.integrable_indicator measurableSet_Ioc
  rw [← Measure.volume_eq_prod] at hbint
  refine Integrable.mono' hbint.integrableOn (hcont.aestronglyMeasurable hRm) ?_
  rw [ae_restrict_iff' hRm]
  refine Filter.Eventually.of_forall fun q hq => ?_
  have h1 : q.1 ∈ Ioc (0 : ℝ) τ := ⟨hq.1.trans_le hq.2.1, hq.2.2⟩
  have h2 : q.2 ∈ Ioc (0 : ℝ) τ := ⟨hq.1, hq.2.1.trans hq.2.2⟩
  rw [indicator_of_mem h1, indicator_of_mem h2, one_mul, Real.norm_eq_abs]
  exact hb _ (hmem q hq) _ ⟨hq.1, hq.2.1.trans (hq.2.2.trans hτ)⟩

end HRS.Whole.AppendixA.Phase2SA16R
