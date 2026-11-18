import HRS.MS.Fp81S21GaussianConditioningFinite
import HRS.MS.Fp81S21GaussianIncrementAdapted3

/-! Packet 36: integrable finite approximants retaining the past sigma-algebra.
The dense-set version also permits algebraic tensor values. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology TopologicalSpace Set
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21

/-- Simple approximants can take values in any separable dense set containing
zero. Integrability, rather than boundedness, suffices for L¹ convergence. -/
theorem fp81s21_past_simple_dense_approx
    {Ω E : Type*} [m₀ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) (f : Ω → E) (hf : Integrable f P)
    (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (hfm : AEStronglyMeasurable[m] f P)
    (s : Set E) [SeparableSpace s] (hs : Dense s) (hzero : (0 : E) ∈ s) :
    ∃ F : ℕ → @SimpleFunc Ω m E,
      (∀ n ω, F n ω ∈ s) ∧ (∀ n, Integrable (F n) P) ∧
      Tendsto (fun n => ∫ ω, ‖F n ω - f ω‖ ∂P) atTop (𝓝 0) := by
  letI : MeasurableSpace Ω := m₀
  let g := hfm.mk f
  have hg : StronglyMeasurable[m] g := hfm.stronglyMeasurable_mk
  have hgi : Integrable g P := hf.congr hfm.ae_eq_mk
  let F : ℕ → @SimpleFunc Ω m E :=
    @SimpleFunc.approxOn E Ω _ _ _ m g hg.measurable s 0 hzero _
  have hFi (n : ℕ) : Integrable (F n) P :=
    SimpleFunc.integrable_approxOn (hg.mono hm).measurable hgi hzero
      (integrable_zero _ _ _) n
  have hL : Tendsto (fun n => ∫⁻ ω, ‖F n ω - g ω‖ₑ ∂P) atTop (𝓝 0) := by
    exact SimpleFunc.tendsto_approxOn_L1_enorm (hg.mono hm).measurable hzero
      (Eventually.of_forall fun ω => hs (g ω)) (by simpa using hgi.2)
  have hreal : Tendsto (fun n => ∫ ω, ‖F n ω - g ω‖ ∂P) atTop (𝓝 0) := by
    convert (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL using 1
    · funext n
      exact integral_norm_eq_lintegral_enorm (f := fun ω => F n ω - g ω)
        ((hFi n).aestronglyMeasurable.sub hgi.1)
    · simp
  refine ⟨F, ?_, hFi, ?_⟩
  · letI : MeasurableSpace Ω := m
    exact fun n ω => SimpleFunc.approxOn_mem hg.measurable hzero n ω
  · have he (n : ℕ) : (∫ ω, ‖F n ω - f ω‖ ∂P) = ∫ ω, ‖F n ω - g ω‖ ∂P := by
      apply integral_congr_ae
      filter_upwards [hfm.ae_eq_mk] with ω hω
      rw [hω]
    simpa only [he] using hreal

/-- A past-simple function is exactly a finite sum with integrable indicator
coefficients. The directions retain any pointwise constraint on its values. -/
theorem fp81s21_past_simple_finite_sum
    {Ω E : Type*} [m₀ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) [IsFiniteMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (F : @SimpleFunc Ω m E)
    (s : Set E) (hs : ∀ ω, F ω ∈ s) :
    ∃ (k : ℕ) (h : Fin k → E) (c : Fin k → Ω → ℝ),
      (∀ i, h i ∈ s) ∧ (∀ i, Integrable (c i) P) ∧
      (∀ i, AEStronglyMeasurable[m] (c i) P) ∧
      ∀ ω, (∑ i, c i ω • h i) = F ω := by
  letI : MeasurableSpace Ω := m₀
  let range : Finset E := @SimpleFunc.range Ω E m F
  let e := Fintype.equivFin range
  let h : Fin (Fintype.card range) → E := fun i => (e.symm i).1
  let c : Fin (Fintype.card range) → Ω → ℝ := fun i =>
    (F ⁻¹' {h i}).indicator (fun _ => 1)
  have hc (i) : Integrable (c i) P :=
    (integrable_const (1 : ℝ)).indicator (hm _ (@SimpleFunc.measurableSet_fiber Ω E m F (h i)))
  have hcm (i) : AEStronglyMeasurable[m] (c i) P :=
    (stronglyMeasurable_const.indicator (@SimpleFunc.measurableSet_fiber Ω E m F (h i))).aestronglyMeasurable
  refine ⟨_, h, c, ?_, hc, hcm, ?_⟩
  · intro i
    obtain ⟨ω, hω⟩ := (@SimpleFunc.mem_range Ω E m F _).1 (e.symm i).2
    simpa only [h, ← hω] using hs ω
  · intro ω
    let i₀ := e ⟨F ω, @SimpleFunc.mem_range_self Ω E m F ω⟩
    have hh : h i₀ = F ω := by simp [h, i₀]
    have hinj : Function.Injective h := Subtype.val_injective.comp e.symm.injective
    rw [Finset.sum_eq_single i₀]
    · simp [c, hh]
    · intro j _ hj
      have hne : F ω ≠ h j := by
        intro he
        exact hj (hinj (he.symm.trans hh.symm))
      simp [c, hne]
    · simp

/-- Finite past-measurable directions in a prescribed dense set approximate
any integrable past-measurable random vector, with the exact L¹ error norm. -/
theorem fp81s21_past_finite_dense_approx
    {Ω E : Type*} [m₀ : MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → E) (hf : Integrable f P)
    (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (hfm : AEStronglyMeasurable[m] f P)
    (s : Set E) [SeparableSpace s] (hs : Dense s) (hzero : (0 : E) ∈ s) :
    ∃ (k : ℕ → ℕ) (h : ∀ n, Fin (k n) → E) (c : ∀ n, Fin (k n) → Ω → ℝ),
      (∀ n i, h n i ∈ s) ∧ (∀ n i, Integrable (c n i) P) ∧
      (∀ n i, AEStronglyMeasurable[m] (c n i) P) ∧
      Tendsto (fun n => ∫ ω, ‖(∑ i, c n i ω • h n i) - f ω‖ ∂P)
        atTop (𝓝 0) := by
  letI : MeasurableSpace Ω := m₀
  obtain ⟨F, hFs, _, hlim⟩ := fp81s21_past_simple_dense_approx P f hf m hm hfm s hs hzero
  choose k h c hh hc hcm he using
    fun n => fp81s21_past_simple_finite_sum P m hm (F n) s (hFs n)
  exact ⟨k, h, c, hh, hc, hcm, by simpa only [he] using hlim⟩

#print axioms fp81s21_past_simple_dense_approx
#print axioms fp81s21_past_simple_finite_sum
#print axioms fp81s21_past_finite_dense_approx
end HRS.Fp81.S21
end
