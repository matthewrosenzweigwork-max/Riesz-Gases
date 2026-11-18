import HRS.MS.S21G2_S12B

/-!
# S21G2 S12 (part D) -- LLN in probability on `P0` and index-shift lemmas (R26-T3.S12)

Helper names carry the prefix `s21g2_s12_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s21g2_s12_lln {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    {h : E → ℝ} (hm : Measurable h) (hi : Integrable h μ) :
    TendstoInMeasure (Measure.infinitePi fun _ : ℕ => μ)
      (fun (N : ℕ) (ω : ℕ → E) => (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, h (ω k)) atTop
      (fun _ => ∫ x, h x ∂μ) := by
  set P0 : Measure (ℕ → E) := Measure.infinitePi fun _ : ℕ => μ with hP0
  have hlaw : ∀ k, P0.map (fun ω => ω k) = μ := fun k => Measure.infinitePi_map_eval _ k
  have hind : iIndepFun (fun (k : ℕ) (ω : ℕ → E) => h (ω k)) P0 :=
    iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ => h) (fun _ => hm)
  have hid : ∀ k : ℕ, IdentDistrib (fun ω : ℕ → E => h (ω k)) (fun ω : ℕ → E => h (ω 0)) P0 P0 := fun k => by
    refine ⟨(hm.comp (measurable_pi_apply k)).aemeasurable, (hm.comp (measurable_pi_apply 0)).aemeasurable, ?_⟩
    have e : ∀ k : ℕ, P0.map (fun ω : ℕ → E => h (ω k)) = μ.map h := fun k => by
      rw [← hlaw k, Measure.map_map hm (measurable_pi_apply k)]; rfl
    rw [e k, e 0]
  have hint : Integrable (fun ω : ℕ → E => h (ω 0)) P0 := by
    refine (integrable_map_measure (f := fun ω : ℕ → E => ω 0) hm.aestronglyMeasurable
      (measurable_pi_apply 0).aemeasurable).1 ?_
    rw [hlaw 0]; exact hi
  have hmean : P0[fun ω : ℕ → E => h (ω 0)] = ∫ x, h x ∂μ := by
    have := integral_map (μ := P0) (φ := fun ω : ℕ → E => ω 0) (f := h)
      (measurable_pi_apply 0).aemeasurable hm.aestronglyMeasurable
    rw [hlaw 0] at this; exact this.symm
  have hae := strong_law_ae (μ := P0) (fun k ω => h (ω k)) hint
    (fun i j hij => hind.indepFun hij) hid
  refine tendstoInMeasure_of_tendsto_ae (fun N => ?_) ?_
  · exact ((Finset.measurable_sum _ fun k _ => hm.comp (measurable_pi_apply k)).const_mul _).aestronglyMeasurable
  · filter_upwards [hae] with ω hω
    simpa [hmean] using hω

theorem s21g2_s12_shift_in {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V : Type*} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → V}
    {X : ℕ → Ω → V} (h : TendstoInDistribution X atTop Z (fun _ => P) P') :
    TendstoInDistribution (fun N => X (N + 1)) atTop Z (fun _ => P) P' :=
  ⟨fun N => h.forall_aemeasurable _, h.aemeasurable_limit,
    h.tendsto.comp (tendsto_add_atTop_nat 1)⟩

theorem s21g2_s12_shift_out {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)}
    [∀ N, IsProbabilityMeasure (P N)]
    {V : Type*} [TopologicalSpace V] [MeasurableSpace V] [OpensMeasurableSpace V]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Z : Ω' → V}
    {F : ∀ N, Ω N → V} (h0 : AEMeasurable (F 0) (P 0))
    (h : TendstoInDistribution (fun N => F (N + 1)) atTop Z (fun N => P (N + 1)) P') :
    TendstoInDistribution F atTop Z P P' := by
  refine ⟨fun N => ?_, h.aemeasurable_limit, ?_⟩
  · cases N with
    | zero => exact h0
    | succ N => exact h.forall_aemeasurable N
  · exact (tendsto_add_atTop_iff_nat (f := fun N => (⟨(P N).map (F N), inferInstance⟩ :
      ProbabilityMeasure V)) 1).1 h.tendsto

/-- Retargeting the limit variable along a measurable map of the limit space. -/
theorem s21g2_s12_retarget {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] {P : ∀ N, Measure (Ω N)}
    [∀ N, IsProbabilityMeasure (P N)] {V W : Type*} [TopologicalSpace W] [MeasurableSpace W]
    [OpensMeasurableSpace W] [MeasurableSpace V]
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Z : Ω' → V} (hZ : AEMeasurable Z P') {Φ : V → W} (hΦ : Measurable Φ)
    {F : ∀ N, Ω N → W} (G : Measure V) (hG : G = P'.map Z) [IsProbabilityMeasure G]
    (h : TendstoInDistribution F atTop (fun ω => Φ (Z ω)) P P') :
    TendstoInDistribution F atTop Φ P G := by
  refine ⟨h.forall_aemeasurable, hΦ.aemeasurable, ?_⟩
  have e : G.map Φ = P'.map (fun ω => Φ (Z ω)) := by
    rw [hG]; exact AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hZ
  convert h.tendsto using 3
  congr 1
  exact Subtype.ext e

end HRS.MS.R26T3
