import HRS.MS.Fp81S21WindowSupMeas4

/-! Continuity and fixed-time measurability of the initial coordinate. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.S21 HRS.MS.CovMeas

/-- The initial coordinate is continuous on the window and measurable at
all its fixed times. -/
theorem fp81s21_initial_coordinate_regular
    {d N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N)
    {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {b : ℝ} (hb : b ∈ Icc (0 : ℝ) T)
    (hX : Measurable (X b.toNNReal)) (hN : 0 < N) (α : MultiIndex d) :
    (∀ ω, ContinuousOn (fun t => s102_zf P X ω b
      (propagatorW C b t (oscTestFun m α))) (Icc b T)) ∧
    (∀ t ∈ Icc b T, Measurable (fun ω => s102_zf P X ω b
      (propagatorW C b t (oscTestFun m α)))) := by
  classical
  let q : ℝ → Euc d → ℝ := fun s x => s101Th C m T b s α x
  have hq : Measurable (Function.uncurry q) :=
    fp81s21_s101Th_joint_measurable hD hb α
  have hqmeas (s : ℝ) : Measurable (q s) :=
    hq.comp (measurable_const.prodMk measurable_id)
  let g : ℝ → Ω → ℝ := fun s ω => s102_zf P X ω b (q s)
  have hg : Measurable (Function.uncurry g) :=
    fp81s21_s102_zf_family_measurable P X b hX hN q hq
  haveI : IsProbabilityMeasure (P.map (X b.toNNReal)) :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance
  let μ : Measure (Euc d) := HRS.Whole.meanEmpirical (P.map (X b.toNNReal))
  haveI : IsProbabilityMeasure μ := HRS.Whole.meanEmpirical_isProbabilityMeasure _ (by omega)
  have hc : 0 ≤ c α := hD.nonneg α
  have hgint (ω : Ω) : IntegrableOn (fun s => g s ω) (Icc b T) := by
    let e : ℝ → ℝ × Ω := fun s => (s, ω)
    have he : Measurable e := measurable_id.prodMk measurable_const
    have hsection : Measurable (fun s => g s ω) := by
      change Measurable ((Function.uncurry g) ∘ e)
      exact hg.comp he
    refine Measure.integrableOn_of_bounded (M := 4 * Real.sqrt N * c α)
      measure_Icc_lt_top.ne hsection.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]
      exact fp81s21_window_s102_zf_abs_bound P X b hX hN μ (hqmeas s) hc
        (fun x => s101_th_bound hD hb s α x) ω
  constructor
  · intro ω
    have hi : IntegrableOn (fun s => g s ω) (uIcc b T) := by
      simpa [uIcc_of_le (hb.2)] using hgint ω
    have hcont : ContinuousOn (fun t => s102_zf P X ω b
        (propagatorW C b b (oscTestFun m α)) + ∫ s in b..t, g s ω) (Icc b T) := by
      have h := intervalIntegral.continuousOn_primitive_interval hi
      exact continuousOn_const.add (by simpa [uIcc_of_le hb.2] using h)
    apply hcont.congr
    intro t ht
    exact fp81s21_window_s102_zf_ftc P X hD hb ht hX hN α ω
  · intro t ht
    let f : Euc d → ℝ := propagatorW C b t (oscTestFun m α)
    have hf : Measurable f := (hD.smoothU α b hb t ht).continuous.measurable
    have hfam := fp81s21_s102_zf_family_measurable P X b hX hN
      (fun _ : ℝ => f) (hf.comp measurable_snd)
    let e : Ω → ℝ × Ω := fun ω => (b, ω)
    have he : Measurable e := measurable_const.prodMk measurable_id
    change Measurable ((fun z : ℝ × Ω => s102_zf P X z.2 b (f)) ∘ e)
    exact hfam.comp he

#print axioms fp81s21_initial_coordinate_regular
end HRS.Fp81.S21
end
