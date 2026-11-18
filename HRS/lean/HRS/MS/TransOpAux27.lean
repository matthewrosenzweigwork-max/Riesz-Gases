import HRS.MS.TransOpAux26
import HRS.MS.MovSchAux17

/-!
# S611 packet P5d: `mov_translated_prepared` from S2.1 (ii)

`mov_translated_prepared_of_S21 : type_of% @whole_space_prepared → type_of% @mov_translated_prepared`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_fluc_pointwise (m : ℕ) (hm : 1 ≤ m) (hdm : (d : ℝ) < m) {N : ℕ} (hN : 1 ≤ N) (q : ℝ)
    (b : Euc d) {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N) (ρ₀ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ₀)
    (ζ : Ω) (t : ℝ) (ht : 0 ≤ t) (σ : ℝ) :
    σ • OscDual.ofMeasureDiff (m : ℝ) (HRS.Whole.empirical (X t.toNNReal ζ))
        (HRS.Whole.withDensityReal (movTranslatedDensity q b ρ₀ t)) =
      s611_Lam m hm (movShift q b t)
        (σ • OscDual.ofMeasureDiff (m : ℝ)
          (HRS.Whole.empirical (fun i => X t.toNNReal ζ i - movShift q b (t.toNNReal : ℝ))) (HRS.Whole.withDensityReal ρ₀)) := by
  have ht' : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht
  rw [ht']
  have := s611_fluc_shift m hm hdm hN σ (fun i => X t.toNNReal ζ i - movShift q b t) ρ₀ hρ (movShift q b t)
  simp only [sub_add_cancel] at this
  exact this

theorem s611_map_unshift (μ : Measure (Euc d)) (b : Euc d) :
    (μ.map (fun x => x + b)).map (fun x => x - b) = μ := by
  rw [Measure.map_map (measurable_sub_const b) (measurable_add_const b)]
  have : ((fun x : Euc d => x - b) ∘ fun x => x + b) = id := by funext x; simp
  rw [this, Measure.map_id]

theorem s611_prep_law (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β q : ℝ} (hβ : 0 < β) (hq : 0 < q)
    (b : Euc d) {γ : ℝ} (hγ : 0 ≤ γ) {ρ₀ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ₀) {N : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X₀ : Ω → EucConfig d N)
    (hX₀m : AEMeasurable X₀ P)
    (hprep : MovPrepared d s N γ (HRS.Whole.withDensityReal (movTranslatedDensity q b ρ₀ 0)) (P.map X₀)) :
    P.map (fun ζ i => X₀ ζ i - b) =
      HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N γ (HRS.Whole.withDensityReal ρ₀) := by
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ₀) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hb0 : movShift q b 0 = b := by simp [movShift]
  have hmu : HRS.Whole.withDensityReal (movTranslatedDensity q b ρ₀ 0) = movTranslate b (HRS.Whole.withDensityReal ρ₀) := by
    show HRS.Whole.withDensityReal (fun x => ρ₀ (x - movShift q b 0)) = _
    rw [hb0]
    exact (HRS.MS.A0.a0_map_withDensity ρ₀ b).symm
  have hsh : Measurable (fun Z : EucConfig d N => fun i => Z i - b) := s611_measurable_unshift b
  have hmap : P.map (fun ζ i => X₀ ζ i - b) = (P.map X₀).map (fun Z : EucConfig d N => fun i => Z i - b) :=
    (AEMeasurable.map_map_of_aemeasurable hsh.aemeasurable hX₀m).symm
  rw [hmap]
  rcases hprep with ⟨h0, hP⟩ | ⟨hpos, hP⟩
  · subst h0
    rw [HRS.Whole.modulatedGibbs_zero, hP, hmu]
    haveI : IsProbabilityMeasure (movTranslate b (HRS.Whole.withDensityReal ρ₀)) := by
      unfold movTranslate; exact inferInstance
    have hmp : ∀ _ : Fin N, MeasurePreserving (fun x : Euc d => x - b)
        (movTranslate b (HRS.Whole.withDensityReal ρ₀)) (HRS.Whole.withDensityReal ρ₀) := fun _ =>
      ⟨measurable_sub_const b, s611_map_unshift _ b⟩
    exact (measurePreserving_pi (fun _ : Fin N => movTranslate b (HRS.Whole.withDensityReal ρ₀))
      (fun _ : Fin N => HRS.Whole.withDensityReal ρ₀) hmp).map_eq
  · rw [hP, hmu, (HRS.Whole.mov_translation_proof hd hs0 hsd β q hβ hq b).2.2.1 N γ hpos (HRS.Whole.withDensityReal ρ₀) inferInstance]
    rw [Measure.map_map hsh (s611_measurable_shift b)]
    have : ((fun Z : EucConfig d N => fun i => Z i - b) ∘ fun (X : EucConfig d N) i => X i + b) = id := by
      funext Y i; simp
    rw [this, Measure.map_id]

end HRS.MS.TransOp

end
