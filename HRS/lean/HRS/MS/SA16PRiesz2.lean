import HRS.MS.SA16PRiesz1

/-!
# SA16P, part 2: the signed measure `A ↦ ℓ(1_A h)` and its Radon-Nikodym density

For a bounded linear functional `ℓ` on `L^p` (`1 < p`) and a positive weight `h ∈ L^p` the set function
`A ↦ ℓ(1_A h)` is a signed measure (σ-additivity by `sa16p_hasSum_ind`), absolutely continuous w.r.t. `μ`; the
Radon-Nikodym theorem for signed measures gives a measurable `G ∈ L^1(μ)` with `∫_A G = ℓ(1_A h)`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16P

section Nu
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {h : α → ℝ} (hh : MemLp h (ENNReal.ofReal p) μ)
  (ℓ : Lp ℝ (ENNReal.ofReal p) μ →L[ℝ] ℝ)

open Classical in
/-- the signed measure `A ↦ ℓ(1_A h)` -/
def sa16p_nu (hp : 1 < p) : SignedMeasure α where
  measureOf' A := if hA : MeasurableSet A then ℓ (sa16p_ind hh A hA) else 0
  empty' := by
    rw [dif_pos MeasurableSet.empty, sa16p_ind_empty]
    simp
  not_measurable' A hA := dif_neg hA
  m_iUnion' f hf hd := by
    simp only [dif_pos (hf _), dif_pos (MeasurableSet.iUnion hf)]
    exact ℓ.hasSum (sa16p_hasSum_ind hh hp hf hd)

open Classical in
lemma sa16p_nu_apply (hp : 1 < p) {A : Set α} (hA : MeasurableSet A) :
    sa16p_nu hh ℓ hp A = ℓ (sa16p_ind hh A hA) := by
  show (if hA : MeasurableSet A then ℓ (sa16p_ind hh A hA) else 0) = _
  rw [dif_pos hA]

lemma sa16p_nu_ac (hp : 1 < p) : sa16p_nu hh ℓ hp ≪ᵥ μ.toENNRealVectorMeasure := by
  intro A hA0
  by_cases hAm : MeasurableSet A
  · rw [Measure.toENNRealVectorMeasure_apply_measurable hAm] at hA0
    rw [sa16p_nu_apply hh ℓ hp hAm]
    have : sa16p_ind hh A hAm = 0 := by
      apply Lp.ext
      filter_upwards [sa16p_ind_coe hh A hAm, Lp.coeFn_zero ℝ (ENNReal.ofReal p) μ,
        measure_eq_zero_iff_ae_notMem.1 hA0] with x h1 h2 h3
      rw [h1, h2]
      simp [Set.indicator_of_notMem h3]
    rw [this, map_zero]
  · exact (sa16p_nu hh ℓ hp).not_measurable' hAm

/-- the Radon-Nikodym density of `sa16p_nu` -/
def sa16p_G (hp : 1 < p) : α → ℝ := (sa16p_nu hh ℓ hp).rnDeriv μ

lemma sa16p_G_measurable (hp : 1 < p) : Measurable (sa16p_G hh ℓ hp) :=
  SignedMeasure.measurable_rnDeriv _ _

lemma sa16p_G_integrable (hp : 1 < p) : Integrable (sa16p_G hh ℓ hp) μ :=
  SignedMeasure.integrable_rnDeriv _ _

lemma sa16p_G_setIntegral (hp : 1 < p) {A : Set α} (hA : MeasurableSet A) :
    ∫ x in A, sa16p_G hh ℓ hp x ∂μ = ℓ (sa16p_ind hh A hA) := by
  have := SignedMeasure.withDensityᵥ_rnDeriv_eq (sa16p_nu hh ℓ hp) μ (sa16p_nu_ac hh ℓ hp)
  have h2 := congrArg (fun v : SignedMeasure α => v A) this
  have hint : Integrable ((sa16p_nu hh ℓ hp).rnDeriv μ) μ := SignedMeasure.integrable_rnDeriv _ _
  rw [withDensityᵥ_apply hint hA, sa16p_nu_apply hh ℓ hp hA] at h2
  exact h2

end Nu

end HRS.Whole.AppendixA.Phase2SA16P
