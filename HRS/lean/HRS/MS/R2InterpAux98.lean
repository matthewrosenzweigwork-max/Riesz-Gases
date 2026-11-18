import HRS.MS.R2InterpAux97

/-!
# S10.2 (worker S10R), part 98 (packet F5m): `E`-valued assembly of the drift `bd` of the Itô representation
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d}

theorem s102_eucl_symm_sum {q : ℕ} (f : Fin q → ℝ) :
    (EuclideanSpace.equiv (Fin q) ℝ).symm f = ∑ i, f i • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  simp [Pi.single_apply]

theorem s102_integrableOn_E {q : ℕ} {s : Set ℝ} (G : Fin q → ℝ → ℝ) (hG : ∀ i, IntegrableOn (G i) s) :
    IntegrableOn (fun u => (EuclideanSpace.equiv (Fin q) ℝ).symm (fun i => G i u)) s := by
  have : (fun u => (EuclideanSpace.equiv (Fin q) ℝ).symm (fun i => G i u)) =
      fun u => ∑ i, G i u • EuclideanSpace.single i (1 : ℝ) := by
    funext u; exact s102_eucl_symm_sum _
  rw [this]
  exact integrable_finsetSum _ fun i _ => (hG i).smul_const _

theorem s102_prog_E {q : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ} (G : Fin q → ℝ → Ω → ℝ)
    (hG : ∀ i, IsProgressive ℱ (G i)) :
    IsProgressive ℱ (fun u ζ => (EuclideanSpace.equiv (Fin q) ℝ).symm (fun i => G i u ζ)) := by
  intro j
  exact (EuclideanSpace.equiv (Fin q) ℝ).symm.continuous.measurable.comp
    ((@measurable_pi_iff _ _ _ (Subtype.instMeasurableSpace.prod (ℱ j)) _).2 fun i => hG i j)

/-- The drift of the Itô representation. -/
def s102_bdE (C : WholeCoeff d) (m : ℝ) {T : ℝ} (hT : 0 < T) (L : ℕ) (sQ : ℝ) (μ : Measure (Euc d)) {N : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) :
    ℝ → Ω → EuclideanSpace ℝ (Fin (s102_q d L)) :=
  fun u ζ => (EuclideanSpace.equiv (Fin (s102_q d L)) ℝ).symm (fun i => s102_bdc C m hT L sQ μ P X i u ζ)

theorem s102_bdE_locL1 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {m T : ℝ} {r : ℕ}
    {c : MultiIndex d → ℝ} (hS : S102Std C m T r c) (hT : 0 < T) (L : ℕ) {β p K M Lr : ℝ} (hβ : 0 < β) (hp : 1 < p)
    {ρ : Euc d → ℝ} (hρR : IsRound2Density d s M Lr ρ) {N : ℕ} (hN : 2 ≤ N) {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsProgressive ℱ (ofNNRealTime X))
    (hdens : ∀ r ∈ Icc (0 : ℝ) T, HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) (P.map (X r.toNNReal))) :
    IsProgressiveLocL1 P ℱ (s102_bdE C m hT L s (HRS.Whole.withDensityReal ρ) P X) := by
  have h := fun i => s102_bdc_prog_int hd hs0 hs hS hT L hβ hp hρR hN P X hX hdens i
  refine ⟨s102_prog_E _ fun i => (h i).1, fun T' => ?_⟩
  have hall : ∀ᵐ ζ ∂P, ∀ i, IntegrableOn (fun u => s102_bdc C m hT L s (HRS.Whole.withDensityReal ρ) P X i u ζ)
      (Icc 0 T') := by
    rw [ae_all_iff]
    intro i
    filter_upwards [(h i).2] with ζ hζ using hζ T'
  filter_upwards [hall] with ζ hζ
  exact s102_integrableOn_E _ hζ

end HRS.MS.R2Interp

end
