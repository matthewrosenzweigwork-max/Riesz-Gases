import HRS.MS.Fp81S21CenteredAdapter
import HRS.MS.Fp81S21WassersteinCoupling
import HRS.MS.Fp81S21NoisePath6

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open HRS HRS.Whole

namespace HRS.Fp81.S21

/-- The rate condition used by the unit L profile: every value is nonnegative
and the real sequence tends to zero. -/
def fp81s21_NonnegativeVanishing (d : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ d n) ∧ Tendsto d atTop (𝓝 0)

/-- A coupling of path laws preserves the sixth moment assumptions of each
marginal. The output fields are exactly the integrability and integral bounds
consumed by the cutoff lifting theorem. -/
theorem fp81s21_jointL_coupling_sixth_marginals
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B]
    (P Q : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (π : Measure (B × B)) [IsProbabilityMeasure π]
    (hπ₁ : π.map Prod.fst = P) (hπ₂ : π.map Prod.snd = Q)
    (M : ℝ)
    (hP6 : Integrable (fun x : B => ‖x‖ ^ 6) P)
    (hQ6 : Integrable (fun x : B => ‖x‖ ^ 6) Q)
    (hPM : ∫ x, ‖x‖ ^ 6 ∂P ≤ M)
    (hQM : ∫ x, ‖x‖ ^ 6 ∂Q ≤ M) :
    Integrable (fun z : B × B => ‖z.1‖ ^ 6) π ∧
      Integrable (fun z : B × B => ‖z.2‖ ^ 6) π ∧
      (∫ z, ‖z.1‖ ^ 6 ∂π) ≤ M ∧
      (∫ z, ‖z.2‖ ^ 6 ∂π) ≤ M := by
  have hPmap : Integrable (fun x : B => ‖x‖ ^ 6) (π.map Prod.fst) := by
    rw [hπ₁]
    exact hP6
  have hQmap : Integrable (fun x : B => ‖x‖ ^ 6) (π.map Prod.snd) := by
    rw [hπ₂]
    exact hQ6
  have hfst : Integrable (fun z : B × B => ‖z.1‖ ^ 6) π := by
    have h := (integrable_map_measure
      (by fun_prop : AEStronglyMeasurable (fun x : B => ‖x‖ ^ 6) (π.map Prod.fst))
      measurable_fst.aemeasurable).mp hPmap
    simpa only [Function.comp_def] using h
  have hsnd : Integrable (fun z : B × B => ‖z.2‖ ^ 6) π := by
    have h := (integrable_map_measure
      (by fun_prop : AEStronglyMeasurable (fun x : B => ‖x‖ ^ 6) (π.map Prod.snd))
      measurable_snd.aemeasurable).mp hQmap
    simpa only [Function.comp_def] using h
  have hfstInt :
      (∫ z, ‖z.1‖ ^ 6 ∂π) = ∫ x, ‖x‖ ^ 6 ∂(π.map Prod.fst) := by
    symm
    simpa only [Function.comp_def] using
      (integral_map measurable_fst.aemeasurable hPmap.aestronglyMeasurable)
  have hsndInt :
      (∫ z, ‖z.2‖ ^ 6 ∂π) = ∫ x, ‖x‖ ^ 6 ∂(π.map Prod.snd) := by
    symm
    simpa only [Function.comp_def] using
      (integral_map measurable_snd.aemeasurable hQmap.aestronglyMeasurable)
  refine ⟨hfst, hsnd, ?_, ?_⟩
  · rw [hfstInt, hπ₁]
    exact hPM
  · rw [hsndInt, hπ₂]
    exact hQM

/-- Restricting both coordinates of two raw path laws by the same physical
window map cannot increase their W1 distance. The final a.e. equalities
identify the restricted long windows with the requested raw windows. -/
theorem fp81s21_jointL_law_restrict_wasserstein
    {d : ℕ} {m H T u : ℝ} (hu : 0 ≤ u) (hH : u + T ≤ H)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Q : Measure Ω'} [IsProbabilityMeasure Q]
    (Y : Ω → OscPath d m H) (Z : Ω' → OscPath d m H)
    (hY : AEMeasurable Y P) (hZ : AEMeasurable Z Q)
    (Y' : Ω → OscPath d m T) (Z' : Ω' → OscPath d m T)
    (hYr : (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction hu hH (Y ω))
      =ᵐ[P] Y')
    (hZr : (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction hu hH (Z ω))
      =ᵐ[Q] Z') :
    wassersteinE 1 (law P Y') (law Q Z') ≤
      wassersteinE 1 (law P Y) (law Q Z) := by
  have hcontract := fp81s21_law_restrict_wasserstein hu hH Y Z hY hZ
  have hLawY :
      law P (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction hu hH (Y ω)) =
        law P Y' := Measure.map_congr hYr
  have hLawZ :
      law Q (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction hu hH (Z ω)) =
        law Q Z' := Measure.map_congr hZr
  rw [← hLawY, ← hLawZ]
  exact hcontract

#print axioms fp81s21_jointL_coupling_sixth_marginals
#print axioms fp81s21_jointL_law_restrict_wasserstein

end HRS.Fp81.S21

end
