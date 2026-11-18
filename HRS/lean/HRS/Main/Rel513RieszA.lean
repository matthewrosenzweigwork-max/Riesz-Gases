import HRS.Main.Rel513Spec
import HRS.Equilibrium.Q84dAuxF
import HRS.Equilibrium.Q84dAuxE

/-!
# HRS.Main.Rel513RieszA -- packet rel513, part 1: `P_{N,β}` is a probability measure

Proofs (relocation pattern) of `canonicalGibbs_isProbability` and `canonicalPartition_pos_riesz`
of `Rel513Spec`.  The `Rel513Spec` declarations themselves are open statements (unproved) and are NOT used.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Main

variable {d : ℕ}

theorem rel513_integrable_of_pos (g V : Torus d → ℝ) (N : ℕ) (β : ℝ)
    (hZ : 0 < canonicalPartition g V N β) :
    Integrable (fun X : Config d N => Real.exp (-β * canonicalHamiltonian g V X)) := by
  by_contra h
  unfold canonicalPartition at hZ
  rw [integral_undef h] at hZ
  exact lt_irrefl _ hZ

theorem canonicalGibbs_isProbability_proof (g V : Torus d → ℝ) (N : ℕ) (β : ℝ)
    (hZ : 0 < canonicalPartition g V N β) :
    IsProbabilityMeasure (canonicalGibbs g V N β) := by
  have hint := rel513_integrable_of_pos g V N β hZ
  refine ⟨?_⟩
  unfold canonicalGibbs
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul]
  have := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)
  unfold canonicalPartition at hZ ⊢
  rw [← this]
  exact ENNReal.inv_mul_cancel (by simpa using hZ) ENNReal.ofReal_ne_top

example := (@canonicalGibbs_isProbability_proof : type_of% @canonicalGibbs_isProbability)

theorem canonicalPartition_pos_riesz_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {N : ℕ} (hN : 1 ≤ N) :
    0 < canonicalPartition (periodicRiesz d s) V N β := by
  obtain ⟨B, hB0, hB⟩ := HRS.Q84d.q84d_exists_lower hd hs0 hsd
  obtain ⟨Vm, hVm⟩ := HRS.Q84d.q84d_exists_bound_smooth hV
  have hlow : ∀ X : Config d N, -((N : ℝ) * Vm + N * B) ≤
      canonicalHamiltonian (periodicRiesz d s) V X := fun X => by
    have := HRS.Q84d.q84d_H_lower hB0 hB hVm hN (∅ : Finset (Fin N × Fin N))
      (Finset.empty_subset _) X
    simpa using this
  have hgm : Measurable (periodicRiesz d s : Torus d → ℝ) :=
    CoercAux.measurable_periodicRiesz_one (by omega) hs0 hsd
  have hVc : Measurable V := HRS.Q84d.q84d_measurable_V hV
  exact HRS.Q84d.q84d_Z_pos hgm hVc hlow hβ.le

example := (@canonicalPartition_pos_riesz_proof : type_of% @canonicalPartition_pos_riesz)

end HRS.Main

end
