/-
# HRS.Equilibrium.Q84dAuxF — packet Q84d: a.e. measurability on `Config` and the Gibbs-weighted
integrability criterion
-/
import HRS.Equilibrium.Q84dAuxE

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84d_pair_mp {i j : Fin N} (hij : i ≠ j) :
    MeasurePreserving (fun X : Config d N => (X i, X j)) volume
      (volume : Measure (Torus d × Torus d)) :=
  ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), by
    rw [Measure.volume_eq_prod]
    exact pi_map_pair (volume : Measure (Torus d)) hij⟩

theorem q84d_aesm_pair {b : Torus d → Torus d → ℝ}
    (hb : AEStronglyMeasurable (fun p : Torus d × Torus d => b p.1 p.2) volume)
    {i j : Fin N} (hij : i ≠ j) :
    AEStronglyMeasurable (fun X : Config d N => b (X i) (X j)) volume :=
  hb.comp_quasiMeasurePreserving (q84d_pair_mp hij).quasiMeasurePreserving

theorem q84d_aesm_pairSum {b : Torus d → Torus d → ℝ}
    (hb : AEStronglyMeasurable (fun p : Torus d × Torus d => b p.1 p.2) volume) :
    AEStronglyMeasurable (fun X : Config d N => pairSumOrdered b X) volume := by
  unfold pairSumOrdered
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => Finset.aestronglyMeasurable_fun_sum _ fun j hj => ?_
  exact q84d_aesm_pair hb (Finset.ne_of_mem_erase hj).symm

theorem q84d_ae_not_collision (hd : 1 ≤ d) :
    ∀ᵐ X ∂(volume : Measure (Config d N)), X ∉ collisionSet d N := by
  have h : ∀ i j : Fin N, ∀ᵐ X ∂(volume : Measure (Config d N)), i ≠ j → X i ≠ X j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun X h => absurd hij h
    · have := (q84d_pair_mp (d := d) (N := N) hij).quasiMeasurePreserving.ae (q84d_ae_ne_diag hd)
      filter_upwards [this] with X hX _ using hX
  have h2 : ∀ᵐ X ∂(volume : Measure (Config d N)), ∀ i j : Fin N, i ≠ j → X i ≠ X j := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    exact h i j
  filter_upwards [h2] with X hX
  rintro ⟨i, j, hij, hXij⟩
  exact hX i j hij hXij

section Criterion

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
include hd hcrit

theorem q84d_hlow {V : Torus d → ℝ} (hV : Torus.IsSmooth V) (hN : 1 ≤ N) :
    ∃ c : ℝ, ∀ X : Config d N, -c ≤ canonicalHamiltonian (periodicRiesz d s) V X := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨B, hB0, hB⟩ := q84d_exists_lower hd hs0 hsd
  obtain ⟨Vm, hVm⟩ := q84d_exists_bound_smooth hV
  refine ⟨(N : ℝ) * Vm + N * B, fun X => ?_⟩
  have := q84d_H_lower hB0 hB hVm hN (∅ : Finset (Fin N × Fin N)) (Finset.empty_subset _) X
  simpa using this

theorem q84d_measurable_g : Measurable (periodicRiesz d s : Torus d → ℝ) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  exact CoercAux.measurable_periodicRiesz_one (by omega) hs0 hsd

omit hd hcrit in
theorem q84d_measurable_V {V : Torus d → ℝ} (hV : Torus.IsSmooth V) : Measurable V :=
  (Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV).continuous).measurable

theorem q84d_isProb {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (hN : 1 ≤ N) :
    IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
  obtain ⟨c, hc⟩ := q84d_hlow hd hcrit hV hN
  exact q84d_gibbs_isProb (q84d_measurable_g hd hcrit) (q84d_measurable_V hV) hc hβ.le

/-- **Gibbs-weighted integrability criterion**: an a.e.-measurable function whose product with
the Gibbs density is bounded off collisions is `P_{N,β}`-integrable. -/
theorem q84d_integrable_of_q_bound {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) {F : Config d N → ℝ} (hF : AEStronglyMeasurable F volume) (C : ℝ)
    (hC : ∀ X : Config d N, X ∉ collisionSet d N →
      Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) * |F X| ≤ C) :
    Integrable F (canonicalGibbs (periodicRiesz d s) V N β) := by
  obtain ⟨c, hc⟩ := q84d_hlow hd hcrit hV hN
  have hgm := q84d_measurable_g hd hcrit
  have hVm := q84d_measurable_V hV
  rw [q84d_integrable_gibbs_iff hgm hVm hc hβ.le]
  refine Integrable.mono' (integrable_const C)
    ((q84d_measurable_q hgm hVm).aestronglyMeasurable.mul hF) ?_
  filter_upwards [q84d_ae_not_collision (N := N) (d := d) (by omega)] with X hX
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact hC X hX

end Criterion

end HRS.Q84d

end
