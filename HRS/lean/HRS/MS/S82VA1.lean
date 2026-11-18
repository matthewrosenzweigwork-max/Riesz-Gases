import HRS.MS.S82VL2
import HRS.MS.S82VG1
import HRS.MS.S82VG2
import HRS.MS.S82VG3

/-!
# S8.2 A02 (S82V), part 5: expansion of the particle generator of the pair statistic
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82V
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

/-- The drift of particle `i` splits into the mean-field drift, the fluctuation, and `F_mu / N`. -/
lemma s82v_drift_split {m : ℕ} (a beta : ℝ) (rho : Euc d → ℝ) (X : EucConfig d (m + 1))
    (i : Fin (m + 1)) :
    particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i =
      (critCoeff d a beta rho).drift 0 (X i) +
        (1 / ((m + 1 : ℕ) : ℝ)) • (Phase2S82.forceMean rho (X i) -
          ∑ k ∈ Finset.univ.erase i, Phase2S82.centeredForce rho (X i) (X k)) := by
  rw [s82v_particleDrift, s82v_drift]
  unfold Phase2S82.centeredForce
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel, smul_sub]
  have hm : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) * (m : ℝ) = 1 - 1 / ((m + 1 : ℕ) : ℝ) := by
    push_cast; field_simp; ring
  have e1 : (1 / ((m + 1 : ℕ) : ℝ)) • (m • forceMean rho (X i)) =
      (1 - 1 / ((m + 1 : ℕ) : ℝ)) • forceMean rho (X i) := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hm]
  rw [e1]
  module

lemma s82v_site_term {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) {m : ℕ}
    (i : Fin (m + 1)) (X : EucConfig d (m + 1)) (hX : ∀ j, j ≠ i → X j ≠ X i) :
    inner ℝ (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i)
        (Phase2S82.configGrad (Phase2S82.pairStatistic (N := m + 1) Q) X i) =
      (2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) *
        (∑ j ∈ Finset.univ.erase i,
            inner ℝ ((critCoeff d a beta rho).drift 0 (X i)) (Phase2S82.pairGradX Q (X i) (X j)) +
          (1 / ((m + 1 : ℕ) : ℝ)) *
            (∑ j ∈ Finset.univ.erase i, inner ℝ (Phase2S82.forceMean rho (X i)) (Phase2S82.pairGradX Q (X i) (X j)) -
              ∑ j ∈ Finset.univ.erase i, ∑ k ∈ Finset.univ.erase i,
                inner ℝ (Phase2S82.centeredForce rho (X i) (X k)) (Phase2S82.pairGradX Q (X i) (X j)))) := by
  rw [s82v_drift_split a beta rho X i, HRS.MS.S82P2.s82p2_configGrad_pair hQ i X hX,
    s82v_sum_succAbove (fun j => Phase2S82.pairGradX Q (X i) (X j)) i]
  rw [inner_smul_right, inner_add_left, inner_smul_left, inner_sub_left, sum_inner]
  simp only [inner_sum, RCLike.conj_to_real]
  rw [Finset.sum_comm]

/-- Expansion of the particle generator of the pair statistic at a collision-free configuration. -/
theorem s82v_gen_expand {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) {m : ℕ}
    (X : EucConfig d (m + 1)) (hX : ∀ i j, i ≠ j → X i ≠ X j) :
    particleGenerator (quadraticGradientDyn d (criticalS d) a beta)
        (Phase2S82.pairStatistic (N := m + 1) Q) X =
      (2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) *
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          (beta⁻¹ * Laplacian.laplacian (fun y => Q y (X j)) (X i) +
            inner ℝ ((critCoeff d a beta rho).drift 0 (X i)) (Phase2S82.pairGradX Q (X i) (X j))) +
      (2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) * (1 / ((m + 1 : ℕ) : ℝ))) *
        ((∑ i, ∑ j ∈ Finset.univ.erase i,
            inner ℝ (Phase2S82.forceMean rho (X i)) (Phase2S82.pairGradX Q (X i) (X j))) -
          ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ Finset.univ.erase i,
            inner ℝ (Phase2S82.centeredForce rho (X i) (X k)) (Phase2S82.pairGradX Q (X i) (X j))) := by
  unfold particleGenerator
  have hs : ∀ i : Fin (m + 1), ∀ j, j ≠ i → X j ≠ X i := fun i j hj => hX j i hj
  have h1 : ∀ i : Fin (m + 1),
      Laplacian.laplacian (fun y => Phase2S82.pairStatistic (N := m + 1) Q (Function.update X i y)) (X i) =
        (2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) *
          ∑ j ∈ Finset.univ.erase i, Laplacian.laplacian (fun y => Q y (X j)) (X i) := fun i =>
    s82v_laplacian_pair hQ i X (hs i)
  simp_rw [h1, s82v_site_term hQ _ X (hs _)]
  have hb : (quadraticGradientDyn d (criticalS d) a beta).invβ = beta⁻¹ := rfl
  rw [hb, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end HRS.MS.S82V
