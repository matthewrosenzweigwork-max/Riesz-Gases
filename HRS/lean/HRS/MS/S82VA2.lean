import HRS.MS.S82VA1
import HRS.MS.S82VC1

/-!
# S8.2 A02 (S82V), part 12: `lifted_pair_generator`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82V
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

lemma s82v_sym_sum {n : ℕ} (L H J : Fin n → Fin n → ℝ)
    (h : ∀ i j, j ≠ i → L i j + L j i = -H i j - J i j) :
    2 * ∑ i, ∑ j ∈ Finset.univ.erase i, L i j =
      -(∑ i, ∑ j ∈ Finset.univ.erase i, H i j) - ∑ i, ∑ j ∈ Finset.univ.erase i, J i j := by
  have h1 := s82v_pairsum_swap L
  have h2 : ∑ i, ∑ j ∈ Finset.univ.erase i, (L i j + L j i) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, (-H i j - J i j) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj =>
      h i j (Finset.mem_erase.1 hj).1
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at h2
  linarith

lemma s82v_rpow52 (n : ℝ) (hn : 0 < n) : n ^ (-(5 / 2 : ℝ)) = n ^ (-(3 / 2 : ℝ)) * n⁻¹ := by
  rw [← Real.rpow_neg_one, ← Real.rpow_add hn]
  norm_num

/-- **A02 `lifted_pair_generator`.** -/
theorem s82v_lifted_pair_generator (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (a beta M A : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (f : Euc d → ℝ) (Q : Euc d → Euc d → ℝ)
    (hQ : PairCorrector a beta rho M A f Q) :
    ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (Phase2S82.pairStatistic Q) X =
        -Phase2S82.pairStatistic (HSource (HRS.Whole.withDensityReal rho) f) X +
          Phase2S82.errorStatistic (critCoeff d a beta rho) rho Q X := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  intro X hXc
  have hX : ∀ i j, i ≠ j → X i ≠ X j := fun i j hij h => hXc ⟨i, j, hij, h⟩
  rw [s82v_gen_expand hQ X hX]
  set r : ℝ := ((m + 1 : ℕ) : ℝ) with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  set c : ℝ := r ^ (-(3 / 2 : ℝ)) with hc
  have hsym := hQ.symmetric
  set mu := HRS.Whole.withDensityReal rho with hmu
  set C := critCoeff d a beta rho with hC
  -- the local Poisson identity, summed
  have hL := s82v_sym_sum
    (fun i j => beta⁻¹ * Laplacian.laplacian (fun y => Q y (X j)) (X i) +
      inner ℝ (C.drift 0 (X i)) (Phase2S82.pairGradX Q (X i) (X j)))
    (fun i j => HSource mu f (X i) (X j)) (fun i j => pairJ C mu Q (X i) (X j))
    (fun i j hji => s82v_pair_poisson hd ha hbeta hrho hQ (X i) (X j) (hX i j (Ne.symm hji)))
  -- the finite algebra
  have hG : ∀ z : Euc d, rieszKernelGrad d (criticalS d) (-z) = -rieszKernelGrad d (criticalS d) z :=
    fun z => s82v_force_neg _ z
  have halg := s82v_final_alg (N := m + 1) X (rieszKernelGrad d (criticalS d)) (forceMean rho) hG
    (fun i j => Phase2S82.pairGradX Q (X i) (X j)) (fun i j => pairJ C mu Q (X i) (X j))
    (fun i j k => tripleG C rho Q (X i) (X j) (X k)) (fun i j => repeatedB rho Q (X i) (X j))
    (fun i j k => by
      simp only [tripleG, tripleT, Phase2S82.centeredForce, s82v_pairGradY_eq hsym]; rfl)
    (fun i j => by
      simp only [repeatedB, s82v_pairGradY_eq hsym])
  have hS : Phase2S82.tripleSum (tripleG C rho Q) X =
      s82v_sum3 (fun i j k => tripleG C rho Q (X i) (X j) (X k)) := rfl
  rw [← hr] at halg
  have hrr : r⁻¹ * r = 1 := inv_mul_cancel₀ hr0.ne'
  unfold Phase2S82.errorStatistic Phase2S82.pairStatistic Phase2S82.pairSum
  rw [← hr, ← hmu, hS, s82v_rpow52 r hr0, ← hc]
  have e1 : (2 : ℝ) / r = 2 * r⁻¹ := by rw [div_eq_mul_inv]
  rw [e1, one_div]
  have e3 : ∀ i k, Phase2S82.centeredForce rho (X i) (X k) =
      rieszKernelGrad d (criticalS d) (X i - X k) - forceMean rho (X i) := fun _ _ => rfl
  simp only [e3]
  linear_combination c * hL + (c * r⁻¹) * halg
    + (c * ∑ i, ∑ j ∈ Finset.univ.erase i, pairJ C mu Q (X i) (X j)) * hrr

end HRS.MS.S82V

end
