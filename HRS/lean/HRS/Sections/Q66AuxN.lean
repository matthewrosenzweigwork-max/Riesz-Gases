import HRS.Sections.Q66AuxM
import HRS.Equilibrium.Q84eAuxA

/-!
# Packet Q66: the exponent drift identity
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q66

open HRS.Q84d HRS.PDE HRS.PDE.MFAux HRS.PDE.MFSchauder

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q66_T_eq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j))
    {r : Torus d → ℝ} (hr : Torus.IsSmooth r)
    (hdiv : ∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * r x))
    (hN : 1 ≤ N) (X : Config d N) :
    ∑ i, ∑ k, v k (X i) * Bik d s (q66_Vrho d s ρ) i k X =
      (N : ℝ) * modulatedEnergy (q66_hv d s v) X (withDensityReal ρ)
        - ((N : ℝ) / 2) * ∫ x, ∫ y, q66_hv d s v x y ∂(withDensityReal ρ) ∂(withDensityReal ρ)
        + ∑ i, convFun (periodicRiesz d s) (fun y => ρ y * r y) (X i) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  have hs1 : s < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  set G : Fin d → Torus d → ℝ := fun k z => (periodicRieszGrad d s z) k with hG
  set F : Fin N → Fin N → ℝ := fun i j => ∑ k, v k (X i) * G k (X i - X j) with hF
  set c : Torus d → ℝ := convFun (periodicRiesz d s) (fun y => ρ y * r y) with hc
  set I : Fin d → Torus d → ℝ := fun k x => ∫ y, ρ y * G k (x - y) with hI
  set J : ℝ := ∫ x, ∫ y, q66_hv d s v x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) with hJ
  -- pointwise: h_v(X i, X j) = F i j + F j i
  have hhv : ∀ i j : Fin N, q66_hv d s v (X i) (X j) = F i j + F j i := by
    intro i j
    unfold q66_hv
    simp only [hF, hG]
    have : X j - X i = -(X i - X j) := by abel
    rw [this]
    simp only [q66_gradKernel_odd hsd, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hpair : ∑ i, ∑ j ∈ Finset.univ.erase i, q66_hv d s v (X i) (X j) =
      2 * ∑ i, ∑ j ∈ Finset.univ.erase i, F i j := by
    simp_rw [hhv, Finset.sum_add_distrib]
    rw [HRS.Q84e.q84e_pair_swap F]
    ring
  -- the energy
  have hME : (N : ℝ) * modulatedEnergy (q66_hv d s v) X (withDensityReal ρ) =
      (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i, F i j
        - ∑ i, ((∑ k, v k (X i) * I k (X i)) + c (X i)) + ((N : ℝ) / 2) * J := by
    unfold modulatedEnergy
    rw [hpair]
    have hint : ∀ i : Fin N, ∫ y, q66_hv d s v (X i) y ∂(withDensityReal ρ) =
        (∑ k, v k (X i) * I k (X i)) + c (X i) := fun i =>
      q66_int_hv hd hs0 hs1 hρ hv hr hdiv (X i)
    rw [Finset.sum_congr rfl fun i _ => hint i]
    field_simp
    ring
  rw [hME]
  have hB : ∀ i : Fin N, ∑ k, v k (X i) * Bik d s (q66_Vrho d s ρ) i k X =
      -(∑ k, v k (X i) * I k (X i)) + (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, F i j := by
    intro i
    unfold Bik
    simp_rw [q66_grad_Vrho hd hs0 hs1 hρ (X i)]
    simp only [hF, hG, hI, mul_add, Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    simp only [mul_neg, Finset.sum_neg_distrib]
    congr 1
    have : ∑ k, v k (X i) * ((1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i, (periodicRieszGrad d s (X i - X j)) k) =
        ∑ j ∈ Finset.univ.erase i, (1 / (N : ℝ)) * ∑ k, v k (X i) * (periodicRieszGrad d s (X i - X j)) k := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    rw [this]
  simp_rw [hB]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib]
  simp only [Finset.sum_add_distrib]
  ring

end HRS.Q66

end
