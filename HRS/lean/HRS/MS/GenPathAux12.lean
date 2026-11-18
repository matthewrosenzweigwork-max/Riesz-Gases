import HRS.MS.GenPathAux11
import HRS.MH.DualityRdC2

/-!
# S5.6 packet P3 (bridge): `flucInteractionRd = ½ Comm_N`

The interaction term of the whole-space duality identity (`flucInteractionRd`, the symmetrised pairings of
`μ_N - μ`) is half of the commutator `Comm_N(Mᵀ∇ψ; X, ρ)` (`commN`, `centeredPairFunctional` of the commutator kernel):
`s56_fluc_eq_comm`.  Hence `(σ/2) ∫_0^t Comm_N(Mᵀ∇U^{r,t}φ_j; X^r, ρ^r) dr` is the Duhamel remainder of the TeX
(`B:eq:duality-identity-final`, S L4004-4012), to which the commutator row `general_orbits_commutator` applies.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS.Whole HRS.Whole.AppendixA HRS.MH.DualityRd

variable {d : ℕ}

theorem s56_pairKernel_eq (D : WholeDyn d) (ψ : Euc d → ℝ) (x y : Euc d) :
    pairKernelRd D ψ x y =
      commutatorKernel d D.s (fun z => Torus.matVec D.M.transpose (gradient ψ z)) x y := by
  unfold pairKernelRd commutatorKernel
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h, ← dc1a_matVec_sub, dc1a_inner_matVec]

theorem s56_fluc_eq_comm (D : WholeDyn d) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) {N : ℕ}
    {ρ : Euc d → ℝ} (hρ : RegSliceRd ρ) {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) (X : EucConfig d N) :
    flucInteractionRd D ψ X ρ = (1 / 2 : ℝ) * centeredPairFunctional
      (commutatorKernel d D.s (fun x => Torus.matVec D.M.transpose (gradient ψ x))) X
      (HRS.Whole.withDensityReal ρ) := by
  obtain ⟨hA1, hA2, hA3, hA4⟩ := pairing_expansion_rd_proof D hd hs0 hsd hρ hψ
  have hP : HRS.Whole.IsProbDensity ρ := hρ.1
  have hρm : Measurable ρ := hP.measurable
  have hρnn : ∀ y, 0 ≤ ρ y := hP.nonneg
  have hK : (commutatorKernel d D.s (fun x => Torus.matVec D.M.transpose (gradient ψ x))) =
      pairKernelRd D ψ := funext fun x => funext fun y => (s56_pairKernel_eq D ψ x y).symm
  rw [hK]
  unfold centeredPairFunctional flucInteractionRd
  have hK_int : ∀ i : Fin N, Integrable (fun x => ρ x * pairKernelRd D ψ x (X i)) := fun i =>
    (hA1 (X i)).congr (Filter.Eventually.of_forall fun x => by dsimp only; rw [dc2_K_symm])
  have hdiag : ∀ i, pairKernelRd D ψ (X i) (X i) = 0 := fun i => by simp [pairKernelRd]
  have hρy : ∀ i, ∫ y, pairKernelRd D ψ (X i) y ∂(HRS.Whole.withDensityReal ρ) =
      ∫ x, ρ x * pairKernelRd D ψ x (X i) := fun i => by
    rw [dc1a_integral_withDensity hρm hρnn]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by dsimp only; rw [dc2_K_symm])
  -- the empirical-empirical pairing
  have hEE : interactionPairingW D ψ (HRS.Whole.empirical X) (HRS.Whole.empirical X) =
      (1 / 2 : ℝ) * ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, pairKernelRd D ψ (X i) (X j)) := by
    rw [dc2_B_eq]
    congr 1
    have e1 : ∀ x, ∫ y, pairKernelRd D ψ x y ∂(HRS.Whole.empirical X) =
        (N : ℝ)⁻¹ * ∑ j, pairKernelRd D ψ x (X j) := fun x => dc2_pair_emp X _
    simp only [e1]
    rw [show (∫ x, (N : ℝ)⁻¹ * ∑ j, pairKernelRd D ψ x (X j) ∂(HRS.Whole.empirical X)) =
        (N : ℝ)⁻¹ * ∑ i, (N : ℝ)⁻¹ * ∑ j, pairKernelRd D ψ (X i) (X j) from
      dc2_pair_emp X (fun x => (N : ℝ)⁻¹ * ∑ j, pairKernelRd D ψ x (X j))]
    have e2 : ∀ i, ∑ j, pairKernelRd D ψ (X i) (X j) = ∑ j ∈ Finset.univ.erase i, pairKernelRd D ψ (X i) (X j) :=
      fun i => by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hdiag, zero_add]
    simp only [e2, ← Finset.mul_sum]
    rw [one_div, ← mul_assoc, ← mul_inv, ← sq]
  -- the empirical-density pairing
  have hEρ : interactionPairingW D ψ (HRS.Whole.empirical X) (HRS.Whole.withDensityReal ρ) =
      (1 / 2 : ℝ) * ((1 / (N : ℝ)) * ∑ i, ∫ y, pairKernelRd D ψ (X i) y ∂(HRS.Whole.withDensityReal ρ)) := by
    rw [dc2_B_eq]
    congr 1
    refine (dc2_pair_emp X (fun x => ∫ y, pairKernelRd D ψ x y ∂(HRS.Whole.withDensityReal ρ))).trans ?_
    rw [one_div]
  have hρE : interactionPairingW D ψ (HRS.Whole.withDensityReal ρ) (HRS.Whole.empirical X) =
      (1 / 2 : ℝ) * ((1 / (N : ℝ)) * ∑ i, ∫ y, pairKernelRd D ψ (X i) y ∂(HRS.Whole.withDensityReal ρ)) := by
    rw [dc2_B_eq]
    congr 1
    have e : ∀ x, (∫ y, pairKernelRd D ψ x y ∂(HRS.Whole.empirical X))
        = (N : ℝ)⁻¹ * ∑ i, pairKernelRd D ψ x (X i) := fun x => dc2_pair_emp X _
    simp only [e]
    rw [dc1a_integral_withDensity hρm hρnn]
    calc ∫ x, ρ x * ((N : ℝ)⁻¹ * ∑ i, pairKernelRd D ψ x (X i))
        = ∫ x, ∑ i, (N : ℝ)⁻¹ * (ρ x * pairKernelRd D ψ x (X i)) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by
            dsimp only
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring)
      _ = ∑ i, ∫ x, (N : ℝ)⁻¹ * (ρ x * pairKernelRd D ψ x (X i)) :=
          integral_finsetSum _ fun i _ => (hK_int i).const_mul _
      _ = ∑ i, (N : ℝ)⁻¹ * ∫ x, ρ x * pairKernelRd D ψ x (X i) :=
          Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      _ = (1 / (N : ℝ)) * ∑ i, ∫ y, pairKernelRd D ψ (X i) y ∂(HRS.Whole.withDensityReal ρ) := by
          rw [Finset.mul_sum, one_div]
          exact Finset.sum_congr rfl fun i _ => by rw [hρy i]
  have hρρ : interactionPairingW D ψ (HRS.Whole.withDensityReal ρ) (HRS.Whole.withDensityReal ρ) =
      (1 / 2 : ℝ) * ∫ x, ∫ y, pairKernelRd D ψ x y ∂(HRS.Whole.withDensityReal ρ)
        ∂(HRS.Whole.withDensityReal ρ) := dc2_B_eq D ψ _ _
  rw [hEE, hEρ, hρE, hρρ]
  ring

end HRS.MS.GenPath
