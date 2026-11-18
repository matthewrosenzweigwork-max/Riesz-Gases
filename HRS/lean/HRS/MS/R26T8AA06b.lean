import HRS.MS.R26T8AA05
import HRS.MS.R26T8AF07a
import HRS.MS.R2InterpAux7

/-!
# S8.2 observed-time layer, packet T8A.A06 (helper b): the finite-N drift correction in pair coordinates

`e_i = N⁻¹ forceMean(X_i) - N⁻¹ ∑_{k≠i} centeredForce(X_i, X_k)` is the difference between the physical particle drift and the
mean-field drift (`r26t8a_a06b_drift`); for `i ≠ j` its pairing with the pair gradients splits into the repeated-label term
`-N⁻¹ repeatedB` and the distinct third-label sum `N⁻¹ ∑_k tripleT` (`r26t8a_a06b_pair_e`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A
open HRS HRS.Whole

/-- `e_i = N⁻¹ forceMean(X_i) - N⁻¹ ∑_{k≠i} centeredForce(X_i,X_k)` -/
def r26t8a_a06b_e {d N : ℕ} (rho : Euc d → ℝ) (X : EucConfig d N) (i : Fin N) : Euc d :=
  (1 / (N : ℝ)) • HRS.MS.Phase2S82.forceMean rho (X i) -
    (1 / (N : ℝ)) • ∑ k ∈ Finset.univ.erase i, HRS.MS.Phase2S82.centeredForce rho (X i) (X k)

theorem r26t8a_a06b_drift {d N : ℕ} (hN : 1 ≤ N) (a beta : ℝ) (rho : Euc d → ℝ)
    (X : EucConfig d N) (i : Fin N) :
    particleDriftW (quadraticGradientDyn d (HRS.MS.Phase2S82.criticalS d) a beta) X i =
      (critCoeff d a beta rho).drift 0 (X i) + r26t8a_a06b_e rho X i := by
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hcard : ((Finset.univ.erase i).card : ℝ) = (N : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hN]; simp
  have hcf : ∑ k ∈ Finset.univ.erase i, HRS.MS.Phase2S82.centeredForce rho (X i) (X k) =
      ∑ k ∈ Finset.univ.erase i, rieszKernelGrad d (HRS.MS.Phase2S82.criticalS d) (X i - X k) -
        ((N : ℝ) - 1) • HRS.MS.Phase2S82.forceMean rho (X i) := by
    unfold HRS.MS.Phase2S82.centeredForce
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, hcard]
  unfold r26t8a_a06b_e
  rw [hcf, r26t8a_f07a_drift]
  unfold particleDriftW
  simp only [quadraticGradientDyn, r26t8a_f05b_matVec_neg, r26t8a_f07a_grad_conf]
  simp only [Finset.sum_neg_distrib, smul_neg, smul_sub, smul_smul]
  have : (1 / (N : ℝ)) * ((N : ℝ) - 1) = 1 - 1 / (N : ℝ) := by field_simp
  rw [this]
  rw [sub_smul, one_smul]
  abel

/-- the pairing of the drift correction with the pair gradients, `i ≠ j` -/
theorem r26t8a_a06b_pair_e {d N : ℕ} (rho : Euc d → ℝ) (Q : Euc d → Euc d → ℝ)
    (hsym : ∀ x y, Q x y = Q y x) (X : EucConfig d N) (i j : Fin N) (hj : j ∈ Finset.univ.erase i) :
    inner ℝ (r26t8a_a06b_e rho X i) (HRS.MS.Phase2S82.pairGradX Q (X i) (X j)) +
      inner ℝ (r26t8a_a06b_e rho X j) (HRS.MS.Phase2S82.pairGradY Q (X i) (X j)) =
    (1 / (N : ℝ)) * (-HRS.MS.Phase2S82.repeatedB rho Q (X i) (X j)) +
      (1 / (N : ℝ)) * ∑ k ∈ (Finset.univ.erase i).erase j,
        HRS.MS.Phase2S82.tripleT rho Q (X i) (X j) (X k) := by
  have hji : j ≠ i := (Finset.mem_erase.1 hj).1
  have hi : i ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨hji.symm, Finset.mem_univ _⟩
  set gX := HRS.MS.Phase2S82.pairGradX Q (X i) (X j) with hgX
  set gY := HRS.MS.Phase2S82.pairGradY Q (X i) (X j) with hgY
  have hinner : ∀ (l : Fin N) (g : Euc d), inner ℝ (r26t8a_a06b_e rho X l) g =
      (1 / (N : ℝ)) * inner ℝ (HRS.MS.Phase2S82.forceMean rho (X l)) g -
        (1 / (N : ℝ)) * ∑ k ∈ Finset.univ.erase l,
          inner ℝ (HRS.MS.Phase2S82.centeredForce rho (X l) (X k)) g := by
    intro l g
    unfold r26t8a_a06b_e
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, sum_inner]
  rw [hinner i gX, hinner j gY]
  rw [← Finset.add_sum_erase (Finset.univ.erase i) _ hj, ← Finset.add_sum_erase (Finset.univ.erase j) _ hi,
    Finset.erase_right_comm]
  have hodd : rieszKernelGrad d (HRS.MS.Phase2S82.criticalS d) (X j - X i) =
      -rieszKernelGrad d (HRS.MS.Phase2S82.criticalS d) (X i - X j) := by
    rw [← neg_sub, HRS.MS.R2Interp.s102_rieszKernelGrad_neg]
  have c1 : inner ℝ (HRS.MS.Phase2S82.centeredForce rho (X i) (X j)) gX =
      inner ℝ (rieszKernelGrad d (HRS.MS.Phase2S82.criticalS d) (X i - X j)) gX -
        inner ℝ (HRS.MS.Phase2S82.forceMean rho (X i)) gX := by
    unfold HRS.MS.Phase2S82.centeredForce; rw [inner_sub_left]
  have c2 : inner ℝ (HRS.MS.Phase2S82.centeredForce rho (X j) (X i)) gY =
      -inner ℝ (rieszKernelGrad d (HRS.MS.Phase2S82.criticalS d) (X i - X j)) gY -
        inner ℝ (HRS.MS.Phase2S82.forceMean rho (X j)) gY := by
    unfold HRS.MS.Phase2S82.centeredForce; rw [inner_sub_left, hodd, inner_neg_left]
  have hT : ∑ k ∈ (Finset.univ.erase j).erase i, HRS.MS.Phase2S82.tripleT rho Q (X i) (X j) (X k) =
      -∑ k ∈ (Finset.univ.erase j).erase i,
          inner ℝ (HRS.MS.Phase2S82.centeredForce rho (X i) (X k)) gX -
        ∑ k ∈ (Finset.univ.erase j).erase i,
          inner ℝ (HRS.MS.Phase2S82.centeredForce rho (X j) (X k)) gY := by
    unfold HRS.MS.Phase2S82.tripleT
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hR : HRS.MS.Phase2S82.repeatedB rho Q (X i) (X j) =
      inner ℝ (rieszKernelGrad d (HRS.MS.Phase2S82.criticalS d) (X i - X j)) gX -
        inner ℝ (rieszKernelGrad d (HRS.MS.Phase2S82.criticalS d) (X i - X j)) gY -
        2 * (inner ℝ (HRS.MS.Phase2S82.forceMean rho (X i)) gX +
          inner ℝ (HRS.MS.Phase2S82.forceMean rho (X j)) gY) := by
    unfold HRS.MS.Phase2S82.repeatedB
    rw [inner_sub_right]
  rw [c1, c2, hT, hR]
  ring

end HRS.MS.R26T8A

end
