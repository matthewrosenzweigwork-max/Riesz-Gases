import HRS.MS.R26T8AG01g
import HRS.MS.S82WA04

/-!
# S8.2 observed-time layer, packet T8A.G01 (helper h): the pole envelope controls the inverse pair distances

For `X` in configuration space and `i ≠ j`, `1 + ‖X i - X j‖^(-2) ≤ configPoleEnvelope 2 X`, and
`1 ≤ configPoleEnvelope 2 X`.  Consequently `a = 1/‖X i - X j‖` satisfies `a ≤ 2 env` and `a² ≤ env`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_g01h_env_one_le (d N : ℕ) (X : EucConfig d N) : 1 ≤ configPoleEnvelope 2 X := by
  unfold configPoleEnvelope
  have h1 : (1 : ℝ) ≤ (1 + ‖X‖) ^ (2 : ℝ) := Real.one_le_rpow (by linarith [norm_nonneg X]) (by norm_num)
  have h2 : (1 : ℝ) ≤ ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-(2 : ℝ))) :=
    Finset.one_le_prod₀ fun i _ => Finset.one_le_prod₀ fun j _ =>
      by linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-(2 : ℝ))]
  exact one_le_mul_of_one_le_of_one_le h1 h2

theorem r26t8a_g01h_env_pair (d N : ℕ) (X : EucConfig d N) (i j : Fin N) (hij : i ≠ j) :
    1 + ‖X i - X j‖ ^ (-(2 : ℝ)) ≤ configPoleEnvelope 2 X := by
  unfold configPoleEnvelope
  have hg : ∀ k : Fin N, 1 ≤ ∏ l ∈ Finset.univ.erase k, (1 + ‖X k - X l‖ ^ (-(2 : ℝ))) := fun k =>
    Finset.one_le_prod₀ fun l _ => by linarith [Real.rpow_nonneg (norm_nonneg (X k - X l)) (-(2 : ℝ))]
  have hi : 1 + ‖X i - X j‖ ^ (-(2 : ℝ)) ≤ ∏ l ∈ Finset.univ.erase i, (1 + ‖X i - X l‖ ^ (-(2 : ℝ))) := by
    have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩
    have := Finset.mul_prod_erase (Finset.univ.erase i) (fun l => 1 + ‖X i - X l‖ ^ (-(2 : ℝ))) hj
    have hrest : 1 ≤ ∏ l ∈ (Finset.univ.erase i).erase j, (1 + ‖X i - X l‖ ^ (-(2 : ℝ))) :=
      Finset.one_le_prod₀ fun l _ => by linarith [Real.rpow_nonneg (norm_nonneg (X i - X l)) (-(2 : ℝ))]
    have hf0 : 0 ≤ 1 + ‖X i - X j‖ ^ (-(2 : ℝ)) := by
      linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-(2 : ℝ))]
    nlinarith
  have hall : ∏ l ∈ Finset.univ.erase i, (1 + ‖X i - X l‖ ^ (-(2 : ℝ))) ≤
      ∏ k : Fin N, ∏ l ∈ Finset.univ.erase k, (1 + ‖X k - X l‖ ^ (-(2 : ℝ))) := by
    have := Finset.mul_prod_erase Finset.univ
      (fun k => ∏ l ∈ Finset.univ.erase k, (1 + ‖X k - X l‖ ^ (-(2 : ℝ)))) (Finset.mem_univ i)
    have hrest : 1 ≤ ∏ k ∈ Finset.univ.erase i, ∏ l ∈ Finset.univ.erase k, (1 + ‖X k - X l‖ ^ (-(2 : ℝ))) :=
      Finset.one_le_prod₀ fun k _ => hg k
    have hgi := hg i
    nlinarith
  have h1 : (1 : ℝ) ≤ (1 + ‖X‖) ^ (2 : ℝ) := Real.one_le_rpow (by linarith [norm_nonneg X]) (by norm_num)
  have hP0 : 0 ≤ ∏ k : Fin N, ∏ l ∈ Finset.univ.erase k, (1 + ‖X k - X l‖ ^ (-(2 : ℝ))) :=
    Finset.prod_nonneg fun k _ => le_trans zero_le_one (hg k)
  have hle := le_mul_of_one_le_left hP0 h1
  linarith

end HRS.MS.R26T8A

end
