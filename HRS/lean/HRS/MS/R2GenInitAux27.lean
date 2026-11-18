import HRS.MS.R2GenInitAux26
import HRS.MS.R2WinErrAux19

/-!
# S10.5 window comparison, packet C1: the interaction remainder is the commutator forcing

For the quadratic gradient dynamics (`M = -1`) and a regular slice `ρ`:
`flucInteractionRd D ψ X ρ = -(1/2) · centeredPairFunctional (commutatorKernel d s ∇ψ) X ρ`, hence
`√N ∫_0^t flucInteractionRd(U(r,t)φ_α) = -(√N/2) ∫_0^t r2CommForcingMov α t r` (`s105_forcing_coord`), the quantity bounded by the hypothesis `F` of the window comparison.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S21 HRS.MS.GenPath HRS.MS.S52 HRS.MH.DualityRd

variable {d : ℕ}

theorem s105_regSlice (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {τ₀ : ℝ} (hτ : 0 < τ₀) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) : RegSliceRd ρ := by
  obtain ⟨θ, Λ, K, hθ, hvalid, C₀thr, hthr0, hSetup⟩ := s21_setup_family hd hs0 hsd ha hβ hτ hρ
  obtain ⟨S, hρ', hinv', hκ', hCadj⟩ := hSetup C₀thr le_rfl
  have hbv : (s21Bounds d s a β τ₀ θ Λ K C₀thr).Valid :=
    s56_valid_of_eq hvalid (s21Bounds_eq s a β τ₀ θ Λ K C₀thr)
  have := s56_regSlice (s21Bounds d s a β τ₀ θ Λ K C₀thr) hbv S 0 (r := 0) ⟨le_rfl, hτ.le⟩
  rwa [hρ' 0 0] at this

theorem s105_cpf_neg {N : ℕ} (h : Euc d → Euc d → ℝ) (X : EucConfig d N) (ν : Measure (Euc d)) :
    centeredPairFunctional (fun x y => -h x y) X ν = -centeredPairFunctional h X ν := by
  unfold centeredPairFunctional
  simp only [Finset.sum_neg_distrib, integral_neg, mul_neg]
  ring

theorem s105_fluc_eq_forcing (hd1 : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ) {N : ℕ}
    {ρ : Euc d → ℝ} (hρ : RegSliceRd ρ) {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) (X : EucConfig d N) :
    flucInteractionRd (quadraticGradientDyn d s a β) ψ X ρ = -(1 / 2 : ℝ) * centeredPairFunctional
      (commutatorKernel d s (fun x => gradient ψ x)) X (HRS.Whole.withDensityReal ρ) := by
  have h := s56_fluc_eq_comm (quadraticGradientDyn d s a β) hd1 hs0 hsd hρ hψ X
  rw [h]
  have hk : commutatorKernel d (quadraticGradientDyn d s a β).s (fun x => Torus.matVec
      (quadraticGradientDyn d s a β).M.transpose (gradient ψ x)) =
      fun x y => -commutatorKernel d s (fun x => gradient ψ x) x y := by
    funext x y
    unfold commutatorKernel
    have hM : (quadraticGradientDyn d s a β).M = -1 := rfl
    have hv : ∀ v : Euc d, Torus.matVec (quadraticGradientDyn d s a β).M.transpose v = -v := by
      intro v
      rw [hM]
      simp [Torus.matVec]
    simp only [hv]
    show inner ℝ (-gradient ψ x - -gradient ψ y) _ = -inner ℝ (gradient ψ x - gradient ψ y) _
    rw [← inner_neg_left]
    congr 1
    abel
  rw [hk, s105_cpf_neg]
  ring

end HRS.MS.R2GenInit
