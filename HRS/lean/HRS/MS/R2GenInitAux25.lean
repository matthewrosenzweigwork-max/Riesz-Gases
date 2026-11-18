import HRS.MS.R2GenInitAux24
import HRS.MS.WsStatAux11
import HRS.MS.GenPathAux29

/-!
# S10.5 window comparison, packet B11: the duality identity and the mild identity for the stationary quadratic dynamics

`s105_duality_stat`: `DualityIdentityRd` for the quadratic gradient dynamics with the constant density `ρ_β` and every terminal time `t ≤ τ₀`
(from the stationary setup at horizon `τ₀`, `s21_setup_family`, and `s56_duality`).
`s105_mild_coord`: for the window time `b+u`, the coordinate `α` of `√N(μ_N^{b+u} - ρ_β)` is the sum of the initial term, the coordinate of the
window reconstruction of the martingale `M`, and the forcing `√N ∫_0^{b+u} flucInteractionRd`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S21 HRS.MS.GenPath HRS.MS.S52

variable {d : ℕ}

theorem s105_duality_stat (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {τ₀ : ℝ} (hτ : 0 < τ₀) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {N : ℕ}
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) τ₀ X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) τ₀) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t φ f) :
    DualityIdentityRd P ℱ W' (quadraticGradientDyn d s a β) (fun _ => ρ) X t f := by
  obtain ⟨θ, Λ, K, hθ, hvalid, C₀thr, hthr0, hSetup⟩ := s21_setup_family hd hs0 hsd ha hβ hτ hρ
  obtain ⟨S, hρ', hinv', hκ', hCadj⟩ := hSetup C₀thr le_rfl
  have hbv : (s21Bounds d s a β τ₀ θ Λ K C₀thr).Valid :=
    s56_valid_of_eq hvalid (s21Bounds_eq s a β τ₀ θ Λ K C₀thr)
  have hdyn : S.dyn N = quadraticGradientDyn d s a β := by
    rw [s21_dyn_eq]
    unfold WholeSetup.dyn
    rw [hinv' N]
    rfl
  have hcoeff : S.coeff N = (quadraticGradientDyn d s a β).coeff (fun _ => ρ) := by
    rw [s21_coeff_setup S hρ' hinv' N, ← s21_dyn_eq]
  have hρN : S.ρ N = fun _ => ρ := funext (hρ' N)
  have hX' : IsWholeStrongSolution P (S.dyn N) (s21Bounds d s a β τ₀ θ Λ K C₀thr).T X₀ W X := by
    rw [hdyn]; exact hX
  have hf' : IsClassicalAdjointW (S.coeff N) t φ f := by rw [hcoeff]; exact hf
  have := s56_duality (s21Bounds d s a β τ₀ θ Λ K C₀thr) hbv S P X₀ W X hX' ℱ W' hF t ht φ f hf'
  rw [hdyn, hρN] at this
  exact this

end HRS.MS.R2GenInit
