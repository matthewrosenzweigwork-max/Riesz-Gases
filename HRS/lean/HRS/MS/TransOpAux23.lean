import HRS.MS.TransOpAux22
import HRS.MS.WsStatAux11
import HRS.MS.GoFeatAux3
import HRS.MS.ThCorrAux1

/-!
# S611 packet P4g: uniqueness inputs for the stationary thermal data

`s611_uniq_of_thermal`: `s611_Uniq d s q β ρ₀ T` for every `T` (classical adjoint solutions of the stationary coefficients are unique,
from the stationary `WholeSetup` of S2.1 (i) and F-CAU).
`s611_hsus_of_thermal`: a.e. uniqueness of response solutions for `μ_β` (`s98_resp_unique`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_uniq_pos (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {q β : ℝ} (hq : 0 < q)
    (hβ : 0 < β) {ρ₀ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ₀) {T : ℝ} (hT : 0 < T) :
    s611_Uniq d s q β ρ₀ T := by
  obtain ⟨θ, Λ, K, hθ, hvalid, C₀thr, h0, hS⟩ := HRS.MS.S21.s21_setup_family hd hs0 hsd hq hβ hT hρ
  obtain ⟨S, h1, h2, h3, -⟩ := hS C₀thr le_rfl
  intro t ht φ f hf r hr
  have hcoef := HRS.MS.S21.s21_coeff_setup S h1 h2 0
  have hD := HRS.MS.S21.s21_dyn_eq (d := d) s q β
  have hf' : IsClassicalAdjointW (S.coeff 0) t φ f := by
    rw [hcoef, ← hD]; exact hf
  have hRd : ∃ (Rg : PDE.Regime) (ν₀ : ℝ),
      HRS.Whole.AppendixA.RdRegimeHolds Rg d (HRS.MS.S21.s21Bounds d s q β T θ Λ K C₀thr).s
        (HRS.MS.S21.s21Bounds d s q β T θ Λ K C₀thr).M (S.invβ 0) ν₀ := by
    rw [h2 0]
    by_cases h : s ≤ (d : ℝ) - 2
    · exact ⟨PDE.Regime.R1, 0, h⟩
    · exact ⟨PDE.Regime.R3, β⁻¹, by
        show (d : ℝ) - 2 < s ∧ 0 < β⁻¹ ∧ β⁻¹ ≤ β⁻¹
        exact ⟨by linarith, inv_pos.2 hβ, le_rfl⟩⟩
  have := HRS.MS.Go.s55f_propagatorW_eq _ (HRS.MS.S21.s21Bounds_valid hd hs0 hsd hβ hT hθ Λ K C₀thr) S 0
    hRd (t := t) ht hf' r hr
  rw [hcoef, ← hD] at this
  exact this

theorem s611_uniq_of_thermal (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {q β : ℝ} (hq : 0 < q)
    (hβ : 0 < β) {ρ₀ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ₀) (T : ℝ) :
    s611_Uniq d s q β ρ₀ T := by
  intro t ht φ f hf r hr
  exact s611_uniq_pos hd hs0 hsd hq hβ hρ (T := max T 1) (lt_of_lt_of_le one_pos (le_max_right _ _)) t
    ⟨ht.1, ht.2.trans (le_max_left _ _)⟩ φ f hf r hr

theorem s611_tcref_of_thermal (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {q β : ℝ} (hq : 0 < q)
    (hβ : 0 < β) {ρ₀ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ₀) :
    ∃ M₀ c S : ℝ, 0 < c ∧ HRS.MS.TcDefs.TcRef d ρ₀ M₀ c S 0 := by
  obtain ⟨c, M₀, m₂, hc, hM₀, hS, -⟩ := HRS.MS.Tc6.tc6_unif hd hs0 hsd (am := q) (ap := q) (βm := β)
    (βp := β) hq hβ le_rfl le_rfl
  obtain ⟨S, -, hS'⟩ := hS 0
  have hρeq : ρ₀ = thermalDensity d s q β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd hq hβ hρ
  have hTc := hS' q β le_rfl le_rfl le_rfl le_rfl
  rw [← hρeq] at hTc
  exact ⟨M₀, c, S, hc, hTc⟩

theorem s611_hsus_of_thermal (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {q β : ℝ} (hq : 0 < q)
    (hβ : 0 < β) {ρ₀ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ₀) {γ : ℝ} (hγ : 0 ≤ γ) :
    ∀ (ψ h1 h2 : Euc d → ℝ),
      HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ₀) γ ψ h1 →
      HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ₀) γ ψ h2 →
      h1 =ᵐ[HRS.Whole.withDensityReal ρ₀] h2 := by
  obtain ⟨M₀, c, S, hc, hTc⟩ := s611_tcref_of_thermal hd hs0 hsd hq hβ hρ
  exact s611_resp_unique (by omega) hs0 hsd hc hTc hγ

end HRS.MS.TransOp

end
