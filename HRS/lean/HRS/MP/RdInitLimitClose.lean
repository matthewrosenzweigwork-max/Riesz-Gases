import HRS.MP.RdInit
import HRS.MP.RdPropAssemble

/-!
# Closing `path_initial_modulus_rd_limit` (S.A.23, limit clause on `ℝ^d`)

The frozen statement (with the almost-sure linearity of `η` added by MP-RD-REPAIRS-3) follows from
`RdInit.path_initial_modulus_rd_limit'_of_increment` and the per-coefficient increment bound `rpi_increment` of
S.A.22.  The increment constant is chosen before `S` and `L`; the index relation of `fd.Gamma` is obtained from the
`regime` field of `LimitPathHyp` by `rpi_hGamma` for some admissible pair, and the statement is vacuous if there is
none.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.RdInitLimitClose
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem path_initial_modulus_rd_limit_proof (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Kadj Cw Cin : ℝ) (m₀ : ℕ) (hm₀' : m₀ ≤ mStar d) (χ : Euc d → ℝ)
    (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, ∀ (S : WholeMainData d), S.s = s → S.T = T → PDE.MatBound MB S.M →
      VHypRd (fd.Gamma + 5) ΛV G₀ S.V → ∀ L : LimitCoeffsRd d,
      LimitPathHyp S L fd ν₀ Λ Kadj Cw m₀ → L.invβ ≤ νbar → L.A ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : Ω → (Euc d → ℝ) → ℝ),
      (∀ (ψ ψ' : Euc d → ℝ) (c : ℝ), Y0Class m₀ χ ψ → Y0Class m₀ χ ψ' →
        ∀ᵐ ζ ∂P, η ζ (c • ψ + ψ') = c * η ζ ψ + η ζ ψ') →
      (∀ ψ : Euc d → ℝ, Y0Class m₀ χ ψ → ∫⁻ ζ, ENNReal.ofReal ((η ζ ψ) ^ 2) ∂P ≤
        ENNReal.ofReal (Cin ^ 2 * (varpiNormE m₀ χ ψ).toReal ^ 2)) →
      ∀ J : ℝ → Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ), (∀ t, Measurable (J t)) →
        (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Euc d → ℝ, IsSobolevTest ((fd.Gamma + 2 : ℕ) : ℝ) φ →
          ∀ᵐ ζ ∂P, HNeg.pairing φ (J t ζ) = L.A * η ζ (propagatorW (L.coeff S) 0 t φ)) →
        (∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ζ, ‖J t ζ - J s' ζ‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (C * |t - s'| ^ 2)) ∧
        ∃ Zc, ContVersionTight (Ω := fun _ : ℕ => Ω) T (fun _ => P) (fun _ t ζ => J t ζ) Zc := by
  classical
  by_cases hex : ∃ (S0 : WholeMainData d) (L0 : LimitCoeffsRd d), S0.s = s ∧
      fd.HoldsAt S0.s S0.M L0.invβ ν₀
  · obtain ⟨S0, L0, hS0s, hH0⟩ := hex
    have hΓ : (mStar d : ℝ) + d / 2 + 4 < ((fd.Gamma : ℝ) + 2) := by
      rw [hS0s] at hH0
      exact HRS.MP.RdProp.rpi_hGamma fd hH0
    obtain ⟨Cgen, hCgen0, hgen⟩ := HRS.MP.RdProp.rpi_increment (s := s) S0.hd (hS0s ▸ S0.hs0)
      (hS0s ▸ S0.hsd) fd.Gamma m₀ hm₀' hΓ MB Λ ΛV G₀ νbar
    set C₁ : ℝ := max Cw 0 * Real.exp (max Cw 0 * T) * Cgen with hC₁
    obtain ⟨C, hC⟩ := HRS.MP.RdInit.path_initial_modulus_rd_limit'_of_increment s fd T Kadj Cin C₁ m₀ χ hχ
    refine ⟨C, fun S hs hT hMB hV L hL hLν hA Ω _ P _ η hlin hη J hJm hJrep => ?_⟩
    have hreg : IsRegularMFRd s (fd.Gamma + 2 + 3) Λ T L.ρ := by
      have h : IsRegularMFRd S.s (fd.Gamma + 2 + 3) Λ S.T L.ρ := hL.coeff.regular
      rw [hs, hT] at h
      exact h
    obtain ⟨U, hU⟩ := hL.weighted
    have hinc : IncrementBoundRd (L.coeff S) T (fd.Gamma + 2) m₀ C₁ :=
      hgen (L.dyn S) L.ρ T Kadj Cw U hs hMB hV hreg L.hinvβ hLν (hT ▸ hL.adjoint) (hT ▸ hU)
    exact hC S hT L (hT ▸ hL.adjoint) hinc hA P η hlin hη J hJm hJrep
  · refine ⟨0, fun S hs hT hMB hV L hL hLν hA Ω _ P _ η hlin hη J hJm hJrep => ?_⟩
    exfalso
    apply hex
    refine ⟨S, L, hs, ?_⟩
    exact hL.regime

example := (@path_initial_modulus_rd_limit_proof :
  type_of% @HRS.Whole.AppendixALemmas.path_initial_modulus_rd_limit)

end HRS.MP.RdInitLimitClose
