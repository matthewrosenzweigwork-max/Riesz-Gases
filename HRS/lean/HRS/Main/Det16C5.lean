import HRS.Main.Det16C4
import HRS.Main.Det16A3

/-!
# Example A.16: L4 + L6 + L7 assembled (`det16c_sup_tendsto`)

From the hypotheses of `deterministic_example` (without the limit data `L`, `hcoef`, `hinit`, `hη`, `hconv`):
`TorusStanding` at the level `gammaIdx d + 2` and a null sequence `ε_N` bounding, a.s. and uniformly in
`t ∈ [0,T]`, the `H^{-γ'}`-distance (`γ' ≥ γ`) between the particle field `σ_N Ξ_N^t` and the transported
initial field `V_N^{t,0}(κ_N Ξ_N^0)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.Det16

open HRS HRS.Main.A8P HRS.Main.A9

variable {d : ℕ}

theorem det16c_pathwiseUnique {S : MainData d} (hβ : ∀ N, S.invβ N = 0) {R : ∀ N, Realization d N}
    (hflow : SelectedFlows S R) {N : ℕ} (hN : 1 ≤ N) :
    PathwiseUnique (R N).P (S.dyn N) S.T (R N).X₀ (R N).W := by
  have h0 : (S.dyn N).invβ = 0 := hβ N
  rcases (hflow N hN).flow with ⟨-, h⟩ | ⟨-, -, hpos, -⟩ | ⟨-, -, hpos, -⟩
  · exact h
  · rw [h0] at hpos; exact absurd hpos (lt_irrefl _)
  · rw [h0] at hpos; exact absurd hpos (lt_irrefl _)

theorem det16c_sup_tendsto (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ VB C₀ Cc Λ' : ℝ), C₀min ≤ C₀ →
    IsCoercivityPair d s C₀ Cc →
    ∀ (S : MainData d), S.s = s → (∀ N, S.invβ N = 0) →
    ∀ (R : ∀ N, Realization d N), SelectedFlows S R →
    (∀ N : ℕ, 1 ≤ N → ∃ (ℱ : MeasureTheory.Filtration ℝ (R N).mΩ)
      (W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ),
      IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X) →
    S.RegimeHolds Rg ν₀ →
    MeanFieldRegularity S (gammaIdx d + 2 + 3) Λ →
    PDE.MatBound MB S.M → PDE.VHyp (gammaIdx d + 2) VB S.V → Torus.SymNonpos S.M →
    (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      HasTransportBound d s (meanFieldDrift (S.dyn N) (S.ρ N t)) Λ') →
    ∀ (Y : ∀ N, Config d N), (∀ N : ℕ, 1 ≤ N → ∀ᵐ ω ∂(R N).P, (R N).X₀ ω = Y N) →
    Tendsto (fun N => S.κ N * correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) (Y N) 0) atTop (𝓝 0) →
    ∃ 𝔈 : ℕ → ℝ, TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d + 2) C₀ Cc 𝔈 ∧
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ γ' : ℝ, (gammaIdx d : ℝ) ≤ γ' →
        ∀ᵐ ω ∂(R N).P, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
          ‖S.sigma N • NegSobolev.ofMeasureDiff γ'
              (empirical ((R N).X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t)) -
            NegSobolev.embed γ' (transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ)
              (S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical (Y N)) S.μ0))‖ ≤ ε N := by
  obtain ⟨C₁, hst⟩ := det16c_standing hd hs0 hsd
  obtain ⟨C₂, C, hC₂, hC, hbd⟩ := det16c_energy_bounds hd hs0 hsd
  obtain ⟨C₀', Cq, hC₀', hCq, hcom⟩ := a8p_commSpec hd hs0 hsd
  refine ⟨max (max C₁ C₂) C₀', fun Rg ν₀ MB Λ VB C₀ Cc Λ' hC₀ hcp S hSs hβ R hflow hfilt hreg hmf
    hmat hV hsym hΛ' Y hdet hsmall => ?_⟩
  have hC1 : C₁ ≤ C₀ := (le_max_left _ _).trans ((le_max_left _ _).trans hC₀)
  have hC2 : C₂ ≤ C₀ := (le_max_right _ _).trans ((le_max_left _ _).trans hC₀)
  have hC3 : C₀' ≤ C₀ := (le_max_right _ _).trans hC₀
  obtain ⟨𝔈, hS⟩ := hst Rg ν₀ MB Λ VB C₀ Cc Λ' hC1 hcp S hSs hβ R hflow hfilt hreg hmf hmat hV hsym hΛ'
    Y hdet hsmall
  refine ⟨𝔈, hS, ?_⟩
  subst hSs
  obtain ⟨Ca, Λ₁, hCa, hspec⟩ := a8p_adjSpec hd S.s hs0 hsd Rg MB Λ VB ν₀
  obtain ⟨Cp, hCp0, hCp⟩ := a8p_hom_prod hd hs0 hsd
  obtain ⟨cT, hcT0, hcT⟩ := a8p_transport_bound hd MB S.s hs0
  have hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT :=
    ⟨hCa.le, hspec, hcom, hCq.le, hC3, hCp0, hCp, hcT0, hcT⟩
  have hV2 : Torus.IsCk 2 S.V := by
    have := hV.1
    exact this.of_le (by exact_mod_cast (by omega : 2 ≤ gammaIdx d + 2 + 3))
  have hae := (hbd C₀ hC2 S rfl hβ R hflow (r := gammaIdx d + 2 + 3) (Λ := Λ) (by omega) hmf hV2
    hsym Λ' hΛ' Y hdet).1
  have hT0 := S.hT.le
  have hZ0 := det16c_Z0_nonneg d
  have hcc : 0 ≤ ((1 / 2) * (Cq * cT)) * (Real.exp (|Λ₁| * S.T) * det16c_Z0 d) := by positivity
  refine ⟨fun N => S.sigma N * (((1 / 2) * (Cq * cT)) * (Real.exp (|Λ₁| * S.T) * det16c_Z0 d)) *
    (S.T * (Real.exp (C * S.T * Λ') *
      max (correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) (Y N) 0) 0)), ?_, ?_⟩
  · have h1 := (det16c_kappa_max_tendsto S.hκ hsmall).const_mul
      ((((1 / 2) * (Cq * cT)) * (Real.exp (|Λ₁| * S.T) * det16c_Z0 d)) *
        (S.T * Real.exp (C * S.T * Λ')))
    rw [mul_zero] at h1
    refine h1.congr fun N => ?_
    rw [det16c_sigma_eq hβ N]; ring
  · intro N hN γ' hγ'
    have hN1 : 1 ≤ N := by omega
    have hsol := det16c_strong hβ hflow hN1
    have hU := det16c_pathwiseUnique hβ hflow hN1
    obtain ⟨x, hx⟩ := det16_deterministic_path (R N).P (S.dyn N) (hβ N) S.T (R N).X₀ (Y N)
      (hdet N hN1) (R N).W hU (R N).X hsol
    have hY : ∀ᵐ ω ∂(R N).P, (R N).X 0 ω = Y N := by
      filter_upwards [hsol.init, hdet N hN1] with ω h1 h2
      rw [h1, h2]
    have hG : 0 ≤ Real.exp (C * S.T * Λ') * max (correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) (Y N) 0) 0 :=
      mul_nonneg (Real.exp_pos _).le (le_max_right _ _)
    have hE : ∀ᵐ ω ∂(R N).P, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
        correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t ≤
          Real.exp (C * S.T * Λ') * max (correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) (Y N) 0) 0 := by
      filter_upwards [hae N hN] with ω hω t ht
      exact (hω t ht).trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_pos _).le)
    exact det16c_sup_bound_embed hP hS hβ hN hG hE x hx (Y N) hY hγ'

end HRS.Main.Det16
