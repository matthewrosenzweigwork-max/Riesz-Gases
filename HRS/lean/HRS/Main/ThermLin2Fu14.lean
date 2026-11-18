import HRS.Main.ThermLin2Fu13

/-!
# THERMLIN2 Fu14: `tl2_dyson_fubini_proof` (B4), the replacement of the stochastic Fubini theorem

**Uses the plan statement `tl2_dyson_pairing` (B1) as a black box** (through `tl2fu_hweak_core`); the orchestrator
swaps in `tl2_dyson_pairing_proof` at integration.  The regularity of `ψ_r = Δ_r U^{r,t} φ` (smooth, in `H^m`,
a.e.-measurable coordinates in `r`) uses `tl2dy_moving_facts` from the packet `Dy` (wk/tl2dyson), merged here.

Proof: the variance computation `tl2fu_main'` (`E D² = 0`, Fu1-Fu9), no stochastic integral is interchanged with an
ordinary one.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

/-- B4 (proved): the almost-sure Fubini identity `⟨Zs^t - Zw^t, φ⟩ = ∫_0^t ⟨Zw^r, (𝓛_r - 𝓛_β)U^{r,t}φ⟩ dr`.
Uses the plan statement `tl2_dyson_pairing` as a black box (via `tl2fu_hweak_core`). -/
theorem tl2_dyson_fubini_proof (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ) (hm : (d : ℝ) + 2 < m)
    {T' : ℝ} (hT' : 0 < T') {K : ℝ} (hK : 0 ≤ K)
    (Vev Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hVd : IsDualEvolution S.dyn S.ρ m Vev) (hVp : IsPlainEvolution Vev T')
    (hVb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Vev t r‖ ≤ K)
    (hWd : IsDualEvolution S.dyn (fun _ => ρβ) m Wev) (hWp : IsPlainEvolution Wev T')
    (hWb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Wev t r‖ ≤ K)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    (G : ℝ → Ω → NegSobolev d m)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T' G (fun r _ => covDensT m S.β⁻¹ T' S.ρ r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0)
    (Zs Zw : ℝ → Ω → NegSobolev d m)
    (hZs : ∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zs t))
    (hZw : ∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zw t))
    (hZsm : ∀ t, Measurable (Zs t)) (hZwm : ∀ t, Measurable (Zw t))
    (hZwc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zw t ω) (Set.Icc 0 T'))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T') {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∀ᵐ ω ∂P, NegSobolev.eval (Zs t ω) φ - NegSobolev.eval (Zw t ω) φ =
      ∫ r in (0 : ℝ)..t, NegSobolev.eval (Zw r ω)
        (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) := by
  have D : Tl2FuSetup m T' K Vev Wev P ℱ G (fun r => covDensT m S.β⁻¹ T' S.ρ r) Zs Zw :=
    { hK := hK, hT0 := hT', hVc := hVp.2.2, hWc := hWp.2.2, hVb := hVb, hWb := hWb, hG := hG, hGc := hGc,
      hGz := hGz, hZs := hZs, hZw := hZw, hZsm := hZsm, hZwm := hZwm, hZwc := hZwc }
  have hφ' : MemSobolev m φ := PDE.MFSemigroup.memSobolev_of_isSmooth hφ m
  rcases ht.1.eq_or_lt with h0 | hpos
  · obtain rfl : t = 0 := h0.symm
    have key := tl2fu_main' (ψ := fun _ => (fun _ : Torus d => (0 : ℝ))) (B := 0) D ht hφ' le_rfl
      (fun r _ => tl2fu_memSob_zero m) (fun r _ => by rw [tl2fu_lpFun_zero, norm_zero])
      (fun k => by
        simp only [tl2fu_lpFun_zero, tl2fu_coord_zero]
        exact aemeasurable_const)
      (fun σ hσ z => by
        have hσ0 : σ = 0 := le_antisymm hσ.2 hσ.1
        subst hσ0
        rw [tl2fu_hweak_core S h m hm Vev Wev hVd hWd hφ le_rfl le_rfl (fun hlt => absurd hlt (lt_irrefl _)) z]
        simp)
    filter_upwards [key] with ω hω
    simpa using hω
  · obtain ⟨B, hB, hreg⟩ := tl2fu_psi_regular S h m hφ hpos
    exact tl2fu_main' (ψ := fun r => tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) (B := B) D ht hφ' hB
      (fun r hr => (hreg r hr).2.1) (fun r hr => (hreg r hr).2.2) (tl2fu_psi_coord_ae S h m hφ hpos)
      (fun σ hσ z => tl2fu_hweak_core S h m hm Vev Wev hVd hWd hφ hσ.1 hσ.2
        (fun _ r hr => (hreg r ⟨hσ.1.trans hr.1, hr.2⟩).1) z)

example := (@tl2_dyson_fubini_proof : type_of% @tl2_dyson_fubini)

end HRS.ThermLin.Plan2
