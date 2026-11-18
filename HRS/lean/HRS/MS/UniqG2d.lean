import HRS.MS.UniqG2dDef

/-!
# G2d: `uloc_uniqueness` from the decay theorems

`uloc_uniqueness_core` has exactly the binders and conclusion of
`HRS.Whole.AppendixALemmas.uloc_uniqueness`, plus the single extra hypothesis `h3`: the R3 decay
theorem (packet G2f), stated with the conclusion and hypotheses of `g2e_decay` except that
`Rg ≠ R3` is replaced by `RdRegimeHolds R3 ...`.

Relocation check (to be written once `h3` is discharged by G2f, as `example`):
`example := (fun hd s hs0 hsd m hm Rg T Λ ΛV G₀ MB νbar ν₀ χ hχ M V invβ ρ hM hV hν hρ hRg t ht z hzb hz =>
  uloc_uniqueness_core hd s hs0 hsd m hm Rg T Λ ΛV G₀ MB νbar ν₀ χ hχ M V invβ ρ hM hV hν hρ hRg t ht z hzb hz
    (g2f_decay_R3 ...)) : type_of% @HRS.Whole.AppendixALemmas.uloc_uniqueness`
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqG2d

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqC1 HRS.MS.UniqC2
  HRS.MS.UniqC3 HRS.MS.UniqG2c HRS.MS.UniqG2e HRS.MS.UniqG2a HRS.MS.UniqNDefs

variable {d : ℕ}

theorem uloc_uniqueness_core (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (T Λ ΛV G₀ MB νbar ν₀ : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (M : Matrix (Fin d) (Fin d) ℝ) (V : Euc d → ℝ) (invβ : ℝ) (ρ : ℝ → Euc d → ℝ)
    (hM : PDE.MatBound MB M) (hV : VHypRd (m + 3) ΛV G₀ V) (hν : 0 ≤ invβ ∧ invβ ≤ νbar)
    (hρ : CoeffHypRd s m Λ T ρ)
    (hRg : RdRegimeHolds Rg d s M invβ ν₀) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T)
    (z : ℝ → Euc d → ℝ) (hzb : IsUlBounded χ 1 t z)
    (hz : IsForwardDistSolutionW (⟨s, M, V, invβ⟩ : WholeDyn d) ρ t z)
    (h3 : Rg = PDE.Regime.R3 → ∀ {Cb K : ℝ} {χh : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d},
      IsCutoffPair χ χh →
      HRS.Whole.IsAdvectingDrift m Cb t
        (fun σ => meanFieldDriftW (⟨s, M, V, invβ⟩ : WholeDyn d) (ρ (t - σ))) →
      HRS.Whole.IsNegDriftFlow t
        (fun σ => meanFieldDriftW (⟨s, M, V, invβ⟩ : WholeDyn d) (ρ (t - σ))) Ψ →
      FlowBundle d m Cb t χ χh
        (fun σ => meanFieldDriftW (⟨s, M, V, invβ⟩ : WholeDyn d) (ρ (t - σ))) Ψ K →
      ∀ B : ℝ, 0 ≤ B → (∀ τ ∈ Set.Icc (0 : ℝ) t, ulocNormE 1 χ (z τ) ≤ ENNReal.ofReal B) →
      ∃ C0 : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ c : Euc d,
        ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ c x * moll d ε (z τ) x ^ 2) ≤
          ENNReal.ofReal (C0 * ε)) :
    ∀ τ ∈ Set.Icc (0 : ℝ) t, z τ =ᵐ[volume] 0 := by
  set D : WholeDyn d := ⟨s, M, V, invβ⟩ with hD
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · intro τ hτ
    have : τ = 0 := le_antisymm (h0 ▸ hτ.2) hτ.1
    subst this
    exact hz.init
  obtain ⟨B, hB⟩ := hzb
  have hB' : 0 ≤ max B 0 := le_max_right _ _
  have hzu : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 1 χ (z τ) ≤ ENNReal.ofReal (max B 0) :=
    fun τ hτ => (hB τ hτ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hb : HRS.Whole.IsAdvectingDrift m (c1Cb d s m MB Λ ΛV G₀) t
      (fun σ => meanFieldDriftW D (ρ (t - σ))) :=
    c2_isAdvectingDrift hd hs0 hsd m MB Λ ΛV G₀ (D := D) (ρ := ρ) rfl hM hV hρ ht
  obtain ⟨χh, hχc⟩ := g2d_cutoffPair hχ
  obtain ⟨Ψ, hΨ⟩ := g2d_flow ht.1 hb
  obtain ⟨K, -, hK⟩ := c3_flow_bundle hd m hm (c1Cb d s m MB Λ ΛV G₀) t hpos χ χh hχc
  have hF := hK _ Ψ hb hΨ
  have hdec : ∃ C0 : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ c : Euc d,
      ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ c x * moll d ε (z τ) x ^ 2) ≤
        ENNReal.ofReal (C0 * ε) := by
    by_cases hR3 : Rg = PDE.Regime.R3
    · exact h3 hR3 hχc hb hΨ hF _ hB' hzu
    · exact g2e_decay hd (D := D) hs0 hsd m hm MB Λ ΛV G₀ hM hV hρ ht hχ hν.1 hb hF hz hB' hzu hχc
        hΨ Rg ν₀ hRg hR3
  obtain ⟨C0, hC0⟩ := hdec
  exact g2c_zero hd hF (fun τ hτ => locMass_of_ulocNormE' hχ (hzu τ hτ)) C0 hC0

end HRS.MS.UniqG2d
