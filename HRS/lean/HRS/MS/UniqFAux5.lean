import HRS.MS.UniqFAux4

/-!
# UNIQ-F, part 5: viscosity `ν ≥ 0` with the mean-field tie `c_t = M ∇g*ρ_t - c₀` (the F-CAU engine)

If `c_t(x) = M (∇g*ρ_t)(x) - c₀` for `t ∈ [0,T]` (the transport coefficient of the mean-field coefficients of `WholeSetup`), then on `[0,T]`
the generator of `fixedEqCoeff b.s b.M b.Q ν c ρ` is that of `D.coeff ρ`, `D = ⟨s, M, quadV Q c₀, ν⟩ : WholeDyn d`
(`∇ quadV Q c₀ = Qx + c₀`, `Q` symmetric), and `IsClassicalAdjointW` only sees the generator at times in `[0,t]`; so
`Fcau.propagatorW_unique_star` (regimes R1, R2a, R2c, R3 and the `LpCase` at `p = 2` through `lpcase_two_cover`) gives uniqueness for EVERY
`ν ∈ [0, ν*]`, in particular `ν = 0`.  The data `CoeffHypRd` come from the slice hypotheses of `fixed_equation`
(`s55f_regular_slice`) and the fields `force`, `rho_cont` of `FixedEqFcauHyp`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.UniqF

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.Ul HRS.MS.Lc HRS.MS.UniqQ HRS.MS.Go HRS.MS.Star

variable {d : ℕ}

/-- `IsClassicalAdjointW` depends on the coefficient only through the generator at times in `[0,t]` -/
theorem uniqf_classical_congr {C C' : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hgen : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ (g : Euc d → ℝ) (x : Euc d), generatorW C r g x = generatorW C' r g x)
    (h : IsClassicalAdjointW C t φ f) : IsClassicalAdjointW C' t φ f := by
  refine ⟨h.c2, h.bdd, h.cont_c2, h.terminal, ?_, ?_, ?_⟩
  · intro x r hr
    rw [← hgen r ⟨hr.1.le, hr.2.le⟩]
    exact h.time_deriv x r hr
  · have e : (fun p : Set.Icc (0 : ℝ) t × Euc d => generatorW C' p.1 (f p.1) p.2) =
        fun p => generatorW C p.1 (f p.1) p.2 := by
      funext p
      exact (hgen p.1 p.1.2 _ _).symm
    rw [e]; exact h.cont_time_deriv
  · obtain ⟨B, hB⟩ := h.bdd_time_deriv
    exact ⟨B, fun r hr x => by rw [← hgen r hr]; exact hB r hr x⟩

/-- the generator of `fixedEqCoeff` with the tie is that of the mean-field coefficients on `[0,T]` -/
theorem uniqf_gen_tie (b : WholeBounds d) (hb : b.Valid) (ν : ℝ) (c : ℝ → Euc d → Euc d) (ρ : ℝ → Euc d → ℝ) (c₀ : Euc d)
    {t : ℝ}
    (htie : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, c r x =
      Torus.matVec b.M (convGradConvW (rieszKernelGrad d b.s) (ρ r) x) - c₀) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ (g : Euc d → ℝ) (x : Euc d),
      generatorW (fixedEqCoeff b.s b.M b.Q ν c ρ) r g x =
        generatorW ((⟨b.s, b.M, quadV b.Q c₀, ν⟩ : WholeDyn d).coeff ρ) r g x := by
  intro r hr g x
  unfold generatorW
  have hdr : (fixedEqCoeff b.s b.M b.Q ν c ρ).drift r x =
      ((⟨b.s, b.M, quadV b.Q c₀, ν⟩ : WholeDyn d).coeff ρ).drift r x := by
    show -(Torus.matVec b.Q x) + c r x = meanFieldDriftW (⟨b.s, b.M, quadV b.Q c₀, ν⟩ : WholeDyn d) (ρ r) x
    unfold meanFieldDriftW
    simp only
    rw [HRS.MS.Adj.ad_gradient_quadV hb.hQ c₀ x, htie r hr x]
    abel
  rw [hdr]
  rfl

/-- `CoeffHypRd` from the slice hypotheses of `fixed_equation` and the two time-continuity / force fields -/
theorem uniqf_coeffHyp (b : WholeBounds d) (hb : b.Valid) {ℓ : ℕ} (hℓ : b.k + 3 + 3 ≤ ℓ) {ρ : ℝ → Euc d → ℝ}
    (hdens : ∀ t ∈ Set.Icc (0 : ℝ) b.T, HRS.Whole.IsProbDensity (ρ t) ∧ ContDiff ℝ ℓ (ρ t) ∧
      weightedSupE ℓ b.L (ρ t) ≤ ENNReal.ofReal b.Λ)
    (hforce : (d : ℝ) - 1 ≤ b.s → ∀ t ∈ Set.Icc (0 : ℝ) b.T, ∀ x,
      ‖fracForceRd d b.s (ρ t) x‖ ≤ b.Λ)
    (hcont : ∀ ψ : Euc d → ℝ, Continuous ψ → (∃ B : ℝ, ∀ x, |ψ x| ≤ B) →
      ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Set.Icc (0 : ℝ) b.T)) :
    ∃ Λ' : ℝ, CoeffHypRd b.s (b.k + 3) Λ' b.T ρ := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hk0 : (0 : ℝ) ≤ b.k := Nat.cast_nonneg b.k
  have hL := hb.hL
  have hs0 := hb.hs0
  have hdL : (d : ℝ) + 3 ≤ b.L := by linarith
  set Λr : ℝ := (∑ j ∈ Finset.range (b.k + 3 + 3 + 1), (d : ℝ) ^ j + 1) * max b.Λ 0 with hΛr
  refine ⟨max Λr b.Λ, fun t ht => (hdens t ht).1, ⟨?_, ?_⟩, hcont⟩
  · intro t ht
    obtain ⟨h1, h2, h3⟩ := s55f_regular_slice (n := ℓ) (b.k + 3 + 3) hℓ hdL (hdens t ht).2.1 (hdens t ht).2.2
    exact ⟨h1, h2, h3.trans (le_max_left _ _)⟩
  · intro hs t ht x
    exact (hforce hs t ht x).trans (le_max_right _ _)


/-- **uniqueness of classical adjoint solutions of `fixedEqCoeff` for every `ν ∈ [0,ν*]` under the mean-field tie** -/
theorem uniqf_unique_tie (b : WholeBounds d) (hb : b.Valid) {ν : ℝ} (hν0 : 0 ≤ ν) (hνs : ν ≤ b.νstar)
    {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ} (hF : FixedEqFcauHyp b ν c ρ) {ℓ : ℕ} (hℓ : b.k + 3 + 3 ≤ ℓ)
    (hdens : ∀ t ∈ Set.Icc (0 : ℝ) b.T, HRS.Whole.IsProbDensity (ρ t) ∧ ContDiff ℝ ℓ (ρ t) ∧
      weightedSupE ℓ b.L (ρ t) ≤ ENNReal.ofReal b.Λ)
    (c₀ : Euc d)
    (htie : ∀ r ∈ Set.Icc (0 : ℝ) b.T, ∀ x, c r x =
      Torus.matVec b.M (convGradConvW (rieszKernelGrad d b.s) (ρ r) x) - c₀)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) {φ : Euc d → ℝ} {f₁ f₂ : ℝ → Euc d → ℝ}
    (h₁ : IsClassicalAdjointW (fixedEqCoeff b.s b.M b.Q ν c ρ) t φ f₁)
    (h₂ : IsClassicalAdjointW (fixedEqCoeff b.s b.M b.Q ν c ρ) t φ f₂) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, f₁ r = f₂ r := by
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  obtain ⟨Λ', hρ⟩ := uniqf_coeffHyp b hb hℓ hdens hF.force hF.rho_cont
  obtain ⟨ΛV, G₀, hV⟩ := s55f_vhyp_quadV hb.hQ c₀ (b.k + 3 + 3)
  have hRg : (∃ (Rg : PDE.Regime) (ν₀ : ℝ), RdRegimeHolds Rg d b.s b.M ν ν₀) ∨ UlocStarRegime d b.s b.M := by
    rcases hF.regime with h | ⟨cs, hcs⟩
    · exact Or.inl h
    · exact lpcase_two_cover ν hcs
  obtain ⟨Rg, ν₀, hRg'⟩ : ∃ (Rg : PDE.Regime) (ν₀ : ℝ),
      RdRegimeHolds Rg d b.s b.M ν ν₀ ∨ UlocStarRegime d b.s b.M := by
    rcases hRg with ⟨Rg, ν₀, h⟩ | h
    · exact ⟨Rg, ν₀, Or.inl h⟩
    · exact ⟨PDE.Regime.R1, 0, Or.inr h⟩
  have hsub : ∀ r ∈ Set.Icc (0 : ℝ) t, r ∈ Set.Icc (0 : ℝ) b.T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hg := uniqf_gen_tie b hb ν c ρ c₀ (t := t) (fun r hr x => htie r (hsub r hr) x)
  exact HRS.MS.Fcau.propagatorW_unique_star hd1 hb.hs0 hb.hsd (b.k + 3) (by omega) Rg b.T Λ' ΛV G₀
    (∑ i, ∑ j, |b.M i j|) b.νstar ν₀ (⟨b.s, b.M, quadV b.Q c₀, ν⟩ : WholeDyn d) ρ rfl (s55f_matBound _) hV
    ⟨hν0, hνs⟩ hρ hRg' ht (uniqf_classical_congr hg h₁) (uniqf_classical_congr hg h₂)

end HRS.MS.UniqF
