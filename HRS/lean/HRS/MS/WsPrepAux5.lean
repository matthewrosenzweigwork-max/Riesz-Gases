import HRS.MS.WsPrepAux4
import HRS.MS.MovEntAux1
import HRS.MS.ThmCons

/-!
# S21R packet 5: the particle package of S2.1 (ii) from S6.6 at the frozen indices

`s21p_package`: for `d ≥ 2`, `0 ≤ s < d`, `a, β > 0`, `β₀ ≥ 0`, `T > 0`, constants `(c₁, C₁)` and `hMov : MovEntAt d s (100d+1000) (102d+1020)`, there are
`εstar > 0` and constants `C₀, CB, CT` such that for every thermal `ρβ`, every `εstar`-admissible perturbation, every resulting solution `ρ`,
every `N ≥ 2` with `GibbsEntropyContraction` and every realization of the frozen statement S2.1 (ii) (vector Brownian motion, independent initial
datum with law `Q_{N,β₀}(μ⁰)`, strong solution on every horizon, no filtration) there is a modification `X'` of `X` (a.s. equal at every time)
which is
* an `IsR2Realization` (global strong solution with the initial datum `X₀`, with a filtration: `s21p_filtered_global`),
* satisfies the S6.6 particle bounds `MovParticleBounds d s a β C₀ CB ρ N P X'` (entropy, pressure `E|F_N^g| ≤ Cδ_N`, product entropy, completed energy
  `E(F_N^g + o_N) ≤ C o_N`, second moment), and
* the window second-moment bound `E sup_{[b,b+T]} N⁻¹∑|x_i|² ≤ CT` for every window start `b ≥ 0`.
These are exactly the realization/particle inputs of `r2_window_errors` (S10.4) and `r2_window_general_initial` (S10.5).
`εstar ≤` the S6.3 smallness and `C₁ εstar ≤` the S6.3 radius are chosen here (`min`), the class transfer is `s21p_resulting_in_class`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

theorem s21p_package (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) {T : ℝ} (hT : 0 < T)
    (hMov : MovEntAt d s (100 * d + 1000) (102 * d + 1020)) (c₁ C₁ : ℝ) :
    ∃ εstar : ℝ, 0 < εstar ∧ ∃ C₀ CB CT : ℝ,
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ε : ℝ, ∀ ψ : Euc d → ℝ,
      IsAdmissiblePerturbation ρβ εstar ε ψ → ∀ ρ : ℝ → Euc d → ℝ,
      IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ → ∀ N : ℕ, 2 ≤ N →
      GibbsEntropyContraction d s a β N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → EucConfig d N),
        IsVectorBrownian P W → IndepFun X₀ (fun ζ t => W t ζ) P →
        law P X₀ = modulatedGibbs (rieszKernel d s) N β₀ (withDensityReal (ρ 0)) →
        (∀ T' : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s a β) T' X₀ W X) →
        ∃ X' : ℝ≥0 → Ω → EucConfig d N, (∀ t : ℝ≥0, X' t =ᵐ[P] X t) ∧
          IsR2Realization d s a β P X₀ W X' ∧
          MovParticleBounds d s a β C₀ CB ρ N P X' ∧
          ∀ b : ℝ, 0 ≤ b → ∫⁻ ζ, ⨆ t ∈ Set.Icc b (b + T),
            ENNReal.ofReal (movSecondMoment (X' t.toNNReal ζ)) ∂P ≤ ENNReal.ofReal CT := by
  by_cases h₁ : ∃ ρ₁ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ₁
  swap
  · exact ⟨1, one_pos, 0, 0, 0, fun ρβ hρβ => absurd ⟨ρβ, hρβ⟩ h₁⟩
  obtain ⟨ρ₁, hρ₁⟩ := h₁
  have hj1 : 1 ≤ 100 * d + 1000 := by omega
  have hjm : (d : ℝ) / 2 + ((100 * d + 1000 : ℕ) : ℝ) + 6 < ((102 * d + 1020 : ℕ) : ℝ) := by
    push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨ε63, r, c₀, c, C63, hε63, hr, hc₀, hc, hC63, hconc, C₀, -, -, hγ⟩ :=
    hMov hd hs0 hsd β a hβ ha ρ₁ hρ₁ hj1 hjm
  obtain ⟨⟨CB, hCB⟩, hwin⟩ := hγ β₀ hβ₀
  obtain ⟨CT, hCT⟩ := hwin T hT
  obtain ⟨-, hρ₁pos, -⟩ := HRS.MS.MovEnt.s66_rho0_facts hd hs0 hsd ha hβ hρ₁
  set K : ℝ := max C₁ 1 with hK
  have hK1 : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  set εstar : ℝ := min ε63 (r / K) with hεstar
  have hεpos : 0 < εstar := lt_min hε63 (div_pos hr hK1)
  have hCr : C₁ * εstar ≤ r := by
    calc C₁ * εstar ≤ K * εstar := mul_le_mul_of_nonneg_right (le_max_left _ _) hεpos.le
      _ ≤ K * (r / K) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK1.le
      _ = r := by field_simp
  refine ⟨εstar, hεpos, C₀, CB, CT, ?_⟩
  intro ρβ hρβ ε ψ hadm ρ hres N hN hGEC Ω _ P _ X₀ W X hBr hInd hlaw0 hstrong
  have hρeq : ρβ = ρ₁ := (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρβ).trans
    (HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ₁).symm
  subst hρeq
  obtain ⟨hf0, hcls⟩ := s21p_resulting_in_class hρ₁pos (j := 100 * d + 1000) (m := 102 * d + 1020)
    (by omega) (by push_cast; ring) hconc (min_le_left _ _) hCr hadm hres
  -- the initial datum and the realization
  have hX0m : Measurable (X 0) := (hstrong 0).adapted 0
  have hinit : X 0 =ᵐ[P] X₀ := (hstrong 0).init
  have hindep0 : IndepFun (X 0) (fun ζ t => W t ζ) P :=
    IndepFun.congr hInd (hinit.symm) Filter.EventuallyEq.rfl
  have hdistinct : ∀ᵐ ζ ∂P, X 0 ζ ∉ eucCollisionSet d N := by
    filter_upwards [(hstrong 0).no_collision] with ζ h
    exact h 0 (by simp)
  have hS0 : ∀ T' : ℝ, 0 < T' → IsWholeStrongSolution P (quadraticGradientDyn d s a β) T' (X 0) W X :=
    fun T' _ => { hstrong T' with init := Filter.Eventually.of_forall fun _ => rfl }
  obtain ⟨X', ℱ, W', hmod, hsol', hfil⟩ := HRS.MS.S21.s21p_filtered_global (by omega) s a β hN P W X hBr hindep0
    hdistinct hS0 hX0m
  have hsolX : ∀ T' : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s a β) T' X₀ W X' := by
    intro T'
    have hi : ∀ᵐ ζ ∂P, X' 0 ζ = X₀ ζ := by
      filter_upwards [(hsol' T').init, hinit] with ζ h1 h2
      exact h1.trans h2
    exact { hsol' T' with init := hi }
  have hreal : IsR2Realization d s a β P X₀ W X' :=
    { brownian := hBr
      indep := hInd
      solution := hsolX
      filtered := ⟨ℱ, W', hfil⟩ }
  have hsetup : MovParticleSetup P d s a β N X₀ W X' :=
    ⟨hBr, hInd, hreal.solution, hreal.filtered⟩
  -- the preparation
  have hprob0 : IsProbabilityMeasure (withDensityReal (ρ 0)) :=
    HRS.MS.Thm.cb_withDensityReal_isProb ((hres.global 0).density 0 ⟨le_rfl, le_rfl⟩)
  have hprep : MovPrepared d s N β₀ (withDensityReal (ρ 0)) (P.map X₀) := by
    rcases hβ₀.eq_or_lt with h0 | hpos
    · refine Or.inl ⟨h0.symm, ?_⟩
      have := hlaw0
      rw [← h0, modulatedGibbs_zero] at this
      exact this
    · exact Or.inr ⟨hpos, hlaw0⟩
  refine ⟨X', hmod, hreal, hCB _ hf0 ρ hcls N hN hGEC P X₀ W X' hsetup hprep, fun b hb => ?_⟩
  exact hCT _ hf0 ρ hcls N hN hGEC P X₀ W X' hsetup hprep b hb

end HRS.Whole
