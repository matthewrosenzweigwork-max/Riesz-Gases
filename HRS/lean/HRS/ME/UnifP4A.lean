import HRS.MD.EQStatMarg

/-!
# Uniform Proposition 4.2 (packet P4)

The constants of Proposition 4.2 (`M:A:prop:marginal`: the cavity/marginal/pole/kernel/density estimates of
`HRS/Equilibrium/Marginal{Entropy,Cavity,Pole,Kernel,Density}.lean`) are already chosen uniformly in
`β ∈ [βm, βp]` and in the smooth densities `ρ ≤ Λ` by the EQ-MARG-U files
(`HRS/Main/EqMargU1`-`EqMargU4`: `eqmarg_*`; the quantitative TV step is `eqmarg_klDiv_le`, which bounds
`KL(Q_{N,β}(μ) ‖ μ^{⊗N}) ≤ C (N a_N) + C'` with `C, C'` independent of `β ∈ [βm, βp]` and of `ρ`, followed by
`Entropy` subadditivity and Pinsker: `eqmarg_tv_of_kl`).  They need only the upper bound `ρ ≤ Λ`.

This file restates, in the quantifier order and the `β ∈ Set.Icc βm βp` form of packets P1 to P3
(constants after `d, s, βm, βp, Λ`, before `β` and `ρ`), the clause of Proposition 4.2 consumed by the proofs of
`cavity_response_proof` and `insertion_coefficient_proof`, namely the uniform forms of
`firstMarginal_density_L2`, `firstMarginal_density_uniform`, `cavity_marginal_le`, `insDefect_le`,
`pDens_bounds`, `qDens_bound`, `convAbs_bound`, `L2_all`, `sup_dev_small`, `cavity_tv`, `tv_pi_mu`.
The lower bound `c₀ ≤ ρ` is not needed.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.EqMarg

variable {d : ℕ} {s : ℝ}

/-- Uniform `firstMarginal_density_L2` (Proposition 4.2, full-law part). -/
theorem firstMarginal_density_L2_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (Λ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N →
      firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪
          withDensityReal ρ ∧
        eLpNorm (fun y => ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β
            (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y).toReal - 1) 2
            (withDensityReal ρ) ≤ ENNReal.ofReal (C * deltaN d s N) := by
  obtain ⟨C, hC0, hC⟩ := MD.EQStat.eqstat_marginal_unif hd hs0 hsd βm βp hβm hββ Λ
  exact ⟨C, hC0, fun β hβ ρ hρ hΛ N hN => hC β hβ.1 hβ.2 ρ hρ hΛ N hN⟩

/-- Uniform `firstMarginal_density_uniform` (Proposition 4.2, last sentence): the threshold `N₀` depends on
`ε` only (and on `d, s, βm, βp, Λ`). -/
theorem firstMarginal_density_uniform_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (Λ : ℝ) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N ≥ N₀,
      firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪
          withDensityReal ρ ∧
        ∀ᵐ y ∂(withDensityReal ρ),
          |((firstMarginal (modulatedGibbs (periodicRiesz d s) N β
              (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y).toReal - 1| ≤ ε := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := eqmarg_sup_dev_small hd hs0 hsd βm βp hβm hββ Λ ε hε
  refine ⟨n₀ + 2, fun β hβ ρ hρ hΛ N hN => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ0 hρ hn (lam := β / ((n + 1 : ℕ) : ℝ)) rfl
  have hae := rnDeriv_pi_eq hd hs0 hsd hρ hlam hln
  rw [modulatedGibbs_eq_cavity hd hs0 hsd hβ0 hρ (n + 1) (Nat.succ_pos n)]
  refine ⟨?_, ?_⟩
  · rw [firstMarginal_eq_withDensity hd hs0 hsd hρ hlam hln]
    exact withDensity_absolutelyContinuous _ _
  · filter_upwards [hae] with y hy
    rw [hy]
    exact hn₀ β hβ.1 hβ.2 ρ hρ hΛ n (by omega) hn _ rfl y

/-- Uniform `tv_pi_mu` (the quantitative form of `tendsto_tvDist_Q`). -/
theorem tv_pi_mu_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ n₁ : ℕ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ n : ℕ, n₁ ≤ n → ∀ A : Set (Torus d), MeasurableSet A →
    |(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (n + 1)
        (β / ((n + 1 : ℕ) : ℝ)) β) A).toReal - (withDensityReal ρ A).toReal| ≤ ε := by
  intro ε hε
  obtain ⟨n₁, h⟩ := eqmarg_tv_pi_mu hd hs0 hsd βm βp hβm hββ Λ ε hε
  exact ⟨n₁, fun β hβ ρ hρ hΛ n hn A hA => h β hβ.1 hβ.2 ρ hρ hΛ n hn A hA⟩

/-- Uniform `cavity_marginal_le`. -/
theorem cavity_marginal_le_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N → ∀ i : Fin (N - 1),
      (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β).map
          (fun Y : Config d (N - 1) => Y i) ≤ ENNReal.ofReal C • withDensityReal ρ := by
  obtain ⟨C, hC0, h⟩ := eqmarg_cavity_marginal_le hd hs0 hsd βm βp hβm hββ Λ
  exact ⟨C, hC0, fun β hβ ρ hρ hΛ N hN i => h β hβ.1 hβ.2 ρ hρ hΛ N hN i⟩

/-- Uniform `insDefect_le`. -/
theorem insDefect_le_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ : ℝ) :
    ∃ C : ℝ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      0 ≤ insDefect (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x ∧
      insDefect (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x ≤ C * deltaN d s N ∧
      cgf (Xx (periodicRiesz d s) (β / N) x)
          (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) 1 -
        2 * cgf (Xx (periodicRiesz d s) (β / N) x)
          (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) (1 / 2) ≤
        C * deltaN d s N := by
  obtain ⟨C, h⟩ := eqmarg_insDefect_le hd hs0 hsd βm βp hβm hββ Λ
  exact ⟨C, fun β hβ ρ hρ hΛ N hN x => h β hβ.1 hβ.2 ρ hρ hΛ N hN x⟩

/-- Uniform `cavity_tv`. -/
theorem cavity_tv_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ N : ℕ, 2 ≤ N → ∀ A : Set (Torus d), MeasurableSet A →
      |(firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) N (β / N) β) A).toReal -
        (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β) A).toReal| ≤
        C * Real.sqrt (deltaN d s N / N) := by
  obtain ⟨C, hC0, h⟩ := eqmarg_cavity_tv hd hs0 hsd βm βp hβm hββ Λ
  exact ⟨C, hC0, fun β hβ ρ hρ hΛ N hN A hA => h β hβ.1 hβ.2 ρ hρ hΛ N hN A hA⟩

/-- Uniform `pDens_bounds`. -/
theorem pDens_bounds_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ : ℝ) :
    ∃ Mp : ℝ, 1 ≤ Mp ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      Real.exp (-Mp) ≤ pDens (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x ∧
      pDens (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x ≤ Mp := by
  obtain ⟨Mp, h1, h⟩ := eqmarg_pDens_bounds hd hs0 hsd βm βp hβm hββ Λ
  exact ⟨Mp, h1, fun β hβ ρ hρ hΛ N hN x => h β hβ.1 hβ.2 ρ hρ hΛ N hN x⟩

/-- Uniform `qDens_bound`. -/
theorem qDens_bound_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ : ℝ) :
    ∃ Mq : ℝ, 0 < Mq ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N →
    (firstMarginal (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β)) ≪
        withDensityReal ρ ∧
    ∀ᵐ x ∂(withDensityReal ρ),
      qDens (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x ≤ Mq := by
  obtain ⟨Mq, h0, h⟩ := eqmarg_qDens_bound hd hs0 hsd βm βp hβm hββ Λ
  exact ⟨Mq, h0, fun β hβ ρ hρ hΛ N hN => h β hβ.1 hβ.2 ρ hρ hΛ N hN⟩

/-- Uniform `convAbs_bound` (independent of `β`). -/
theorem convAbs_bound_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (Λ : ℝ) :
    ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ x : Torus d, ∫ y, |periodicRiesz d s (x - y)| ∂(withDensityReal ρ) ≤ Kg :=
  eqmarg_convAbs hd hs0 hsd Λ

/-- Uniform `sup_dev_small`: the threshold `n₀` depends on `ε` only. -/
theorem sup_dev_small_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ n : ℕ, n₀ ≤ n → 0 < n → ∀ lam : ℝ,
      lam = β / ((n + 1 : ℕ) : ℝ) → ∀ x : Torus d,
      |pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1| ≤ ε := by
  intro ε hε
  obtain ⟨n₀, h⟩ := eqmarg_sup_dev_small hd hs0 hsd βm βp hβm hββ Λ ε hε
  exact ⟨n₀, fun β hβ ρ hρ hΛ n hn hn0 lam hlam x => h β hβ.1 hβ.2 ρ hρ hΛ n hn hn0 lam hlam x⟩

/-- Uniform `L2_all`. -/
theorem L2_all_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ n : ℕ, 0 < n → ∀ lam : ℝ, lam = β / ((n + 1 : ℕ) : ℝ) →
      ∫ x, (pDens (periodicRiesz d s) (withDensityReal ρ) n lam β x - 1) ^ 2 ∂(withDensityReal ρ) ≤
        (C * deltaN d s (n + 1)) ^ 2 := by
  obtain ⟨C, hC0, h⟩ := eqmarg_L2_all hd hs0 hsd βm βp hβm hββ Λ
  exact ⟨C, hC0, fun β hβ ρ hρ hΛ n hn lam hlam => h β hβ.1 hβ.2 ρ hρ hΛ n hn lam hlam⟩

end HRS.ME.Unif

end
