import HRS.MS.S113EndAux7

/-!
# S11.3 endpoint (worker S113X), part 8: `r2_moving_Lp` from the X cores

`s113x_r2_moving_Lp_of_cores`: the frozen statement `type_of% (r2_moving_Lp ..)` follows from the existence of a tuple of S6.3 constants
`(j, m, ε_*, r, c₀, c, C₁)` with `MovNonlinearConclusion` for which the X cores (`S113XCores`: source exponential moment, killed-diffusion
localization, measurability of `L`, and, for `γ = 0`, bounded negative-temperature normalizers) hold.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s113x_r2_moving_Lp_of_cores (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ) (hγ : 0 ≤ γ)
    (hγs : 0 < s → 0 < γ)
    (hcores : ∃ j m : ℕ, 1 ≤ j ∧ (d : ℝ) / 2 + j + 6 < m ∧
      ∃ εstar r c₀ c C₁ : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c ∧ 0 < C₁ ∧
        MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        S113XCores d s q β γ ρ₀ j m εstar r c₀) :
    type_of% (HRS.Whole.r2_moving_Lp hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) := by
  obtain ⟨j, m, hj, hm, εstar, r, c₀, c, C₁, hε, hr, hc₀, hc, hC₁, hNL, hsrc, hloc, hmeas, hlog⟩ := hcores
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨cL, C₀, hcL, hC₀, hX1⟩ := hsrc
  have hLprops : ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
      ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
      (∀ t : ℝ, 0 ≤ t → (⨆ x : Euc d, ENNReal.ofReal ‖fderiv ℝ (movU d s q β (ρ t)) x‖) < ⊤) ∧
        Integrable (r2MovL d s q β ρ) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    fun f0 hf0 ρ hρ' => s113x_L_props hj hNL hC₁ hε hc hc₀ hf0 hρ' (hmeas f0 hf0 ρ hρ')
  obtain ⟨M, L, E, c₁, hM1, hc₁, hE, hfam⟩ :=
    HRS.MS.MovEnt.s66_fam_exists hd hs0 hsd hq hβ hρ hC₁ hc₀.le hNL
  have hround : ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
      ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ → ∀ t : ℝ, 0 ≤ t →
        IsRound2Density d s M L (ρ t) := fun f0 hf0 ρ hρ' t ht => by
    have hfm := hfam f0 hf0 ρ hρ'
    exact ⟨hfm.prob t ht, hfm.bound t ht, hfm.logm t ht⟩
  have hQ : ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
      ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ → ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
        IsProbabilityMeasure (s113x_Q d s β ρ N t) := fun f0 hf0 ρ hρ' N hN t ht =>
    s113x_Q_prob hd hs0 hs hβ hq hρ hC₁ hc₀ hNL hf0 hρ' hN ht
  obtain ⟨astar, hastar, hK0⟩ : ∃ astar : ℝ, 0 < astar ∧ (γ = 0 → ∃ K₀ : ℝ,
      ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
      ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ θ ∈ Set.Icc (-astar) (0 : ℝ),
        0 < HRS.Whole.gibbsNormalizer (rieszKernel d s) N θ (HRS.Whole.withDensityReal (ρ 0)) ∧
        |Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d s) N θ (HRS.Whole.withDensityReal (ρ 0)))| ≤ K₀) := by
    by_cases h0 : γ = 0
    · obtain ⟨a, ha, K₀, hK₀⟩ := hlog h0
      exact ⟨a, ha, fun _ => ⟨K₀, hK₀⟩⟩
    · exact ⟨1, one_pos, fun h => absurd h h0⟩
  refine ⟨j, m, hj, hm, εstar, r, c₀, c, C₁, hε, hr, hc₀, hc, hC₁, hNL, hLprops, astar, cL, hastar, hcL, ?_, ?_⟩
  · -- clause (3)
    intro p₀ hp₀ K₀
    refine ⟨max (max K₀ 0 + 1) (Real.exp C₀), ?_⟩
    intro f0 hf0 ρ hρ' N hN Ω _ P _ X₀ W X hsetup hac hmom t ht
    exact s113x_power_bound hloc hf0 hρ' hcL hC₀ (hLprops f0 hf0 ρ hρ').2
      (fun N hN t ht => hX1 f0 hf0 ρ hρ' N hN t ht) hN (fun t ht => hQ f0 hf0 ρ hρ' N hN t ht)
      P X₀ W X hsetup hac hp₀ hmom t ht
  · -- clause (2)
    intro p₀ hp₀ hθ1 hθ2
    obtain ⟨Kim, hKim⟩ : ∃ Kim : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
        ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ → ∀ N : ℕ, 2 ≤ N →
        ∀ f : Measure (EucConfig d N), MovPrepared d s N γ (HRS.Whole.withDensityReal (ρ 0)) f →
          f ≪ s113x_Q d s β ρ N 0 ∧ r2MovPowerMoment d s β ρ N f 0 p₀ ≤ ENNReal.ofReal Kim := by
      by_cases h0 : γ = 0
      · obtain ⟨K₀, hK₀⟩ := hK0 h0
        obtain ⟨K, hK⟩ := s113x_initial_moment_zero hd hs0 hs M L (K₀ := K₀) hβ hp₀
        refine ⟨K, fun f0 hf0 ρ hρ' N hN f hf => ?_⟩
        have hθ : p₀ * 0 - (p₀ - 1) * β ∈ Set.Icc (-astar) (0 : ℝ) := by
          have := hθ2 h0
          rw [h0] at this
          refine ⟨this.le, ?_⟩
          nlinarith
        have hK' := hK (ρ 0) (hround f0 hf0 ρ hρ' 0 le_rfl) N hN
          (hK₀ f0 hf0 ρ hρ' N hN _ hθ)
        rcases hf with ⟨-, hfe⟩ | ⟨hpos, -⟩
        · rw [hfe]; exact hK'
        · exact absurd h0 hpos.ne'
      · have hγpos : 0 < γ := lt_of_le_of_ne hγ (Ne.symm h0)
        obtain ⟨K, hK⟩ := s113x_initial_moment_pos hd hs0 hs M L hβ hγpos hp₀ (hθ1 hγpos)
        refine ⟨K, fun f0 hf0 ρ hρ' N hN f hf => ?_⟩
        have hK' := hK (ρ 0) (hround f0 hf0 ρ hρ' 0 le_rfl) N hN
        rcases hf with ⟨h00, -⟩ | ⟨-, hfe⟩
        · exact absurd h00 h0
        · rw [hfe]; exact hK'
    set K : ℝ := max (max Kim 0 + 1) (Real.exp C₀) with hK
    have hK1 : 1 ≤ K := le_trans (by have := le_max_right Kim 0; linarith) (le_max_left _ _)
    refine ⟨K, fun f0 hf0 ρ hρ' => ?_⟩
    have hL0 : ∀ u, 0 ≤ u → 0 ≤ r2MovL d s q β ρ u := fun u _ => by unfold r2MovL; exact ENNReal.toReal_nonneg
    have hLi := (hLprops f0 hf0 ρ hρ').2
    set B : ℝ := ∫ u in Set.Ioi (0 : ℝ), r2MovL d s q β ρ u with hB
    have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Ioi fun u hu => hL0 u hu.le
    obtain ⟨h1, h2, h3⟩ := s113_uniform_exponent cL p₀ B hcL hp₀ hB0 _ hL0 hLi le_rfl
    refine ⟨lt_of_lt_of_le h1 h2, ?_⟩
    intro N hN Ω _ P _ X₀ W X hsetup hprep
    obtain ⟨hac0, hM0⟩ := hKim f0 hf0 ρ hρ' N hN _ hprep
    have hbound := fun t ht => s113x_power_bound hloc hf0 hρ' hcL hC₀ hLi
      (fun N hN t ht => hX1 f0 hf0 ρ hρ' N hN t ht) hN (fun t ht => hQ f0 hf0 ρ hρ' N hN t ht)
      P X₀ W X hsetup hac0 hp₀ hM0 t ht
    refine ⟨hM0.trans (ENNReal.ofReal_le_ofReal ?_), fun t ht => ⟨(hbound t ht).1, (hbound t ht).2, ?_⟩⟩
    · exact le_trans (by have := le_max_left Kim 0; linarith) (le_max_left _ _)
    · have hXm : Measurable (X t.toNNReal) := (hsetup.sol t).adapted _
      have hfp : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
        (Measure.isProbabilityMeasure_map_iff hXm.aemeasurable).2 inferInstance
      have hQt := hQ f0 hf0 ρ hρ' N hN t ht
      have hhm : Measurable (r2MovRatio d s β ρ N (P.map (X t.toNNReal)) t) :=
        (Measure.measurable_rnDeriv _ _).ennreal_toReal
      have hh0 : ∀ x, 0 ≤ r2MovRatio d s β ρ N (P.map (X t.toNNReal)) t x := fun x => ENNReal.toReal_nonneg
      exact s113x_eLpNorm_le (s113x_Q d s β ρ N t) _ hhm hh0 (le_of_lt (lt_of_lt_of_le h1 h2)) (h3 t ht).1 hK1
        (hbound t ht).2

end HRS.MS.S113BD
