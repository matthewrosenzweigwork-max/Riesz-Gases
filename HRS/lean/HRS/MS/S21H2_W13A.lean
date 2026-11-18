import HRS.MS.S113X2C2
import HRS.MS.R2S11Aux15

/-!
# S21H2, packet R26-T3.W13 (part A): the actual-density conclusion of S11.4 item (1) at EXPLICIT indices `(j, m)`

`HRS.MS.R2S11.s11_item1_of_Lp` composed with `s113c_r2_moving_Lp_of_X2_X4` hides the regularity indices `(j, m)` behind an existential.
The frozen `Trajectory` data only controls `C_b^{100d+1001}` and `Σ^{102d+1020}`, so the indices must be known to be small.
This file repeats the two proofs (the X2/X4 assembly and `s11_item1_of_Lp`) with the indices as parameters; the output is `S11ActDens`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21H2W13

open HRS.Whole HRS.MS.S113BD HRS.MS.R2S11
open HRS (Euc)

variable {d : ℕ}

theorem s21h2_item1_explicit (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ) (hγ : 0 ≤ γ)
    (j m : ℕ) (hj : 1 ≤ j) (hm : (d : ℝ) / 2 + j + 6 < m) (εstar r c₀ c C₁ : ℝ)
    (hOK : S113XTupleOK d s q β ρ₀ j m εstar r c₀ c C₁)
    (hloc : S113XLocalizedI d s q β ρ₀ j m εstar r c₀)
    (hlog : γ = 0 → S113XLogNormalizer d s q β ρ₀ j m εstar r c₀) :
    ∃ pinf K : ℝ, 1 < pinf ∧ S11ActDens d s q β γ ρ₀ j m εstar r c₀ pinf K := by
  obtain ⟨hε, hr, hc₀, hc, hC₁, hNL, hFacts⟩ := hOK
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  have hid := s113x_identity_ae hd hs0 hs hβ hq hρ hj hm hC₁ hε hc hc₀ hNL hFacts
  obtain ⟨cL, C₀, hcL, hC₀, hX1⟩ := s113x_source_of_identity_ae hd hs0 hs hβ hq hρ hj hC₁ hε hc hc₀ hNL hid
  have hmeas := s113x_meas hd hs0 hs hβ hq hρ hj hm hC₁ hε hc₀ hNL
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

  have hprep : ∀ p₀ : ℝ, 1 < p₀ →
      (0 < γ → 0 < p₀ * γ - (p₀ - 1) * β) → (γ = 0 → -astar < p₀ * γ - (p₀ - 1) * β) →
      ∃ K : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
        ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
        1 < r2MovExponentInf cL p₀ (r2MovL d s q β ρ) ∧
        ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
          MovParticleSetup P d s q β N X₀ W X →
          MovPrepared d s N γ (HRS.Whole.withDensityReal (ρ 0)) (P.map X₀) →
          r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀ ≤ ENNReal.ofReal K ∧
          ∀ t : ℝ, 0 ≤ t →
            P.map (X t.toNNReal) ≪ HRS.Whole.modulatedGibbs (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ t)) ∧
            r2MovPowerMoment d s β ρ N (P.map (X t.toNNReal)) t
              (r2MovExponent cL p₀ (r2MovL d s q β ρ) t) ≤ ENNReal.ofReal K ∧
            eLpNorm (r2MovRatio d s β ρ N (P.map (X t.toNNReal)) t)
              (ENNReal.ofReal (r2MovExponentInf cL p₀ (r2MovL d s q β ρ)))
              (HRS.Whole.modulatedGibbs (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ t))) ≤ ENNReal.ofReal K := by
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
    have hbound := fun t ht => s113c_power_bound hloc hf0 hρ' hcL hC₀ hLi
      (fun N hN => hX1 f0 hf0 ρ hρ' N hN) hN (fun t ht => hQ f0 hf0 ρ hρ' N hN t ht)
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
  have hfin := hLprops
  obtain ⟨p₀, hp₀, hθ1, hθ2⟩ := s11_p0_exists hβ hγ hastar
  obtain ⟨K, hK⟩ := hprep p₀ hp₀ hθ1 hθ2
  set B : ℝ := C₁ * εstar / c with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨(1 - (1 - p₀⁻¹) * Real.exp (-(cL⁻¹) * B))⁻¹, K, ?_, ?_⟩
  · have h1 := HRS.MS.S113BD.s113_uniform_exponent cL p₀ B hcL hp₀ hB0 (fun _ => 0) (fun _ _ => le_rfl)
      (by simp) (by simp [hB0])
    exact h1.1
  · intro f0 hf0 ρ hρ' N hN Ω _ P _ X₀ W X hsetup hprep' t ht
    obtain ⟨hinf, hrest⟩ := hK f0 hf0 ρ hρ'
    have hLi := (hfin f0 hf0 ρ hρ').2
    have hL0 : ∀ u, 0 ≤ u → 0 ≤ r2MovL d s q β ρ u := fun u _ => ENNReal.toReal_nonneg
    have hLB := s11_L_integral_le hj hNL hC₁ hε hc hc₀.le hf0 hρ' hLi
    obtain ⟨h1, h2, h3⟩ := HRS.MS.S113BD.s113_uniform_exponent cL p₀ B hcL hp₀ hB0 _ hL0 hLi hLB
    obtain ⟨-, hbig⟩ := hrest N hN P X₀ W X hsetup hprep'
    obtain ⟨hac, -, hnorm⟩ := hbig t ht
    have hXm : Measurable (X t.toNNReal) := (hsetup.sol t).adapted _
    haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) := (Measure.isProbabilityMeasure_map_iff hXm.aemeasurable).2 inferInstance
    have hfm := hfam f0 hf0 ρ hρ'
    haveI := s11_Q_prob hd hs0 hs hβ (M := M) (L := L) ⟨hfm.prob t ht, hfm.bound t ht, hfm.logm t ht⟩ hN
    refine ⟨inferInstance, hac, ?_⟩
    calc _ ≤ eLpNorm (r2MovRatio d s β ρ N (P.map (X t.toNNReal)) t)
            (ENNReal.ofReal (r2MovExponentInf cL p₀ (r2MovL d s q β ρ)))
            (HRS.Whole.modulatedGibbs (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ t))) :=
          eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal h2)
      _ ≤ _ := hnorm

end HRS.MS.S21H2W13
