import HRS.MS.R2S11Aux6

/-!
# S11.4 item (1) from the conclusion of S11.3 (`r2_moving_Lp`)
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2S11

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s11_p0_exists {β γ astar : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ) (hastar : 0 < astar) :
    ∃ p₀ : ℝ, 1 < p₀ ∧ (0 < γ → 0 < p₀ * γ - (p₀ - 1) * β) ∧
      (γ = 0 → -astar < p₀ * γ - (p₀ - 1) * β) := by
  rcases hγ.eq_or_lt with h0 | hpos
  · refine ⟨1 + min 1 (astar / (2 * β)), ?_, fun h => absurd h (by rw [← h0]; exact lt_irrefl _), fun _ => ?_⟩
    · have : 0 < min 1 (astar / (2 * β)) := lt_min one_pos (by positivity)
      linarith
    · have h1 : min 1 (astar / (2 * β)) * β ≤ astar / 2 := by
        calc min 1 (astar / (2 * β)) * β ≤ (astar / (2 * β)) * β :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hβ.le
          _ = astar / 2 := by field_simp
      rw [← h0]
      nlinarith
  · refine ⟨1 + min 1 (γ / (2 * β)), ?_, fun _ => ?_, fun h => absurd h hpos.ne'⟩
    · have : 0 < min 1 (γ / (2 * β)) := lt_min one_pos (by positivity)
      linarith
    · have h1 : min 1 (γ / (2 * β)) * β ≤ γ / 2 := by
        calc min 1 (γ / (2 * β)) * β ≤ (γ / (2 * β)) * β :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hβ.le
          _ = γ / 2 := by field_simp
      have h2 : 0 ≤ min 1 (γ / (2 * β)) := (lt_min one_pos (by positivity)).le
      nlinarith

theorem s11_Q_prob (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {M L β : ℝ} (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsRound2Density d s M L ρ) {N : ℕ} (hN : 2 ≤ N) :
    IsProbabilityMeasure (HRS.Whole.modulatedGibbs (rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)) := by
  obtain ⟨C, -, hC⟩ := HRS.MS.R2Mt.s92_normalizer_bounds hd hs0 hs M L β (2 * β) hβ (by linarith)
  have hW := (hC ρ hρ N hN β ⟨le_rfl, by linarith⟩).1
  haveI := HRS.MS.R2Mt.s92_isProb_mu hρ.prob
  exact HRS.MS.R2Mt.s92_isProb_Q hW

theorem s11_item1_of_Lp (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ) (hγ : 0 ≤ γ)
    (hγs : 0 < s → 0 < γ)
    (h113 : type_of% (r2_moving_Lp hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs)) :
    ∃ j m : ℕ, 1 ≤ j ∧ (d : ℝ) / 2 + j + 6 < m ∧
      ∃ εstar r c₀ c C₁ : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c ∧ 0 < C₁ ∧
        MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        ∃ pinf K : ℝ, 1 < pinf ∧ S11ActDens d s q β γ ρ₀ j m εstar r c₀ pinf K := by
  obtain ⟨j, m, hj, hm, εstar, r, c₀, c, C₁, hε, hr, hc₀, hc, hC₁, hNL, hfin, astar, cL, hastar, hcL,
    -, hprep⟩ := h113
  refine ⟨j, m, hj, hm, εstar, r, c₀, c, C₁, hε, hr, hc₀, hc, hC₁, hNL, ?_⟩
  obtain ⟨p₀, hp₀, hθ1, hθ2⟩ := s11_p0_exists hβ hγ hastar
  obtain ⟨K, hK⟩ := hprep p₀ hp₀ hθ1 hθ2
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨M, L, E, c₁, hM1, hc₁, hE, hfam⟩ :=
    HRS.MS.MovEnt.s66_fam_exists hd hs0 hsd hq hβ hρ hC₁ hc₀.le hNL
  set B : ℝ := C₁ * εstar / c with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨(1 - (1 - p₀⁻¹) * Real.exp (-(cL⁻¹) * B))⁻¹, K, ?_, ?_⟩
  · -- 1 < pstar, using any class member is not needed: take the trivial member-free statement
    have h1 := HRS.MS.S113BD.s113_uniform_exponent cL p₀ B hcL hp₀ hB0 (fun _ => 0) (fun _ _ => le_rfl)
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

end HRS.MS.R2S11
