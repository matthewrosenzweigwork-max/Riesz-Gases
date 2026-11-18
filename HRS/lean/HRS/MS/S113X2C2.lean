import HRS.MS.S113X2C1

/-!
# S11.3 X2 wiring (worker S11W), C2: the restated core `S113XLocalizedI` and the endpoints from it

`S113XLocalizedI` replaces `S113XLocalized` (S113EndAux4) by its integrated one-sided form: the exit-flux term of the killed
Dirichlet diffusion is not absolutely continuous in time, and `M_n` need not be positive.  For every locally absolutely continuous
exponent `p > 1`: `Gp` is interval integrable and `M_n(t) - M_n(s) ≤ ∫_s^t Gp` for `0 ≤ s ≤ t ≤ T`.  The endpoints
`s113c_r2_moving_Lp_of_X2` and `s113c_r2_moving_moment_transfer_of_X2` are the copies of `s113x_..._of_X2` for it
(the barrier lemma `s113c_chain_bound_int` replaces the logarithmic Grönwall argument).
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

/-- X2, integrated form: the killed (localized) approximations of the actual law. -/
def S113XLocalizedI (d : ℕ) (s q β : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) (εstar r c₀ : ℝ) : Prop :=
  ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
    ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
    ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
      MovParticleSetup P d s q β N X₀ W X →
      P.map X₀ ≪ s113x_Q d s β ρ N 0 →
      ∀ p₀ : ℝ, 1 < p₀ → r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀ < ⊤ →
      ∃ rr : ℕ → ℝ → EucConfig d N → ℝ,
        (∀ n t, Measurable (rr n t)) ∧ (∀ n t x, 0 ≤ rr n t x) ∧
        (∀ n (T : ℝ), ∃ B, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, rr n t x ≤ B) ∧
        (∀ t : ℝ, 0 ≤ t → P.map (X t.toNNReal) ≪ s113x_Q d s β ρ N t ∧
          Tendsto (fun n => ∫⁻ x, ‖rr n t x - r2MovRatio d s β ρ N (P.map (X t.toNNReal)) t x‖ₑ
            ∂(s113x_Q d s β ρ N t)) atTop (𝓝 0)) ∧
        (∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (rr n 0 x ^ p₀) ∂(s113x_Q d s β ρ N 0) ≤
          r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀ + ENNReal.ofReal (1 / ((n : ℝ) + 1))) ∧
        ∀ p : ℝ → ℝ, (∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval p 0 T) →
          (∀ t : ℝ, 0 ≤ t → 1 < p t) → ∀ n : ℕ, ∀ T : ℝ, 0 ≤ T →
            IntervalIntegrable (s113c_Gp (s113x_Q d s β ρ N) (rr n) (s113x_source d s q β N ρ) p) volume 0 T ∧
            ∀ s' t : ℝ, 0 ≤ s' → s' ≤ t → t ≤ T →
              s113_powerMass (s113x_Q d s β ρ N t) (rr n t) (p t) -
                  s113_powerMass (s113x_Q d s β ρ N s') (rr n s') (p s') ≤
                ∫ τ in s'..t, s113c_Gp (s113x_Q d s β ρ N) (rr n) (s113x_source d s q β N ρ) p τ

section Bound

/-- The power bound for one particle setup, from the cores X1 (specialized to the trajectory) and X2. -/
theorem s113c_power_bound {s q β : ℝ} {ρ₀ : Euc d → ℝ} {j m : ℕ} {εstar r c₀ : ℝ}
    (hX2 : S113XLocalizedI d s q β ρ₀ j m εstar r c₀) {f0 : Euc d → ℝ}
    (hf0 : MovInitialClass ρ₀ j m εstar f0) {ρ : ℝ → Euc d → ℝ}
    (hρ : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ) {cL C₀ : ℝ} (hcL : 0 < cL) (hC₀ : 0 ≤ C₀)
    (hLi : Integrable (r2MovL d s q β ρ) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hsrc : ∀ N : ℕ, 2 ≤ N → ∀ᵐ t : ℝ, 0 < t →
        Measurable (s113x_source d s q β N ρ t) ∧
        (r2MovL d s q β ρ t = 0 → ∀ X, s113x_source d s q β N ρ t X = 0) ∧
        (0 < r2MovL d s q β ρ t →
          ∫⁻ X, ENNReal.ofReal (Real.exp ((cL / r2MovL d s q β ρ t) * |s113x_source d s q β N ρ t X|))
              ∂(s113x_Q d s β ρ N t) ≤ ENNReal.ofReal (Real.exp C₀)))
    {N : ℕ} (hN : 2 ≤ N) (hQ : ∀ t : ℝ, 0 ≤ t → IsProbabilityMeasure (s113x_Q d s β ρ N t))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hsetup : MovParticleSetup P d s q β N X₀ W X)
    (hac0 : P.map X₀ ≪ s113x_Q d s β ρ N 0) {p₀ : ℝ} (hp₀ : 1 < p₀) {K₀ : ℝ}
    (hM0 : r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀ ≤ ENNReal.ofReal K₀) (t : ℝ) (ht : 0 ≤ t) :
    P.map (X t.toNNReal) ≪ s113x_Q d s β ρ N t ∧
      r2MovPowerMoment d s β ρ N (P.map (X t.toNNReal)) t
        (r2MovExponent cL p₀ (r2MovL d s q β ρ) t) ≤
        ENNReal.ofReal (max (max K₀ 0 + 1) (Real.exp C₀)) := by
  have hfin : r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀ < ⊤ :=
    lt_of_le_of_lt hM0 ENNReal.ofReal_lt_top
  obtain ⟨rr, hrm, hr0, hrB, hconv, hinit, hode⟩ :=
    hX2 f0 hf0 ρ hρ N hN P X₀ W X hsetup hac0 p₀ hp₀ hfin
  obtain ⟨hacT, hL1⟩ := hconv t ht
  refine ⟨hacT, ?_⟩
  set L : ℝ → ℝ := r2MovL d s q β ρ with hL
  have hL0 : ∀ u, 0 ≤ u → 0 ≤ L u := fun u _ => ENNReal.toReal_nonneg
  set p : ℝ → ℝ := r2MovExponent cL p₀ L with hp
  have hpb : ∀ u, 0 ≤ u → 1 < p u := fun u hu => (s113x_exponent_bounds hcL hp₀ hL0 hu).1
  have hpac : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval p 0 T := fun T hT =>
    s113x_exponent_ac hcL hp₀ hL0 hLi hT
  set K : ℝ := max (max K₀ 0 + 1) (Real.exp C₀) with hK
  -- the bound for every localization
  have hbound : ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (rr n t x ^ p t) ∂(s113x_Q d s β ρ N t) ≤ ENNReal.ofReal K := by
    intro n
    have hmain := hode p hpac hpb n
    have := hQ t ht
    obtain ⟨B, hBt⟩ := hrB n t
    rw [s113x_lintegral_eq_mass (s113x_Q d s β ρ N t) (rr n t) (hrm n t) (hr0 n t) (p t) B (hpb t ht) (hBt t ⟨ht, le_rfl⟩)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hch := s113c_chain_bound_int (fun u => s113x_Q d s β ρ N u) hQ (fun u => rr n u)
      (fun u => s113x_source d s q β N ρ u) L cL C₀ p₀ hcL hC₀ hp₀ hL0 hLi (hrm n) (hr0 n) (hrB n)
      (hsrc N hN) (fun T hT => hmain T hT) ht
    refine hch.trans (max_le_max ?_ le_rfl)
    -- initial mass
    have := hQ 0 le_rfl
    obtain ⟨B0, hB0⟩ := hrB n 0
    have h0 := hinit n
    have hl := s113x_lintegral_eq_mass (s113x_Q d s β ρ N 0) (rr n 0) (hrm n 0) (hr0 n 0) p₀ B0 hp₀ (hB0 0 ⟨le_rfl, le_rfl⟩)
    rw [hl] at h0
    have hMfin : r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀ + ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨hfin.ne, ENNReal.ofReal_ne_top⟩
    have h1 := ENNReal.toReal_mono hMfin h0
    rw [ENNReal.toReal_ofReal (s113x_mass_nonneg _ _ _ (hr0 n 0))] at h1
    rw [ENNReal.toReal_add hfin.ne ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at h1
    have h2 : (r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀).toReal ≤ max K₀ 0 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hM0
      rwa [ENNReal.toReal_ofReal'] at this
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    linarith
  -- Fatou along an a.e. subsequence
  have := hQ t ht
  have hhm : Measurable (r2MovRatio d s β ρ N (P.map (X t.toNNReal)) t) :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hh0 : ∀ x, 0 ≤ r2MovRatio d s β ρ N (P.map (X t.toNNReal)) t x := fun x => ENNReal.toReal_nonneg
  have := s113x_limit_bound (s113x_Q d s β ρ N t) (fun n => rr n t)
    (r2MovRatio d s β ρ N (P.map (X t.toNNReal)) t) (fun n => hrm n t) (fun n => hr0 n t) hhm hh0
    (p t) K (hpb t ht) hL1 hbound
  exact this

end Bound

section Endpoints

variable {d : ℕ}

theorem s113c_r2_moving_Lp_of_X2_X4 (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ) (hγ : 0 ≤ γ)
    (hγs : 0 < s → 0 < γ)
    (hcores : ∃ j m : ℕ, 1 ≤ j ∧ (d : ℝ) / 2 + j + 6 < m ∧
      ∃ εstar r c₀ c C₁ : ℝ, S113XTupleOK d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        S113XLocalizedI d s q β ρ₀ j m εstar r c₀ ∧
        (γ = 0 → S113XLogNormalizer d s q β ρ₀ j m εstar r c₀)) :
    type_of% (HRS.Whole.r2_moving_Lp hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) := by
  obtain ⟨j, m, hj, hm, εstar, r, c₀, c, C₁, ⟨hε, hr, hc₀, hc, hC₁, hNL, hFacts⟩, hloc, hlog⟩ := hcores
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
  refine ⟨j, m, hj, hm, εstar, r, c₀, c, C₁, hε, hr, hc₀, hc, hC₁, hNL, hLprops, astar, cL, hastar, hcL, ?_, ?_⟩
  · -- clause (3)
    intro p₀ hp₀ K₀
    refine ⟨max (max K₀ 0 + 1) (Real.exp C₀), ?_⟩
    intro f0 hf0 ρ hρ' N hN Ω _ P _ X₀ W X hsetup hac hmom t ht
    exact s113c_power_bound hloc hf0 hρ' hcL hC₀ (hLprops f0 hf0 ρ hρ').2
      (fun N hN => hX1 f0 hf0 ρ hρ' N hN) hN (fun t ht => hQ f0 hf0 ρ hρ' N hN t ht)
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


theorem s113c_r2_moving_moment_transfer_of_X2_X4 (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (β q : ℝ) (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ)
    (hcores : ∃ j m : ℕ, 1 ≤ j ∧ (d : ℝ) / 2 + j + 6 < m ∧
      ∃ εstar r c₀ c C₁ : ℝ, S113XTupleOK d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        S113XLocalizedI d s q β ρ₀ j m εstar r c₀ ∧
        (γ = 0 → S113XLogNormalizer d s q β ρ₀ j m εstar r c₀)) :
    type_of% (HRS.Whole.r2_moving_moment_transfer hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) :=
  HRS.MS.R2S11.s11_moving_moment_transfer_of_Lp' hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs
    (s113c_r2_moving_Lp_of_X2_X4 hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs hcores)

theorem s113c_r2_moving_Lp_of_X2 (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ) (hγ : 0 ≤ γ)
    (hγs : 0 < s → 0 < γ)
    (hcores : ∃ j m : ℕ, 1 ≤ j ∧ (d : ℝ) / 2 + j + 6 < m ∧
      ∃ εstar r c₀ c C₁ : ℝ, S113XTupleOK d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        S113XLocalizedI d s q β ρ₀ j m εstar r c₀) :
    type_of% (HRS.Whole.r2_moving_Lp hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) := by
  obtain ⟨j, m, hj, hm, εstar, r, c₀, c, C₁, hOK, hloc⟩ := hcores
  refine s113c_r2_moving_Lp_of_X2_X4 hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs
    ⟨j, m, hj, hm, εstar, r, c₀, c, C₁, hOK, hloc, fun hγ0 => ?_⟩
  have hs00 : s = 0 := by
    rcases lt_or_eq_of_le hs0 with h | h
    · exact absurd hγ0 (hγs h).ne'
    · exact h.symm
  obtain ⟨hε, hr, hc₀, hc, hC₁, hNL, -⟩ := hOK
  exact s113x_logNormalizer hd hs00 hβ hq hρ hC₁ hc₀ hNL

theorem s113c_r2_moving_moment_transfer_of_X2 (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s)
    (hs : s < (d : ℝ) / 2) (β q : ℝ) (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ)
    (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ)
    (hcores : ∃ j m : ℕ, 1 ≤ j ∧ (d : ℝ) / 2 + j + 6 < m ∧
      ∃ εstar r c₀ c C₁ : ℝ, S113XTupleOK d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        S113XLocalizedI d s q β ρ₀ j m εstar r c₀) :
    type_of% (HRS.Whole.r2_moving_moment_transfer hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) :=
  HRS.MS.R2S11.s11_moving_moment_transfer_of_Lp' hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs
    (s113c_r2_moving_Lp_of_X2 hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs hcores)

end Endpoints

end HRS.MS.S113BD

end
