import HRS.MS.MovEntAux16

/-!
# S6.6, packet P6 (part 10): clause (1) from `SuperDiss d s`

`s66_clause1`: assembly of `WholeMFEHyp` for the S6.3 class, the dissipation inequality and `s66_clause1_core`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovEnt

open HRS.Whole

local notation "wd" => Whole.withDensityReal

variable {d : ℕ}

theorem s66_clause1 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {q β : ℝ} (hq : 0 < q) (hβ : 0 < β)
    {ρ₀ : Euc d → ℝ} (hρ₀ : Whole.IsThermalEquilibrium d s q β ρ₀)
    (hDiss : HRS.MS.MfeConf.SuperDiss d s)
    {m : ℕ} {εstar r c₀ c C₁ : ℝ} (hε : 0 < εstar) (hc₀ : 0 < c₀) (hc : 0 < c) (hC₁ : 0 < C₁)
    (hconc : MovNonlinearConclusion d s q β ρ₀ 1 m εstar r c₀ c C₁)
    (B₁ : ℝ) (hB₁ : 0 ≤ B₁)
    (hschw : ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ 1 m εstar f0 → ∀ ρ : ℝ → Euc d → ℝ,
        MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ → ∀ t : ℝ, 0 ≤ t → ContDiff ℝ 3 (ρ t) ∧
          ∀ k : ℕ, k ≤ 3 → ∀ x : Euc d,
            movBracket x ^ (d + 3) * ‖iteratedFDeriv ℝ k (fun y => ρ t y - ρ₀ y) x‖ ≤ B₁) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ 1 m εstar f0 → ∀ ρ : ℝ → Euc d → ℝ,
      MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        MovParticleSetup P d s q β N X₀ W X → ∀ t : ℝ, 0 ≤ t →
          relEntropy (P.map (X t.toNNReal))
              (Whole.modulatedGibbs (rieszKernel d s) N β (wd (ρ t))) ≤
            ENNReal.ofReal C * (relEntropy (P.map X₀)
                (Whole.modulatedGibbs (rieszKernel d s) N β (wd (ρ 0))) +
              ENNReal.ofReal (N * deltaN d s N)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨M, L, E, c₁, hM1, hc₁, hE0, hfam⟩ := s66_fam_exists hd hs0 hsd hq hβ hρ₀ hC₁ hc₀.le hconc
  obtain ⟨Λ, hΛ1, hΛ⟩ := s66_regular_of_schwartz hd hs0 hsd hq hβ hρ₀ B₁ hB₁
  obtain ⟨hp0, hpos0, Cg, cg, hcg, hgauss⟩ := s66_rho0_facts hd hs0 hsd hq hβ hρ₀
  have hCg0 : 0 ≤ Cg := by
    have h1 := hgauss 0
    have := hpos0 0
    simp at h1
    linarith
  set Kbar : ℝ := C₁ * εstar / c with hKbar
  have hKbar0 : 0 ≤ Kbar := by positivity
  obtain ⟨C₅, hC₅, hcore⟩ := s66_clause1_core hd hs0 hsd M L β Kbar hβ hKbar0
  refine ⟨C₅, hC₅, ?_⟩
  intro f0 hf0 ρ hρ N hN Ω _ P _ X₀ W X hset t ht
  have hprops := s66_class_props hconc hf0 hρ hc₀.le
  have hF := hfam f0 hf0 ρ hρ
  by_cases hH0 : relEntropy (P.map X₀) (Whole.modulatedGibbs (rieszKernel d s) N β (wd (ρ 0))) = ⊤
  · rw [hH0, top_add, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by linarith)).ne']
    exact le_top
  · set D : WholeDyn d := quadraticGradientDyn d s q β with hD
    obtain ⟨hV3, hVB, hVc⟩ := s66_confinement_facts (d := d) q hq
    have hXm : ∀ t' : ℝ≥0, Measurable (X t') := fun t' => (hset.sol 0).adapted t'
    have hX₀ : AEMeasurable X₀ P := by
      have h0 : AEMeasurable (X 0) P := (hXm 0).aemeasurable
      exact h0.congr (by filter_upwards [(hset.sol 0).init] with ζ hζ using hζ)
    -- the data of `K`
    set K : ℝ → ℝ := fun r' => C₁ * εstar * Real.exp (-c * r') with hK
    obtain ⟨hKi, hKint⟩ := s66_int_K (A := C₁ * εstar) (c := c) (by positivity) hc t
    have hK0 : ∀ r' ∈ Set.Icc (0 : ℝ) t, 0 ≤ K r' := fun r' _ => by simp only [hK]; positivity
    have hLip : ∀ r' ∈ Set.Icc (0 : ℝ) t, HasLipBoundW (mfeTransportW D (ρ r')) (K r') := fun r' hr' =>
      s66_lip_of_decay (hK := by positivity) (hprops r' hr'.1).2.2.2 hr'.1
    -- the Gibbs entropy of the initial law
    have hgibbs : relEntropy (P.map X₀) (Whole.canonicalGibbs (rieszKernel d D.s) D.V N (1 / D.invβ)) ≠ ⊤ := by
      show relEntropy (P.map X₀) (Whole.canonicalGibbs (rieszKernel d s) (confinement q) N (1 / β⁻¹)) ≠ ⊤
      rw [one_div, inv_inv, s66_canonical_eq hd hs0 hsd hq hβ hρ₀ N]
      haveI : IsProbabilityMeasure (P.map X₀) := inferInstance
      -- data at `ρ 0 = ρ₀ (1 + f0)`
      obtain ⟨hρ0p, hρ0pos, hρ0ratio, -⟩ := hprops 0 le_rfl
      have hκ0 : ∀ x, 0 < 1 + f0 x := by
        intro x
        have h1 := (hρ0ratio x).1
        have h2 := hρ.init x
        have h3 := hpos0 x
        have hC1 : 0 < C₁⁻¹ := inv_pos.2 hC₁
        by_contra hneg
        push Not at hneg
        have : ρ 0 x ≤ 0 := by rw [h2]; nlinarith
        linarith [hρ0pos x]
      have hκm : Measurable (fun x => 1 + f0 x) := by
        have : Continuous f0 := hf0.cb.1.continuous
        fun_prop
      have hρκ : ∀ x, ρ 0 x = ρ₀ x * (1 + f0 x) := hρ.init
      have hκb : ∀ x, C₁⁻¹ ≤ 1 + f0 x ∧ 1 + f0 x ≤ C₁ := by
        intro x
        have h1 := (hρ0ratio x).1
        have h2 := (hρ0ratio x).2
        have h3 := hpos0 x
        rw [hρκ x] at h1 h2
        exact ⟨le_of_mul_le_mul_right (by linarith) h3, le_of_mul_le_mul_right (by linarith) h3⟩
      have hLk : ∀ x, |Real.log (1 + f0 x)| ≤ |Real.log C₁| := by
        intro x
        obtain ⟨hlo, hhi⟩ := hκb x
        have hpos : 0 < 1 + f0 x := hκ0 x
        have h1 : Real.log (1 + f0 x) ≤ Real.log C₁ := Real.log_le_log hpos hhi
        have h2 : -Real.log C₁ ≤ Real.log (1 + f0 x) := by
          have := Real.log_le_log (inv_pos.2 hC₁) hlo
          rwa [Real.log_inv] at this
        rw [abs_le]
        constructor
        · linarith [le_abs_self (Real.log C₁)]
        · linarith [le_abs_self (Real.log C₁)]
      set A : ℝ := max 1 C₁ * Cg with hA
      have hA0 : 0 ≤ A := by positivity
      have hg1 : ∀ x, ρ 0 x ≤ A * Real.exp (-cg * ‖x‖ ^ 2) := fun x =>
        calc ρ 0 x ≤ C₁ * ρ₀ x := (hρ0ratio x).2
          _ ≤ C₁ * (Cg * Real.exp (-cg * ‖x‖ ^ 2)) := mul_le_mul_of_nonneg_left (hgauss x) hC₁.le
          _ = (C₁ * Cg) * Real.exp (-cg * ‖x‖ ^ 2) := by ring
          _ ≤ A * Real.exp (-cg * ‖x‖ ^ 2) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hCg0) (Real.exp_pos _).le
      have hg2 : ∀ x, ρ₀ x ≤ A * Real.exp (-cg * ‖x‖ ^ 2) := fun x =>
        calc ρ₀ x ≤ Cg * Real.exp (-cg * ‖x‖ ^ 2) := hgauss x
          _ = (1 * Cg) * Real.exp (-cg * ‖x‖ ^ 2) := by ring
          _ ≤ A * Real.exp (-cg * ‖x‖ ^ 2) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hCg0) (Real.exp_pos _).le
      -- `GibbsWellDefined` for both densities
      have hmem : β ∈ Set.Icc (β / 2) (2 * β) := ⟨by linarith, by linarith⟩
      obtain ⟨Cp1, hCp1⟩ := s66_gibbs_data hd hs0 hsd M L (β / 2) (2 * β) (by positivity) (by linarith)
      have hW₁ := (hCp1 (ρ 0) (hF.prob 0 le_rfl) (hF.bound 0 le_rfl) (hF.logm 0 le_rfl) N hN β hmem).1
      obtain ⟨L₀, hL₀⟩ := s66_gauss_data hd1 hp0 hCg0 hcg hgauss
      obtain ⟨Cp2, hCp2⟩ := s66_gibbs_data hd hs0 hsd Cg L₀ (β / 2) (2 * β) (by positivity) (by linarith)
      have hρ₀le : ∀ x, ρ₀ x ≤ Cg := fun x =>
        (hgauss x).trans (by
          have : Real.exp (-cg * ‖x‖ ^ 2) ≤ 1 := by
            rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖x‖]
          nlinarith)
      have hW₂ := (hCp2 ρ₀ hp0 hρ₀le (fun _ => hL₀) N hN β hmem).1
      obtain ⟨B, hB, hum⟩ := s66_pot_bdd hd hs0 hsd hρ0p hp0 hA0 hcg hg1 hg2 hW₁ hW₂
      exact s66_gibbs_finite (by omega) hβ hρ0p hp0 hκm hκ0 hρκ hW₁ hW₂ hum hB hLk (P.map X₀) hH0
    have hmfe0 : MFEFiniteW d s (P.map X₀) (wd (ρ 0)) := by
      haveI : IsProbabilityMeasure (P.map X₀) := inferInstance
      exact ((s66_split hd hs0 hsd M L β hβ (hF.prob 0 le_rfl) (hF.bound 0 le_rfl) (hF.logm 0 le_rfl) hN
        (P.map X₀)).1).1 hH0
    have hyp : WholeMFEHyp P D N t Λ 3 ρ X₀ W X :=
      { gradient := rfl
        pos_temp := inv_pos.2 hβ
        mf := hρ.solution t
        mf_reg := fun r' hr' => hΛ (ρ r') (hschw f0 hf0 ρ hρ r' hr'.1).1 (hschw f0 hf0 ρ hρ r' hr'.1).2
        r_ge := le_rfl
        Λ_ge := hΛ1
        pos_density := fun r' hr' x => (hprops r' hr'.1).2.1 x
        gibbs_entropy := hgibbs
        mfe_init := hmfe0
        brownian := hset.brownian
        indep := hset.indep
        sol := hset.sol t
        filtered := hset.filtered }
    have hDissT := hDiss D rfl hV3 hVB hVc N hN t Λ 3 ht P ρ X₀ W X hyp K hKi hLip
    have hKint' : ∫ r' in Set.Icc 0 t, K r' ≤ Kbar := by
      simpa [hKbar, hK] using hKint
    exact hcore q N hN t ht P ρ X₀ X K
      (fun r' hr' => ⟨hF.prob r' hr'.1, hF.bound r' hr'.1, hF.logm r' hr'.1⟩) hXm hX₀ hKi hK0 hKint' hLip
      hDissT hH0 t ⟨ht, le_rfl⟩

end HRS.MS.MovEnt

end
