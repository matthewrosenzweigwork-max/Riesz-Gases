import HRS.MS.MovEntAux25
import HRS.MS.WsPrepAux4

/-!
# S21R packet 9: S6.6 at the explicit indices `(1, d/2 + 8)` (`MovEntAt`), from the dissipation inequality

`movEntAt_low_of_diss : SuperDiss d s → MovEntAt d s 1 (d / 2 + 8)`.  This is `mov_entropy_of_diss` (MovEntAux25) with its witnessed indices
`j = 1`, `m = d/2 + 8` exposed in the statement (the frozen `mov_entropy` has existential indices; see WsPrepAux4).  The proof is the proof
of `mov_entropy_of_diss` verbatim, without the first `refine` component.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovEnt

open HRS.Whole

local notation "wd" => Whole.withDensityReal

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem movEntAt_low_of_diss {s : ℝ} (hDiss : HRS.MS.MfeConf.SuperDiss d s) :
    MovEntAt d s 1 (d / 2 + 8) := by
  intro hd hs0 hsd β q hβ hq ρ₀ hρ _ _
  have hd1 : 1 ≤ d := by omega
  set m : ℕ := d / 2 + 8 with hmdef
  have hm : (d : ℝ) / 2 + (1 : ℕ) + 6 < m := by
    have : (d : ℝ) ≤ 2 * ((d / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : d ≤ 2 * (d / 2) + 1)
    rw [hmdef]; push_cast; linarith
  have hmK : ((3 : ℕ) : ℝ) + d / 2 + 4 < m := by
    have : (d : ℝ) ≤ 2 * ((d / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : d ≤ 2 * (d / 2) + 1)
    rw [hmdef]; push_cast; linarith
  obtain ⟨εstar, r, c₀, c, C₁, hε, hr, hc₀, hc, hC₁, hconc, hschwall⟩ :=
    HRS.MS.MovSch.mov_schwartz_proof hd hs0 hsd β q hβ hq 3 1 m le_rfl hm hmK ρ₀ hρ
  obtain ⟨CKL, hCKL⟩ := hschwall (d + 3)
  set B₁ : ℝ := |CKL| * εstar with hB₁
  have hB₁0 : 0 ≤ B₁ := by positivity
  have hschw : ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ 1 m εstar f0 → ∀ ρ : ℝ → Euc d → ℝ,
      MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ → ∀ t : ℝ, 0 ≤ t → ContDiff ℝ 3 (ρ t) ∧
        ∀ k : ℕ, k ≤ 3 → ∀ x : Euc d,
          movBracket x ^ (d + 3) * ‖iteratedFDeriv ℝ k (fun y => ρ t y - ρ₀ y) x‖ ≤ B₁ := by
    intro f0 hf0 ρ hρ' t ht
    obtain ⟨ρ', -, hρ'b⟩ := hCKL f0 hf0 ρ hρ'
    obtain ⟨hct, -, hb⟩ := hρ'b t ht
    refine ⟨by exact_mod_cast hct, fun k hk x => ?_⟩
    have h1 := hb k hk x
    have hbr : 0 ≤ movBracket x ^ (d + 3) := by have := s66_one_le_bracket x; positivity
    have h2 : movBracket x ^ (d + 3) * ‖iteratedFDeriv ℝ k (fun y => ρ t y - ρ₀ y) x‖ ≤
        movBracket x ^ (d + 3) * (‖iteratedFDeriv ℝ k (fun y => ρ t y - ρ₀ y) x‖ +
          ‖iteratedFDeriv ℝ k (ρ' t) x‖) := by
      refine mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) hbr
    have h3 : CKL * εstar * Real.exp (-c * t) ≤ B₁ := by
      have h4 : Real.exp (-c * t) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      have h5 : CKL * εstar * Real.exp (-c * t) ≤ |CKL| * εstar * Real.exp (-c * t) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hε.le) (Real.exp_pos _).le
      have h6 : |CKL| * εstar * Real.exp (-c * t) ≤ |CKL| * εstar * 1 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      linarith
    linarith
  refine ⟨εstar, r, c₀, c, C₁, hε, hr, hc₀, hc, hC₁, hconc, ?_⟩
  -- uniform data
  obtain ⟨M, L, E, c₁, hM1, hc₁, hE0, hfam⟩ := s66_fam_exists hd hs0 hsd hq hβ hρ hC₁ hc₀.le hconc
  obtain ⟨C₀, hC₀1, hcl0⟩ := s66_clause0 hd1 hs0 hsd M hM1
  obtain ⟨C, hC1, hcl1⟩ := s66_clause1 hd hs0 hsd hq hβ hρ hDiss hε hc₀ hc hC₁ hconc B₁ hB₁0 hschw
  refine ⟨C₀, ?_, ⟨C, ?_⟩, ?_⟩
  · intro f0 hf0 ρ hρ' N hN t ht X hX
    have hF := hfam f0 hf0 ρ hρ'
    exact hcl0 N hN (ρ t) (hF.prob t ht) (hF.bound t ht) (fun hs => (hF.logm t ht hs).1) X hX
  · intro f0 hf0 ρ hρ' N hN _ Ω _ P _ X₀ W X hset t ht
    exact hcl1 f0 hf0 ρ hρ' N hN P X₀ W X hset t ht
  · intro γ hγ
    obtain ⟨C₄, hC₄⟩ := s66_prep_entropy hd hs0 hsd M L β γ hβ hγ
    set C₄' : ℝ := max C₄ 0 with hC₄'
    have hC₄'0 : 0 ≤ C₄' := le_max_right _ _
    set C₁' : ℝ := C * (C₄' + 1) with hC₁'
    have hC₁'0 : 0 ≤ C₁' := by have : 0 ≤ C := by linarith
                               positivity
    obtain ⟨Cp, hCp0, hpb⟩ := s66_particle_bounds hd hs0 hsd M L E c₁ β C₁' hβ hc₁ hC₁'0
    have key : ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ 1 m εstar f0 → ∀ ρ : ℝ → Euc d → ℝ,
        MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ → ∀ N : ℕ, 2 ≤ N →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
          MovParticleSetup P d s q β N X₀ W X →
          MovPrepared d s N γ (wd (ρ 0)) (P.map X₀) → MovParticleBounds d s q β C₀ Cp ρ N P X := by
      intro f0 hf0 ρ hρ' N hN Ω _ P _ X₀ W X hset hprep
      have hF := hfam f0 hf0 ρ hρ'
      have hXm : ∀ t : ℝ≥0, Measurable (X t) := fun t => (hset.sol 0).adapted t
      refine hpb ρ hF N hN P X hXm ?_ q C₀ hC₀1
      intro t ht
      have h1 := hcl1 f0 hf0 ρ hρ' N hN P X₀ W X hset t ht
      have hX₀ : AEMeasurable X₀ P := by
        have h0 : AEMeasurable (X 0) P := (hXm 0).aemeasurable
        exact h0.congr (by filter_upwards [(hset.sol 0).init] with ζ hζ using hζ)
      haveI : IsProbabilityMeasure (P.map X₀) := inferInstance
      have h0 : relEntropy (P.map X₀) (Whole.modulatedGibbs (rieszKernel d s) N β (wd (ρ 0))) ≤
          ENNReal.ofReal (C₄ * N * deltaN d s N) :=
        hC₄ (ρ 0) (hF.prob 0 le_rfl) (hF.bound 0 le_rfl) (hF.logm 0 le_rfl) N hN (P.map X₀) hprep
      obtain ⟨hδ0, -, -, -⟩ := s66_delta_facts hd1 hs0 hsd (C₀ := 1) le_rfl hN
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hNδ : 0 ≤ (N : ℝ) * deltaN d s N := by positivity
      have hC0 : 0 ≤ C := by linarith
      calc relEntropy (P.map (X t.toNNReal)) (Whole.modulatedGibbs (rieszKernel d s) N β (wd (ρ t)))
          ≤ ENNReal.ofReal C * (relEntropy (P.map X₀)
              (Whole.modulatedGibbs (rieszKernel d s) N β (wd (ρ 0))) + ENNReal.ofReal (N * deltaN d s N)) := h1
        _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (C₄' * N * deltaN d s N) + ENNReal.ofReal (N * deltaN d s N)) := by
            refine mul_le_mul' le_rfl (add_le_add (h0.trans (ENNReal.ofReal_le_ofReal ?_)) le_rfl)
            have : C₄ * N * deltaN d s N ≤ C₄' * (N * deltaN d s N) := by
              have := mul_le_mul_of_nonneg_right (le_max_left C₄ 0) hNδ
              linarith
            linarith
        _ = ENNReal.ofReal (C₁' * N * deltaN d s N) := by
            have h5 : 0 ≤ C₄' * N * deltaN d s N := by positivity
            rw [← ENNReal.ofReal_add h5 hNδ, ← ENNReal.ofReal_mul hC0]
            congr 1
            simp only [hC₁']
            ring
    refine ⟨⟨Cp, fun f0 hf0 ρ hρ' N hN _ Ω _ P _ X₀ W X hset hprep =>
      key f0 hf0 ρ hρ' N hN P X₀ W X hset hprep⟩, ?_⟩
    intro T hT
    -- the pair term
    have hPpx : ∃ CP : ℝ, 0 ≤ CP ∧ ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ 1 m εstar f0 →
        ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ → ∀ N : ℕ, 2 ≤ N →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
          MovParticleSetup P d s q β N X₀ W X → MovPrepared d s N γ (wd (ρ 0)) (P.map X₀) →
          ∀ t : ℝ, 0 ≤ t → ∫⁻ ζ, ENNReal.ofReal (s66Pp s (X t.toNNReal ζ)) ∂P ≤ ENNReal.ofReal CP := by
      rcases hs0.eq_or_lt with h0 | hpos
      · subst h0
        refine ⟨1, zero_le_one, fun f0 hf0 ρ hρ' N hN Ω _ P _ X₀ W X hset hprep t ht => ?_⟩
        calc ∫⁻ ζ, ENNReal.ofReal (s66Pp (0 : ℝ) (X t.toNNReal ζ)) ∂P ≤ ∫⁻ ζ, ENNReal.ofReal 1 ∂P :=
              lintegral_mono fun ζ => ENNReal.ofReal_le_ofReal (s66_Pp_le_zero (by omega) _)
          _ = ENNReal.ofReal 1 := by rw [lintegral_const, measure_univ, mul_one]
      · obtain ⟨hp0, hpos0, Cg, cg, hcg, hgauss⟩ := s66_rho0_facts hd hs0 hsd hq hβ hρ
        have hCg0 : 0 ≤ Cg := by
          have h1 := hgauss 0
          have := hpos0 0
          simp at h1
          linarith
        set A : ℝ := max 1 C₁ * Cg with hA
        have hA0 : 0 ≤ A := by positivity
        obtain ⟨Bcm, hBcm⟩ := s66_cm_bdd hd1 hpos hsd hA0 hcg
        refine ⟨2 * Cp + 2 * max Bcm 0, by positivity, fun f0 hf0 ρ hρ' N hN Ω _ P _ X₀ W X hset hprep t ht => ?_⟩
        have hF := hfam f0 hf0 ρ hρ'
        have hprops := s66_class_props hconc hf0 hρ' hc₀.le
        have hρg : ∀ x, ρ t x ≤ A * Real.exp (-cg * ‖x‖ ^ 2) := fun x =>
          calc ρ t x ≤ C₁ * ρ₀ x := ((hprops t ht).2.2.1 x).2
            _ ≤ C₁ * (Cg * Real.exp (-cg * ‖x‖ ^ 2)) := mul_le_mul_of_nonneg_left (hgauss x) hC₁.le
            _ = (C₁ * Cg) * Real.exp (-cg * ‖x‖ ^ 2) := by ring
            _ ≤ A * Real.exp (-cg * ‖x‖ ^ 2) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hCg0) (Real.exp_pos _).le
        have hcm := hBcm (ρ t) (hF.prob t ht) hρg
        have hXm : ∀ t' : ℝ≥0, Measurable (X t') := fun t' => (hset.sol 0).adapted t'
        have hk := (key f0 hf0 ρ hρ' N hN P X₀ W X hset hprep t ht).2.1
        obtain ⟨hδ0, hδ1, -, -⟩ := s66_delta_facts hd1 hs0 hsd (C₀ := 1) le_rfl hN
        haveI : IsProbabilityMeasure (wd (ρ t)) := HRS.MS.Thm.cb_withDensityReal_isProb (hF.prob t ht)
        have hFm : Measurable (fun Z : EucConfig d N => rieszModulatedEnergy d s Z (wd (ρ t))) :=
          HRS.MS.Wr.wr9_measurable_pairEnergy (k := fun x y => rieszKernel d s (x - y)) (μ := wd (ρ t))
            (HRS.MS.Wr.wr9_rieszKernel_pair_meas (d := d) s)
        have hFmap : ∫⁻ ζ, ENNReal.ofReal |rieszModulatedEnergy d s (X t.toNNReal ζ) (wd (ρ t))| ∂P ≤
            ENNReal.ofReal (Cp * deltaN d s N) := by
          rw [← lintegral_map (hFm.abs.ennreal_ofReal) (hXm _)]
          exact hk
        have hpt : ∀ ζ, ENNReal.ofReal (s66Pp s (X t.toNNReal ζ)) ≤
            2 * ENNReal.ofReal |rieszModulatedEnergy d s (X t.toNNReal ζ) (wd (ρ t))| +
              ENNReal.ofReal (2 * max Bcm 0) := by
          intro ζ
          have h1 := s66_Pp_le_pos (by omega : 0 < N) hpos (μ := wd (ρ t)) (B := max Bcm 0)
            (fun x => (hcm x).trans (le_max_left _ _)) (X t.toNNReal ζ)
          refine (ENNReal.ofReal_le_ofReal h1).trans ?_
          refine ENNReal.ofReal_add_le.trans ?_
          rw [ENNReal.ofReal_mul (by norm_num)]
          simp
        calc ∫⁻ ζ, ENNReal.ofReal (s66Pp s (X t.toNNReal ζ)) ∂P
            ≤ ∫⁻ ζ, (2 * ENNReal.ofReal |rieszModulatedEnergy d s (X t.toNNReal ζ) (wd (ρ t))| +
                ENNReal.ofReal (2 * max Bcm 0)) ∂P := lintegral_mono hpt
          _ = 2 * ∫⁻ ζ, ENNReal.ofReal |rieszModulatedEnergy d s (X t.toNNReal ζ) (wd (ρ t))| ∂P +
                ENNReal.ofReal (2 * max Bcm 0) := by
              rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
                lintegral_const_mul' _ _ (by simp)]
          _ ≤ 2 * ENNReal.ofReal (Cp * deltaN d s N) + ENNReal.ofReal (2 * max Bcm 0) :=
              add_le_add (mul_le_mul' le_rfl hFmap) le_rfl
          _ ≤ ENNReal.ofReal (2 * Cp + 2 * max Bcm 0) := by
              have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
              rw [h2, ← ENNReal.ofReal_mul (by norm_num),
                ← ENNReal.ofReal_add (by positivity) (by positivity)]
              refine ENNReal.ofReal_le_ofReal ?_
              have := mul_le_mul_of_nonneg_left hδ1 hCp0
              nlinarith
    obtain ⟨CP, hCP0, hCP⟩ := hPpx
    obtain ⟨CT, hCT⟩ := s66_window (d := d) q β hβ hq hs0 Cp CP T hCp0 hCP0 hT
    refine ⟨CT, fun f0 hf0 ρ hρ' N hN _ Ω _ P _ X₀ W X hset hprep b hb => ?_⟩
    refine hCT N hN P X₀ W X hset (fun t ht => ?_) (fun t ht => hCP f0 hf0 ρ hρ' N hN P X₀ W X hset hprep t ht) b hb
    exact (key f0 hf0 ρ hρ' N hN P X₀ W X hset hprep t ht).2.2.2.2

end HRS.MS.MovEnt
