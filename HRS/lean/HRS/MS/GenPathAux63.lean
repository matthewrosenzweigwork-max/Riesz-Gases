import HRS.MS.GenPathAux62

/-!
# S5.6 packet P10c: assembly of `general_paths` (conditional on the a.e. measurability of the initial functional)

`s56_general_paths_core` is the frozen statement `HRS.Whole.general_paths` with ONE additional hypothesis `hη`:
`ζ ↦ η₀(ζ)(U^{0,t}φ_α)` is a.e. measurable (the frozen `gaussian_part` clause `law P G = multivariateGaussian 0 Σ` does not
force this when `Σ = 0`: `Measure.map f μ` of a non-a.e.-measurable `f` is the Dirac mass at `Classical.ofNonempty`, not `0`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_sigma_pos (b : WholeBounds d) (S : WholeSetup b) (N : ℕ) (hN : 1 ≤ N) : 0 < S.σ N := by
  unfold WholeSetup.σ sigmaScale
  have hκ := S.hκ N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  split_ifs with h
  · exact hκ
  · have hinv : 0 < S.invβ N := lt_of_le_of_ne (S.hinvβ N).1 (Ne.symm h)
    exact lt_min hκ (Real.sqrt_pos.2 (div_pos hNr hinv))

theorem s56_E_mono (b : WholeBounds d) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N) (hbv : b.Valid)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t)) :
    S.energyMomentE N 1 P X ≤ S.energyMomentE N 2 P X := by
  unfold WholeSetup.energyMomentE
  refine iSup_mono fun t => ?_
  have hm : Measurable fun ζ => ENNReal.ofReal |rieszModulatedEnergy d b.s (X (Real.toNNReal t) ζ)
      (HRS.Whole.withDensityReal (S.ρ N t)) + HRS.oN d b.s b.C₀ N| := by
    have h := s56_energy_meas b hbv S N
    have e := mrrClamp_of_mem t.2
    have h2 : Measurable fun x : EucConfig d N => rieszModulatedEnergy d b.s x
        (HRS.Whole.withDensityReal (S.ρ N t)) + HRS.oN d b.s b.C₀ N := by
      have := h.comp (measurable_const (a := (t : ℝ)).prodMk measurable_id)
      simpa [Function.comp_def, e] using this
    exact ENNReal.measurable_ofReal.comp (measurable_abs.comp (h2.comp (hXm _)))
  set f : Ω → ℝ≥0∞ := fun ζ => ENNReal.ofReal |rieszModulatedEnergy d b.s (X (Real.toNNReal t) ζ)
      (HRS.Whole.withDensityReal (S.ρ N t)) + HRS.oN d b.s b.C₀ N| with hf
  simp only [div_one, ENNReal.rpow_one]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P (p := 2) (q := 2) Real.HolderConjugate.two_two
    hm.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ, one_mul] at h
  exact h

theorem s56_w_nonneg (d : ℕ) (e M₂ : ℝ) (N : ℕ) (hM : 0 ≤ M₂) : 0 ≤ generalLocalizationRate d e M₂ N := by
  unfold generalLocalizationRate
  refine Real.iInf_nonneg fun R => ?_
  have hR : (1 : ℝ) ≤ R.1 := R.2
  have hR0 : 0 < R.1 := by linarith
  positivity

theorem s56_general_paths_core (b₀ : WholeBounds d) (hb : b₀.Valid) :
    ∃ C₀min : ℝ, ∀ b : WholeBounds d, b = { b₀ with C₀ := b.C₀ } → C₀min ≤ b.C₀ →
    ∃ C : ℝ, 0 < C ∧ ∀ S : WholeSetup b, ∀ (N : ℕ), 2 ≤ N →
      OscAdjointInput (S.coeff N) b.m b.T → ∀ (M₂ : ℝ)
      {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)), IsVectorBrownian P W →
      ∀ X : ℝ≥0 → Ω → EucConfig d N, IsWholeStrongSolution P (S.dyn N) b.T X₀ W X →
      (∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
        IsWholeFilteredSolution P ℱ W' W X) →
      ∀ η₀ : Ω → (Euc d → ℝ) → ℝ,
      IndepFun (fun ζ => (X₀ ζ, η₀ ζ)) (fun ζ t => W t ζ) P →
      (∀ t ∈ Set.Icc (0 : ℝ) b.T,
        ∫⁻ ζ, ENNReal.ofReal (HRS.Whole.pair (HRS.Whole.empirical (X (Real.toNNReal t) ζ))
          (fun x => ‖x‖ ^ 2)) ∂P ≤ ENNReal.ofReal M₂ ∧
        ENNReal.ofReal (HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) (fun x => ‖x‖ ^ 2)) ≤
          ENNReal.ofReal M₂) →
      ∀ Y : ℝ → Ω → OscDual d b.m,
      IsLinearFluctuationSolutionW P (S.coeff N) b.m (S.q N) b.T (fun ζ f => S.A N * η₀ ζ f) Y →
      (∀ (t : Set.Icc (0 : ℝ) b.T) (α : MultiIndex d),
        AEMeasurable (fun ζ => S.A N * η₀ ζ (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) P) →
      AEMeasurable (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)) P ∧
      AEMeasurable (processWindow b.m b.T 0 Y) P ∧
      ENNReal.ofReal (smoothDist 2 (law P (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)))
          (law P (processWindow b.m b.T 0 Y))) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (S.A N) * S.initialErrorE N 1 P X₀ η₀ +
          ENNReal.ofReal (S.σ N) * S.energyMomentE N 1 P X +
          ENNReal.ofReal (S.q N * generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N)) ∧
      wassersteinE 1 (law P (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)))
          (law P (processWindow b.m b.T 0 Y)) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (S.A N) * S.initialErrorE N 1 P X₀ η₀ +
          ENNReal.ofReal (S.σ N) * S.energyMomentE N 1 P X +
          ENNReal.ofReal (Real.sqrt (S.q N * generalLocalizationRate d
            (S.energyMomentE N 1 P X).toReal M₂ N))) ∧
      wassersteinE 2 (law P (flucPathW b.m b.T 0 (S.σ N) X (S.ρ N)))
          (law P (processWindow b.m b.T 0 Y)) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (S.A N) * S.initialErrorE N 2 P X₀ η₀ +
          ENNReal.ofReal (S.σ N) * S.energyMomentE N 2 P X +
          ENNReal.ofReal (Real.sqrt (S.q N * generalLocalizationRate d
            (S.energyMomentE N 1 P X).toReal M₂ N))) := by
  obtain ⟨C₀t, hTrAll⟩ := s56_trace_moment' b₀ hb
  obtain ⟨C₀r1, hR1All⟩ := s56_rem_moment' b₀ hb 1 (Or.inl rfl)
  obtain ⟨C₀r2, hR2All⟩ := s56_rem_moment' b₀ hb 2 (Or.inr rfl)
  refine ⟨max C₀t (max C₀r1 C₀r2), fun b hbeq hC0 => ?_⟩
  have hbv : b.Valid := s56_valid_of_eq hb hbeq
  have hT0 : 0 ≤ b.T := hbv.hT.le
  obtain ⟨Ctr', hCtr0, hTr⟩ := hTrAll b hbeq ((le_max_left _ _).trans hC0)
  obtain ⟨C1, hC10, hR1⟩ := hR1All b hbeq (((le_max_left _ _).trans (le_max_right _ _)).trans hC0)
  obtain ⟨C2, hC20, hR2⟩ := hR2All b hbeq (((le_max_right _ _).trans (le_max_right _ _)).trans hC0)
  obtain ⟨Ctr, Cmax, hOMall⟩ := HRS.MS.Star.general_orbits_maximal_proof b hbv
  obtain ⟨Cs, Cw1, Cw2, hCs0, hCw10, hCw20, hCmp⟩ := s56_compare' (d := d) b.m b.T hT0
  set C : ℝ := 1 + Cs * Ctr' + (Cw1 + Cw2) * Real.sqrt Ctr' + C1 + C2 with hCdef
  have hCpos : 0 < C := by
    have : 0 ≤ Cs * Ctr' := mul_nonneg hCs0 hCtr0
    have : 0 ≤ (Cw1 + Cw2) * Real.sqrt Ctr' := mul_nonneg (add_nonneg hCw10 hCw20) (Real.sqrt_nonneg _)
    linarith
  refine ⟨C, hCpos, fun S N hN hC M₂ Ω _ P _ X₀ W hW X hX hfilt η₀ hind hmom Y hY hη => ?_⟩
  obtain ⟨ℱ, W', hF⟩ := hfilt
  have hN1 : 1 ≤ N := by omega
  refine ⟨s56_fluc_aemeas b hbv S hN1 P X₀ W X hX, ?_, ?_⟩
  · have := HRS.GF.gfb4_aemeasurable_windowPath P hT0 Y (fun t _ => hY.meas t) hY.cont
    rwa [← s56_wpo_eq_windowPath] at this
  have hσ0 : ENNReal.ofReal (S.σ N) ≠ 0 := (ENNReal.ofReal_pos.2 (s56_sigma_pos b S N hN1)).ne'
  have hC0' : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.2 hCpos).ne'
  by_cases hE1 : S.energyMomentE N 1 P X = ⊤
  · have hE2 : S.energyMomentE N 2 P X = ⊤ :=
      top_unique (hE1 ▸ s56_E_mono b S hN1 hbv P X (fun t => hX.adapted t))
    refine ⟨?_, ?_, ?_⟩
    · rw [hE1]
      simp only [ENNReal.mul_top hσ0, add_top, top_add, ENNReal.mul_top hC0']
      exact le_top
    · rw [hE1]
      simp only [ENNReal.mul_top hσ0, add_top, top_add, ENNReal.mul_top hC0']
      exact le_top
    · rw [hE2]
      simp only [ENNReal.mul_top hσ0, add_top, top_add, ENNReal.mul_top hC0']
      exact le_top
  have hM₂pos : 0 < M₂ := by
    obtain ⟨-, h2⟩ := hmom 0 ⟨le_rfl, hT0⟩
    have hpos := s56_secondMoment_pos (d := d) (by have := hbv.hd; omega) ((S.mf N).density 0 ⟨le_rfl, hT0⟩)
      ((S.mf N).second_moment 0 ⟨le_rfl, hT0⟩)
    by_contra hle
    push_neg at hle
    rw [ENNReal.ofReal_of_nonpos hle] at h2
    have : ENNReal.ofReal (HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0)) (fun x => ‖x‖ ^ 2)) = 0 :=
      le_antisymm h2 bot_le
    exact (ENNReal.ofReal_pos.2 hpos).ne' this
  obtain ⟨hsm, hw1, hw2⟩ := s56_master b hbv S hN hC (hOMall S N) hCmp hCtr0 hTr hR1 hR2 M₂ hM₂pos.le P X₀ W X
    hX ℱ W' hF η₀ hmom hE1 Y hY.meas hY hη
  set w : ℝ := generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N with hw
  have hw0 : 0 ≤ w := s56_w_nonneg d _ M₂ N hM₂pos.le
  have hq0 : 0 ≤ S.q N := s56_q_nonneg b S N hN1
  have hqw : 0 ≤ S.q N * w := mul_nonneg hq0 hw0
  set Qw : ℝ≥0∞ := ENNReal.ofReal (S.q N * w) with hQw
  set Eσ1 : ℝ≥0∞ := ENNReal.ofReal (S.σ N) * S.energyMomentE N 1 P X with hEσ1
  set Eσ2 : ℝ≥0∞ := ENNReal.ofReal (S.σ N) * S.energyMomentE N 2 P X with hEσ2
  have hcoef : ∀ (c : ℝ), c ≤ C → ENNReal.ofReal c ≤ ENNReal.ofReal C := fun c hc =>
    ENNReal.ofReal_le_ofReal hc
  have hone : (1 : ℝ) ≤ C := by
    have : 0 ≤ Cs * Ctr' := mul_nonneg hCs0 hCtr0
    have : 0 ≤ (Cw1 + Cw2) * Real.sqrt Ctr' := mul_nonneg (add_nonneg hCw10 hCw20) (Real.sqrt_nonneg _)
    linarith
  have hones : ∀ x : ℝ≥0∞, x ≤ ENNReal.ofReal C * x := fun x => by
    calc x = 1 * x := (one_mul x).symm
      _ ≤ ENNReal.ofReal C * x := by
        gcongr
        simpa using ENNReal.ofReal_le_ofReal hone
  have hC1 : ENNReal.ofReal (C1 * S.σ N) = ENNReal.ofReal C1 * ENNReal.ofReal (S.σ N) :=
    ENNReal.ofReal_mul hC10
  have hC2 : ENNReal.ofReal (C2 * S.σ N) = ENNReal.ofReal C2 * ENNReal.ofReal (S.σ N) :=
    ENNReal.ofReal_mul hC20
  refine ⟨?_, ?_, ?_⟩
  · -- smoothness
    have e1 : ENNReal.ofReal Cs * ENNReal.ofReal (Ctr' * S.q N * w) = ENNReal.ofReal (Cs * Ctr') * Qw := by
      rw [hQw, ← ENNReal.ofReal_mul hCs0, ← ENNReal.ofReal_mul (mul_nonneg hCs0 hCtr0)]
      congr 1; ring
    have e2 : ENNReal.ofReal (C1 * S.σ N) * S.energyMomentE N 1 P X = ENNReal.ofReal C1 * Eσ1 := by
      rw [hC1, mul_assoc]
    rw [e1, e2] at hsm
    have hle1 : ENNReal.ofReal (Cs * Ctr') ≤ ENNReal.ofReal C := hcoef _ (by
      have : 0 ≤ (Cw1 + Cw2) * Real.sqrt Ctr' := mul_nonneg (add_nonneg hCw10 hCw20) (Real.sqrt_nonneg _)
      have : 0 ≤ C1 := hC10
      have : 0 ≤ C2 := hC20
      linarith)
    have hle2 : ENNReal.ofReal C1 ≤ ENNReal.ofReal C := hcoef _ (by
      have : 0 ≤ Cs * Ctr' := mul_nonneg hCs0 hCtr0
      have : 0 ≤ (Cw1 + Cw2) * Real.sqrt Ctr' := mul_nonneg (add_nonneg hCw10 hCw20) (Real.sqrt_nonneg _)
      have : 0 ≤ C2 := hC20
      linarith)
    calc _ ≤ _ := hsm
      _ ≤ ENNReal.ofReal C * Qw + ENNReal.ofReal C * Eσ1 +
          ENNReal.ofReal C * (ENNReal.ofReal (S.A N) * S.initialErrorE N 1 P X₀ η₀) := by
        exact add_le_add (add_le_add (mul_le_mul' hle1 le_rfl) (mul_le_mul' hle2 le_rfl)) (hones _)
      _ = _ := by ring
  · -- the `W_1` estimate
    set Sq : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (S.q N * w)) with hSq
    have hx : 0 ≤ Ctr' * S.q N * w := by
      have : Ctr' * S.q N * w = Ctr' * (S.q N * w) := by ring
      rw [this]; exact mul_nonneg hCtr0 hqw
    have hsqrt : ∀ Cw : ℝ, 0 ≤ Cw → ENNReal.ofReal Cw * (ENNReal.ofReal (Ctr' * S.q N * w)) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (Cw * Real.sqrt Ctr') * Sq := by
      intro Cw hCw
      rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num), ← Real.sqrt_eq_rpow,
        show Ctr' * S.q N * w = Ctr' * (S.q N * w) by ring, Real.sqrt_mul hCtr0,
        ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← mul_assoc, ← ENNReal.ofReal_mul hCw]
    rw [hsqrt Cw1 hCw10] at hw1
    have e2 : ENNReal.ofReal (C1 * S.σ N) * S.energyMomentE N 1 P X = ENNReal.ofReal C1 * Eσ1 := by
      rw [hC1, mul_assoc]
    rw [e2] at hw1
    have hle1 : ENNReal.ofReal (Cw1 * Real.sqrt Ctr') ≤ ENNReal.ofReal C := hcoef _ (by
      have : 0 ≤ Cs * Ctr' := mul_nonneg hCs0 hCtr0
      have : Cw1 * Real.sqrt Ctr' ≤ (Cw1 + Cw2) * Real.sqrt Ctr' :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
      have : 0 ≤ C1 := hC10
      have : 0 ≤ C2 := hC20
      linarith)
    have hle2 : ENNReal.ofReal C1 ≤ ENNReal.ofReal C := hcoef _ (by
      have : 0 ≤ Cs * Ctr' := mul_nonneg hCs0 hCtr0
      have : 0 ≤ (Cw1 + Cw2) * Real.sqrt Ctr' := mul_nonneg (add_nonneg hCw10 hCw20) (Real.sqrt_nonneg _)
      have : 0 ≤ C2 := hC20
      linarith)
    calc _ ≤ _ := hw1
      _ ≤ ENNReal.ofReal C * Sq + ENNReal.ofReal C * Eσ1 +
          ENNReal.ofReal C * (ENNReal.ofReal (S.A N) * S.initialErrorE N 1 P X₀ η₀) := by
        exact add_le_add (add_le_add (mul_le_mul' hle1 le_rfl) (mul_le_mul' hle2 le_rfl)) (hones _)
      _ = _ := by ring
  · -- the `W_2` estimate
    set Sq : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (S.q N * w)) with hSq
    have hx : 0 ≤ Ctr' * S.q N * w := by
      have : Ctr' * S.q N * w = Ctr' * (S.q N * w) := by ring
      rw [this]; exact mul_nonneg hCtr0 hqw
    have hsqrt : ∀ Cw : ℝ, 0 ≤ Cw → ENNReal.ofReal Cw * (ENNReal.ofReal (Ctr' * S.q N * w)) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (Cw * Real.sqrt Ctr') * Sq := by
      intro Cw hCw
      rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num), ← Real.sqrt_eq_rpow,
        show Ctr' * S.q N * w = Ctr' * (S.q N * w) by ring, Real.sqrt_mul hCtr0,
        ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← mul_assoc, ← ENNReal.ofReal_mul hCw]
    rw [hsqrt Cw2 hCw20] at hw2
    have e2 : ENNReal.ofReal (C2 * S.σ N) * S.energyMomentE N 2 P X = ENNReal.ofReal C2 * Eσ2 := by
      rw [hC2, mul_assoc]
    rw [e2] at hw2
    have hle1 : ENNReal.ofReal (Cw2 * Real.sqrt Ctr') ≤ ENNReal.ofReal C := hcoef _ (by
      have : 0 ≤ Cs * Ctr' := mul_nonneg hCs0 hCtr0
      have : Cw2 * Real.sqrt Ctr' ≤ (Cw1 + Cw2) * Real.sqrt Ctr' :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
      have : 0 ≤ C1 := hC10
      have : 0 ≤ C2 := hC20
      linarith)
    have hle2 : ENNReal.ofReal C2 ≤ ENNReal.ofReal C := hcoef _ (by
      have : 0 ≤ Cs * Ctr' := mul_nonneg hCs0 hCtr0
      have : 0 ≤ (Cw1 + Cw2) * Real.sqrt Ctr' := mul_nonneg (add_nonneg hCw10 hCw20) (Real.sqrt_nonneg _)
      have : 0 ≤ C1 := hC10
      linarith)
    calc _ ≤ _ := hw2
      _ ≤ ENNReal.ofReal C * Sq + ENNReal.ofReal C * Eσ2 +
          ENNReal.ofReal C * (ENNReal.ofReal (S.A N) * S.initialErrorE N 2 P X₀ η₀) := by
        exact add_le_add (add_le_add (mul_le_mul' hle1 le_rfl) (mul_le_mul' hle2 le_rfl)) (hones _)
      _ = _ := by ring

end HRS.MS.GenPath
