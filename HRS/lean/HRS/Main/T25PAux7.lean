import HRS.Main.T25PAux6

/-!
# T25P, part 7: `‖Ψ_a‖_{L²} ≤ C J_N/√N`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.MovLog

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- Cauchy-Schwarz for `ℝ≥0∞`-series over a countable index. -/
theorem t25p_cs_tsum {ι : Type*} [Countable ι] (f g : ι → ℝ≥0∞) :
    (∑' i, f i * g i) ^ 2 ≤ (∑' i, f i ^ 2) * ∑' i, g i ^ 2 := by
  letI : MeasurableSpace ι := ⊤
  haveI : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have h := t25p_cs (Measure.count : Measure ι) (f := f) (g := g)
    (measurable_from_top).aemeasurable (measurable_from_top).aemeasurable
  simpa only [lintegral_count] using h

/-- `(x^{1/2})² = x` in `ℝ≥0∞`. -/
theorem t25p_rpow_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- `J_N ≥ 1`. -/
theorem t25p_J_ge_one (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {T' : ℝ}
    (hps : IsParticleSystem P htr.dyn T' X₀ W X) {p₀ : ℝ} (hp₀ : 1 < p₀)
    (hac : P.map X₀ ≪ modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))
    (hfin : eLpNorm ((P.map X₀).rnDeriv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))
      (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) < ⊤) :
    1 ≤ logMomentScale d s N p₀ (P.map X₀)
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) := by
  have hs0 := htr.hs0
  have hQ : ∀ r : ℝ, movT_Q (periodicRiesz d s) htr.dyn N ρ r =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ r)) :=
    fun r => movT_Q_eq_beta (D := htr.dyn) (β := β) (by simp [IsSmoothPositiveTrajectory.dyn, PDE.mfData]) N ρ r
  have hae : AEMeasurable X₀ P := (hps.sol.adapted 0).aemeasurable.congr hps.sol.init
  haveI : IsProbabilityMeasure (P.map X₀) := (Measure.isProbabilityMeasure_map_iff hae).2 inferInstance
  haveI : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) := by
    rw [← hQ 0]; exact movfin_movT_Q_isProb hN (movlog_traj htr 0) ⟨le_rfl, le_rfl⟩
  have hNδ1 : 1 ≤ (N : ℝ) * deltaN d s N := one_le_mul_deltaN hs0 N (by omega)
  have ha1 := movspec_one_le_eLpNorm_rnDeriv (P.map X₀)
    (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) hac hp₀.le
  have hat1 : 1 ≤ (eLpNorm ((P.map X₀).rnDeriv (modulatedGibbs (periodicRiesz d s) N β
      (withDensityReal (ρ 0)))) (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d s) N β
        (withDensityReal (ρ 0)))).toReal := by
    have := ENNReal.toReal_mono hfin.ne ha1
    simpa using this
  have := Real.log_nonneg hat1
  unfold logMomentScale
  linarith

/-- `∫ ‖f‖ₑ² = (eLpNorm f 2)²`. -/
theorem t25p_lintegral_sq_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) :
    ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P = eLpNorm f 2 P ^ 2 := by
  have h : eLpNorm f 2 P = (∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
    simp [ENNReal.rpow_two]
  rw [h, t25p_rpow_half_sq]

/-- Second moments of the mode forcings. -/
theorem t25p_mode_L2 (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (p₀ : ℝ) (hp₀ : 1 < p₀) :
    ∃ c2 : ℝ, 0 ≤ c2 ∧ ∀ N : ℕ, 2 ≤ N → ∀ T' : ℝ, 0 < T' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn T' X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        P.map X₀ ≪ modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)) →
        eLpNorm ((P.map X₀).rnDeriv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))
          (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) < ⊤ →
        ∀ (j : NonzeroLattice d), ∀ r ∈ Set.Icc (0 : ℝ) T',
          ∫⁻ ω, ‖t25p_y d s ρ X j r ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal
            ((c2 * Lattice.jp j.1 ^ 2 * logMomentScale d s N p₀ (P.map X₀)
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))) / Real.sqrt N) ^ 2 := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨cstar, A, hA, hw, hw0, hdom⟩ := movsx_hdom hd1 htr.hs0 htr.hsd
  obtain ⟨C₂, hC₂0, hC₂⟩ := T25.t25_moving_pair_moments hd htr p₀ hp₀ cstar hw 2 (by norm_num)
  obtain ⟨C₀, hC₀⟩ := Torus.cbNorm_realMode_le (d := d) 2
  set C₀' : ℝ := max C₀ 0 with hC₀'
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  refine ⟨C₂ * A * d * C₀', by positivity, ?_⟩
  intro N hN T' hT' Ω _ P _ X₀ W X hP hfilt hac hfin j r hr
  obtain ⟨ℱ, W', hF⟩ := hfilt
  set J : ℝ := logMomentScale d s N p₀ (P.map X₀)
    (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) with hJ
  have hJ1 : 1 ≤ J := t25p_J_ge_one hd htr hN P hP hp₀ hac hfin
  have hNpos : 0 < N := by omega
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hNpos)
  have hek : Torus.IsCk 2 (Torus.realMode j) := adjkd_isCk_of_smooth 2 (adjkd_isSmooth_realMode j)
  have hlip := dyncmp_lip_grad hek
  have hL0 : 0 ≤ (d : ℝ) * Torus.cbNorm 2 (Torus.realMode j) :=
    mul_nonneg (Nat.cast_nonneg d) (adjkd_cbNorm_nonneg 2 _)
  have hvc : Continuous (Torus.grad (Torus.realMode j)) :=
    Commutator.IsLipschitzVF.continuous hL0 hlip
  have hmeasK := dyncmp_commKernel_measurable
    (KernelGrad.measurable_periodicRieszGrad (by exact_mod_cast htr.hsd)) hvc.measurable
  have hsym : ∀ x y, commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j)) x y =
      commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j)) y x :=
    fun x y => dyncmp_commKernel_symm_gen htr.hsd _ x y
  have hmom := hC₂ N hN T' hT'.le P X₀ W X hP ⟨ℱ, W', hF⟩ hac hfin
    (A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j))) (mul_nonneg hA hL0)
    (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) hmeasK hsym
    (fun x y _ => hdom _ _ hL0 hlip x y) r hr
  -- `y = (1/√N) • (N F)`
  set Fm : Ω → ℝ := fun ω => (N : ℝ) * modulatedEnergy
    (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (X r.toNNReal ω)
    (withDensityReal (ρ r)) with hFm
  have hym : Measurable (fun ω => t25p_y d s ρ X j r ω) :=
    t25p_y_meas_omega hd htr hT' hF.progressive j hr
  have hyeq : (fun ω => t25p_y d s ρ X j r ω) = (1 / Real.sqrt N) • Fm := by
    funext ω
    simp only [t25p_y, hFm, Pi.smul_apply, smul_eq_mul]
    have hN' : (1 / Real.sqrt N) * (N : ℝ) = Real.sqrt N := by
      rw [div_mul_eq_mul_div, one_mul, div_eq_iff hsq.ne']
      exact (Real.mul_self_sqrt (Nat.cast_nonneg N)).symm
    rw [← mul_assoc, hN']
  rw [t25p_lintegral_sq_eq P hym.aestronglyMeasurable, hyeq, eLpNorm_const_smul]
  have h2 : eLpNorm Fm 2 P ≤ ENNReal.ofReal (C₂ * (A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j))) * J) := by
    have e2 : ENNReal.ofReal 2 = 2 := by norm_num
    simpa [hFm, e2] using hmom
  have hcb : Torus.cbNorm 2 (Torus.realMode j) ≤ C₀' * Lattice.jp j.1 ^ 2 :=
    (hC₀ j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hreal : C₂ * (A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j))) * J ≤
      C₂ * A * d * C₀' * Lattice.jp j.1 ^ 2 * J := by
    have h0 : 0 ≤ J := by linarith
    have : C₂ * (A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j))) ≤
        C₂ * A * d * C₀' * Lattice.jp j.1 ^ 2 := by
      calc C₂ * (A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j)))
          ≤ C₂ * (A * ((d : ℝ) * (C₀' * Lattice.jp j.1 ^ 2))) := by gcongr
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_right this h0
  have h3 : eLpNorm Fm 2 P ≤ ENNReal.ofReal (C₂ * A * d * C₀' * Lattice.jp j.1 ^ 2 * J) :=
    h2.trans (ENNReal.ofReal_le_ofReal hreal)
  have hcoef : ‖(1 / Real.sqrt N : ℝ)‖ₑ = ENNReal.ofReal (1 / Real.sqrt N) := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hcoef]
  have h4 : ENNReal.ofReal (1 / Real.sqrt N) * eLpNorm Fm 2 P ≤
      ENNReal.ofReal ((C₂ * A * d * C₀' * Lattice.jp j.1 ^ 2 * J) / Real.sqrt N) := by
    calc ENNReal.ofReal (1 / Real.sqrt N) * eLpNorm Fm 2 P
        ≤ ENNReal.ofReal (1 / Real.sqrt N) * ENNReal.ofReal (C₂ * A * d * C₀' * Lattice.jp j.1 ^ 2 * J) :=
          mul_le_mul' le_rfl h3
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  exact pow_le_pow_left' h4 2

end HRS.T25P
