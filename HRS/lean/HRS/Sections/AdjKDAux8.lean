import HRS.Sections.AdjKDAux7

/-!
# ADJKD, part 8: the `L¹` remainder bound `adjkd_remainder_L1` (packet B2)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- A time-independent smooth test function is a `C^{1,2}` test. -/
theorem adjkd_isC12_const (T : ℝ) (j : NonzeroLattice d) :
    IsC12Test T (fun _ : ℝ => Torus.realMode j) (fun _ _ => (0 : ℝ)) := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (Torus.realMode j)) :=
    adjkd_isSmooth_realMode j
  refine ⟨fun r _ => adjkd_isCk_of_smooth 2 (adjkd_isSmooth_realMode j), ?_, ?_, ?_⟩
  · intro i hi
    have := hs.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)
    exact this.comp continuous_snd
  · intro x r _
    exact hasDerivAt_const r _
  · exact continuous_const



theorem adjkd_y_measurable (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {T : ℝ} (hT : 0 ≤ T)
    (hd : 1 ≤ d) {N : ℕ} {Ω : Type u} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {X : ℝ≥0 → Ω → Config d N} (hX : IsProgressive ℱ (ofNNRealTime X))
    (hρP : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (ρ r)) (j : NonzeroLattice d) :
    Measurable (fun p : ℝ × Ω => Real.sqrt N * modulatedEnergy
      (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j)))
      (X (clampTI T p.1).toNNReal p.2) (withDensityReal (ρ (clampTI T p.1)))) := by
  have hjc := Q40b.q40b_jointCont hd htr T
  have h := Q40b.q40b_Fm_meas (N := N) (s := s) (ρ := ρ) (X := X) (ℱ := ℱ) hT htr.hsd
    (adjkd_isC12_const T j) hjc hρP hX
  exact h.const_mul (Real.sqrt N)

theorem adjkd_remainder_L1 (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn T X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : NonzeroLattice d,
          IntervalIntegrable (fun r =>
            Real.sqrt N * modulatedEnergy
              (commKernel (periodicRieszGrad d htr.dyn.s)
                (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k))))
              (X r.toNNReal ω) (withDensityReal (ρ r))) volume 0 t) ∧
        ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, (∑' k : NonzeroLattice d,
            ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m) * evolvingForcingCoord htr.dyn ρ X k t ω ^ 2)) ^
              (1 / 2 : ℝ) ∂P ≤
          ENNReal.ofReal (C * entropyScale d s N (P.map X₀)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / Real.sqrt N) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨cstar, A, hA, hw, hw0, hdom⟩ := movsx_hdom hd1 htr.hs0 htr.hsd
  obtain ⟨C₁, hC₁0, hC₁⟩ := T25.t25_pair_input.{u} hd htr cstar hw
  obtain ⟨Cr, cr, hCrpos, hcrpos, Vev, hdual, hplain, hdec, -⟩ := adjk_evolution_along_trajectory hd htr m
  have hCV : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cr := by
    intro u t hu hut
    refine (hdec u t hu hut).trans ?_
    have : Real.exp (-cr * (t - u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith [hCrpos]
  obtain ⟨C₀, hC₀⟩ := Torus.cbNorm_realMode_le (d := d) 2
  set C₀' : ℝ := max C₀ 0 with hC₀'
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  have hS : Summable fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-m) * Lattice.jp j.1 ^ (2 : ℝ) := by
    have := summable_jp_rpow (d := d) ((m - 2) / 2) (by linarith)
    refine this.congr fun j => ?_
    rw [← Real.rpow_add (Torus.jp_pos _)]
    congr 1
    ring
  set S₀ : ℝ := ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (-m) * Lattice.jp j.1 ^ (2 : ℝ) with hS₀
  have hS₀0 : 0 ≤ S₀ := tsum_nonneg fun j => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _)
    (Real.rpow_nonneg (Torus.jp_pos _).le _)
  set c : ℝ := C₁ * A * d * C₀' with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨Cr * S₀ * T * c, by positivity, ?_⟩
  intro N hN Ω _ P _ X₀ W X hP hfilt hfin
  obtain ⟨ℱ, W', hF⟩ := hfilt
  set B : ℝ := entropyScale d s N (P.map X₀)
    (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) with hB
  have hB0 : 0 ≤ B := by
    have hδ := one_le_mul_deltaN (d := d) htr.hs0 N (by omega)
    have := ENNReal.toReal_nonneg (a := relEntropy (P.map X₀)
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))
    rw [hB]; unfold entropyScale; linarith
  have hNpos : 0 < N := by omega
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hNpos)
  -- the data on `[0,T]`
  have hjc := Q40b.q40b_jointCont hd1 htr T
  have hMF := Q40b.q40b_meanField hd1 htr hT
  have hρP : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (ρ r) := fun r hr => hMF.density r hr
  -- the mode forcings
  obtain ⟨yfun, hyfun⟩ : ∃ yfun : NonzeroLattice d → ℝ → Ω → ℝ, ∀ j r ω, yfun j r ω =
      Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (X r.toNNReal ω)
        (withDensityReal (ρ r)) := ⟨fun j r ω => Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (X r.toNNReal ω)
        (withDensityReal (ρ r)), fun _ _ _ => rfl⟩
  have hmeasc : ∀ j, Measurable (fun p : ℝ × Ω => yfun j (clampTI T p.1) p.2) := by
    intro j
    have e : (fun p : ℝ × Ω => yfun j (clampTI T p.1) p.2) = fun p : ℝ × Ω => Real.sqrt N *
        modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j)))
          (X (clampTI T p.1).toNNReal p.2) (withDensityReal (ρ (clampTI T p.1))) :=
      funext fun p => hyfun _ _ _
    rw [e]
    exact adjkd_y_measurable htr hT.le hd1 hF.progressive hρP j
  have hae_mem : ∀ᵐ p ∂((volume.restrict (Set.Ioc (0 : ℝ) T)).prod P), p.1 ∈ Set.Ioc (0 : ℝ) T :=
    Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst)
      (ae_restrict_mem measurableSet_Ioc)
  have hAE : ∀ j, AEMeasurable (fun p : ℝ × Ω => yfun j p.1 p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) T)).prod P) := by
    intro j
    refine (hmeasc j).aemeasurable.congr ?_
    filter_upwards [hae_mem] with p hp
    rw [clampTI_of_mem ⟨hp.1.le, hp.2⟩]
  have hsect : ∀ j ω, AEMeasurable (fun r => yfun j r ω) (volume.restrict (Set.Ioc (0 : ℝ) T)) := by
    intro j ω
    have h0 : Measurable (fun r : ℝ => (r, ω)) := measurable_id.prodMk (measurable_const (a := ω))
    have h1 : Measurable (fun r : ℝ => yfun j (clampTI T r) ω) := (hmeasc j).comp h0
    refine h1.aemeasurable.congr ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_
    show yfun j (clampTI T r) ω = yfun j r ω
    rw [clampTI_of_mem ⟨hr.1.le, hr.2⟩]
  -- pair input for each mode and time
  have hpair : ∀ j : NonzeroLattice d, ∀ r ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ‖yfun j r ω‖ₑ ∂P ≤ ENNReal.ofReal
        ((C₁ * (A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j))) * B) / Real.sqrt N) := by
    intro j r hr
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
    obtain ⟨hint, hbd⟩ := hC₁ N hN T hT.le P X₀ W X hP ⟨ℱ, W', hF⟩ hfin
      (A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j))) (mul_nonneg hA hL0)
      (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) hmeasK hsym
      (fun x y _ => hdom _ _ hL0 hlip x y) r hr
    have hh := adjkd_y_bound hNpos hint hbd
    simp_rw [hyfun]
    exact hh
  -- the expectation of the series of mode integrals
  have hKc0 : 0 ≤ c * B / Real.sqrt N := by positivity
  have hmodeInt : ∀ j : NonzeroLattice d, ∫⁻ ω, (∫⁻ r in Set.Ioc (0 : ℝ) T, ‖yfun j r ω‖ₑ) ∂P ≤
      ENNReal.ofReal (c * B / Real.sqrt N * Lattice.jp j.1 ^ 2) * ENNReal.ofReal T := by
    intro j
    have hf : AEMeasurable (fun p : ℝ × Ω => ‖yfun j p.1 p.2‖ₑ)
        ((volume.restrict (Set.Ioc (0 : ℝ) T)).prod P) := (hAE j).enorm
    rw [← lintegral_lintegral_swap (μ := volume.restrict (Set.Ioc (0 : ℝ) T)) (ν := P)
      (f := fun r ω => ‖yfun j r ω‖ₑ) hf]
    have hcb : Torus.cbNorm 2 (Torus.realMode j) ≤ C₀' * Lattice.jp j.1 ^ 2 :=
      (hC₀ j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hreal : C₁ * (A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j))) * B / Real.sqrt N ≤
        c * B / Real.sqrt N * Lattice.jp j.1 ^ 2 := by
      calc C₁ * (A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j))) * B / Real.sqrt N
          ≤ C₁ * (A * ((d : ℝ) * (C₀' * Lattice.jp j.1 ^ 2))) * B / Real.sqrt N := by gcongr
        _ = c * B / Real.sqrt N * Lattice.jp j.1 ^ 2 := by rw [hc]; ring
    calc ∫⁻ r in Set.Ioc (0 : ℝ) T, ∫⁻ ω, ‖yfun j r ω‖ₑ ∂P
        ≤ ∫⁻ r in Set.Ioc (0 : ℝ) T, ENNReal.ofReal (c * B / Real.sqrt N * Lattice.jp j.1 ^ 2) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
          exact (hpair j r ⟨hr.1.le, hr.2⟩).trans (ENNReal.ofReal_le_ofReal hreal)
      _ = _ := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
  -- the series of mode integrals
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : Ω → ℝ≥0∞, ∀ ω, Ψ ω = ∑' j : NonzeroLattice d,
      ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) * ∫⁻ r in Set.Ioc (0 : ℝ) T, ‖yfun j r ω‖ₑ :=
    ⟨fun ω => ∑' j : NonzeroLattice d, ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
      ∫⁻ r in Set.Ioc (0 : ℝ) T, ‖yfun j r ω‖ₑ, fun _ => rfl⟩
  have hmeasj : ∀ j : NonzeroLattice d, AEMeasurable (fun ω => ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
      ∫⁻ r in Set.Ioc (0 : ℝ) T, ‖yfun j r ω‖ₑ) P := by
    intro j
    have hf : AEMeasurable (fun p : ℝ × Ω => ‖yfun j p.1 p.2‖ₑ)
        ((volume.restrict (Set.Ioc (0 : ℝ) T)).prod P) := (hAE j).enorm
    exact (hf.lintegral_prod_left').const_mul _
  have hΨmeas : AEMeasurable Ψ P := by
    have : Ψ = fun ω => ∑' j : NonzeroLattice d, ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
        ∫⁻ r in Set.Ioc (0 : ℝ) T, ‖yfun j r ω‖ₑ := funext hΨdef
    rw [this]
    exact AEMeasurable.ennreal_tsum hmeasj
  have hΨint : ∫⁻ ω, Ψ ω ∂P ≤ ENNReal.ofReal (S₀ * T * (c * B / Real.sqrt N)) := by
    simp_rw [hΨdef]
    rw [lintegral_tsum hmeasj]
    have hstep : ∀ j : NonzeroLattice d, ∫⁻ ω, (ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
        ∫⁻ r in Set.Ioc (0 : ℝ) T, ‖yfun j r ω‖ₑ) ∂P ≤ ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
          (ENNReal.ofReal (c * B / Real.sqrt N * Lattice.jp j.1 ^ 2) * ENNReal.ofReal T) := by
      intro j
      have hf : AEMeasurable (fun p : ℝ × Ω => ‖yfun j p.1 p.2‖ₑ)
          ((volume.restrict (Set.Ioc (0 : ℝ) T)).prod P) := (hAE j).enorm
      rw [lintegral_const_mul'' _ (hf.lintegral_prod_left')]
      exact mul_le_mul' le_rfl (hmodeInt j)
    refine (ENNReal.tsum_le_tsum hstep).trans (le_of_eq ?_)
    have hterm : ∀ j : NonzeroLattice d, ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
        (ENNReal.ofReal (c * B / Real.sqrt N * Lattice.jp j.1 ^ 2) * ENNReal.ofReal T) =
        ENNReal.ofReal ((Lattice.jp j.1 ^ (-m) * Lattice.jp j.1 ^ (2 : ℝ)) *
          (c * B / Real.sqrt N * T)) := by
      intro j
      have hw0 : 0 ≤ Lattice.jp j.1 ^ (-m) := Real.rpow_nonneg (Torus.jp_pos _).le _
      have hjp0 : 0 ≤ c * B / Real.sqrt N * Lattice.jp j.1 ^ 2 := by positivity
      rw [← ENNReal.ofReal_mul hjp0, ← ENNReal.ofReal_mul hw0, Real.rpow_two]
      congr 1
      ring
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by
      have := Real.rpow_nonneg (Torus.jp_pos j.1).le (-m)
      have h2 := Real.rpow_nonneg (Torus.jp_pos j.1).le (2 : ℝ)
      positivity) (hS.mul_right _), tsum_mul_right]
    congr 1
    ring
  have hΨfin : ∫⁻ ω, Ψ ω ∂P ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hΨint
  have hae : ∀ᵐ ω ∂P, Ψ ω < ⊤ := ae_lt_top' hΨmeas hΨfin
  have hpw : ∀ᵐ ω ∂P, (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : NonzeroLattice d,
      IntervalIntegrable (fun r => Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s)
          (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k)))) (X r.toNNReal ω)
        (withDensityReal (ρ r))) volume 0 t) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, (∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m) *
        (∫ r in (0 : ℝ)..t, -(Real.sqrt N * modulatedEnergy
          (commKernel (periodicRieszGrad d s)
            (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k)))) (X r.toNNReal ω)
          (withDensityReal (ρ r)))) ^ 2)) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal Cr * Ψ ω := by
    filter_upwards [hae] with ω hω
    have hy : ∀ j : NonzeroLattice d, AEMeasurable (fun r => Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j)))
        (X r.toNNReal ω) (withDensityReal (ρ r))) (volume.restrict (Set.Ioc (0 : ℝ) T)) := by
      intro j
      have h := hsect j ω
      simp only [hyfun] at h
      exact h
    have hΨne : ∑' j : NonzeroLattice d, ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
        ∫⁻ r in Set.Ioc (0 : ℝ) T, ‖Real.sqrt N * modulatedEnergy
          (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j)))
          (X r.toNNReal ω) (withDensityReal (ρ r))‖ₑ ≠ ⊤ := by
      have h := hω.ne
      rw [hΨdef] at h
      simp only [hyfun] at h
      exact h
    have hpath := adjkd_pathwise hd htr hm hT hdual (hplain T hT.le) hCV
      (fun r => X r.toNNReal ω) hy hΨne
    refine ⟨fun t ht k => (hpath t ht).1 k, fun t ht => ?_⟩
    refine (hpath t ht).2.trans (mul_le_mul' le_rfl ?_)
    rw [hΨdef]
    simp only [hyfun]
    exact le_rfl
  refine ⟨?_, ?_⟩
  · filter_upwards [hpw] with ω hω using hω.1
  · calc ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, (∑' k : NonzeroLattice d,
            ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m) * evolvingForcingCoord htr.dyn ρ X k t ω ^ 2)) ^
              (1 / 2 : ℝ) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal Cr * Ψ ω ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hpw] with ω hω
          refine iSup₂_le fun t ht => ?_
          exact hω.2 t ht.1
      _ = ENNReal.ofReal Cr * ∫⁻ ω, Ψ ω ∂P := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal Cr * ENNReal.ofReal (S₀ * T * (c * B / Real.sqrt N)) :=
          mul_le_mul' le_rfl hΨint
      _ = ENNReal.ofReal (Cr * S₀ * T * c * B / Real.sqrt N) := by
          rw [← ENNReal.ofReal_mul hCrpos.le]
          congr 1
          ring

end HRS.AdjK
