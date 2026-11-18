import HRS.Main.T25PAux4

/-!
# T25P, part 5: `E Ψ_a ≤ C B_N/√N` (the `L¹` remainder bound, uniform in the window start)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- Joint measurability of the mode forcings on `[0,T']` (clamped), for a filtered strong solution. -/
theorem t25p_y_joint_meas (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {T' : ℝ} (hT' : 0 < T')
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {X : ℝ≥0 → Ω → Config d N} (hX : IsProgressive ℱ (ofNNRealTime X)) (j : NonzeroLattice d) :
    Measurable (fun p : ℝ × Ω => t25p_y d s ρ X j (clampTI T' p.1) p.2) := by
  have hd1 : 1 ≤ d := by omega
  have hMF := Q40b.q40b_meanField hd1 htr hT'
  have hρP : ∀ r ∈ Set.Icc (0 : ℝ) T', IsProbDensity (ρ r) := fun r hr => hMF.density r hr
  exact adjkd_y_measurable htr hT'.le hd1 hX hρP j

/-- Sectionwise a.e. measurability on `Ioc 0 T'` (jointly and in `r` for fixed `ω`). -/
theorem t25p_y_aemeas (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {T' : ℝ} (hT' : 0 < T')
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {X : ℝ≥0 → Ω → Config d N} (hX : IsProgressive ℱ (ofNNRealTime X)) (j : NonzeroLattice d) :
    AEMeasurable (fun p : ℝ × Ω => t25p_y d s ρ X j p.1 p.2) ((volume.restrict (Set.Ioc (0 : ℝ) T')).prod P) ∧
    ∀ ω, AEMeasurable (fun r => t25p_y d s ρ X j r ω) (volume.restrict (Set.Ioc (0 : ℝ) T')) := by
  have hmeasc := t25p_y_joint_meas hd htr hT' hX j
  have hae_mem : ∀ᵐ p ∂((volume.restrict (Set.Ioc (0 : ℝ) T')).prod P), p.1 ∈ Set.Ioc (0 : ℝ) T' :=
    Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst)
      (ae_restrict_mem measurableSet_Ioc)
  refine ⟨?_, ?_⟩
  · refine hmeasc.aemeasurable.congr ?_
    filter_upwards [hae_mem] with p hp
    rw [clampTI_of_mem ⟨hp.1.le, hp.2⟩]
  · intro ω
    have h0 : Measurable (fun r : ℝ => (r, ω)) := measurable_id.prodMk (measurable_const (a := ω))
    have h1 : Measurable (fun r : ℝ => t25p_y d s ρ X j (clampTI T' r) ω) :=
      Measurable.comp (g := fun p : ℝ × Ω => t25p_y d s ρ X j (clampTI T' p.1) p.2)
        (f := fun r : ℝ => (r, ω)) hmeasc h0
    refine h1.aemeasurable.congr ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun r hr => ?_
    show t25p_y d s ρ X j (clampTI T' r) ω = t25p_y d s ρ X j r ω
    rw [clampTI_of_mem ⟨hr.1.le, hr.2⟩]

/-- Pair input for the mode forcings: `E|y_j(r)| ≤ c₀ ⟨j⟩² B_N/√N` for all `r ∈ [0,T']`. -/
theorem t25p_mode_L1 (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) :
    ∃ c0 : ℝ, 0 ≤ c0 ∧ ∀ N : ℕ, 2 ≤ N → ∀ T' : ℝ, 0 ≤ T' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn T' X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        ∀ (j : NonzeroLattice d), ∀ r ∈ Set.Icc (0 : ℝ) T',
          ∫⁻ ω, ‖t25p_y d s ρ X j r ω‖ₑ ∂P ≤ ENNReal.ofReal
            ((c0 * Lattice.jp j.1 ^ 2 * entropyScale d s N (P.map X₀)
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))) / Real.sqrt N) := by
  classical
  have hd1 : 1 ≤ d := by omega
  obtain ⟨cstar, A, hA, hw, hw0, hdom⟩ := movsx_hdom hd1 htr.hs0 htr.hsd
  obtain ⟨C₁, hC₁0, hC₁⟩ := T25.t25_pair_input hd htr cstar hw
  obtain ⟨C₀, hC₀⟩ := Torus.cbNorm_realMode_le (d := d) 2
  set C₀' : ℝ := max C₀ 0 with hC₀'
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  refine ⟨C₁ * A * d * C₀', by positivity, ?_⟩
  intro N hN T' hT' Ω _ P _ X₀ W X hP hfilt hfin j r hr
  obtain ⟨ℱ, W', hF⟩ := hfilt
  set B : ℝ := entropyScale d s N (P.map X₀)
    (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) with hB
  have hB0 : 0 ≤ B := by
    have hδ := one_le_mul_deltaN (d := d) htr.hs0 N (by omega)
    have := ENNReal.toReal_nonneg (a := relEntropy (P.map X₀)
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))
    rw [hB]; unfold entropyScale; linarith
  have hNpos : 0 < N := by omega
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
  obtain ⟨hint, hbd⟩ := hC₁ N hN T' hT' P X₀ W X hP ⟨ℱ, W', hF⟩ hfin
    (A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j))) (mul_nonneg hA hL0)
    (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) hmeasK hsym
    (fun x y _ => hdom _ _ hL0 hlip x y) r hr
  have hh := adjkd_y_bound hNpos hint hbd
  have hcb : Torus.cbNorm 2 (Torus.realMode j) ≤ C₀' * Lattice.jp j.1 ^ 2 :=
    (hC₀ j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hreal : C₁ * (A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j))) * B / Real.sqrt N ≤
      (C₁ * A * d * C₀' * Lattice.jp j.1 ^ 2 * B) / Real.sqrt N := by
    have : C₁ * (A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j))) * B ≤
        C₁ * A * d * C₀' * Lattice.jp j.1 ^ 2 * B := by
      calc C₁ * (A * ((d : ℝ) * Torus.cbNorm 2 (Torus.realMode j))) * B
          ≤ C₁ * (A * ((d : ℝ) * (C₀' * Lattice.jp j.1 ^ 2))) * B := by gcongr
        _ = _ := by ring
    exact div_le_div_of_nonneg_right this (Real.sqrt_nonneg _)
  unfold t25p_y
  exact hh.trans (ENNReal.ofReal_le_ofReal hreal)

/-- The `L¹` bound for `Ψ_a`, uniformly in the window start `a`. -/
theorem t25p_Psi_L1 (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) + 2 < m) {cr : ℝ} (hcr : 0 < cr) {T : ℝ} (hT : 0 < T) :
    ∃ CΨ : ℝ, 0 ≤ CΨ ∧ ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, 0 ≤ a →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        ∫⁻ ω, t25p_Psi d s ρ m cr a T X ω ∂P ≤ ENNReal.ofReal
          ((CΨ * entropyScale d s N (P.map X₀)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)))) / Real.sqrt N) := by
  classical
  obtain ⟨c0, hc00, hc0⟩ := t25p_mode_L1 hd htr
  have hS : Summable fun j : NonzeroLattice d => Lattice.jp j.1 ^ (-m) * Lattice.jp j.1 ^ (2 : ℝ) := by
    have := summable_jp_rpow (d := d) ((m - 2) / 2) (by linarith)
    refine this.congr fun j => ?_
    rw [← Real.rpow_add (Torus.jp_pos _)]
    congr 1
    ring
  set S₀ : ℝ := ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (-m) * Lattice.jp j.1 ^ (2 : ℝ) with hS₀
  have hS₀0 : 0 ≤ S₀ := tsum_nonneg fun j => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _)
    (Real.rpow_nonneg (Torus.jp_pos _).le _)
  refine ⟨S₀ * (1 / cr + T) * c0, by positivity, ?_⟩
  intro N hN a ha Ω _ P _ X₀ W X hP hfilt hfin
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
  have hT' : 0 < a + T := by linarith
  have hKc0 : 0 ≤ c0 * B / Real.sqrt N := by positivity
  have hAE : ∀ j, AEMeasurable (fun p : ℝ × Ω => t25p_y d s ρ X j p.1 p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) (a + T))).prod P) := fun j =>
    (t25p_y_aemeas hd htr hT' P hF.progressive j).1
  -- the weighted mode integrals
  have hwm : Measurable (t25p_w cr a) := (t25p_w_cont cr a).measurable
  have hmodeInt : ∀ j : NonzeroLattice d,
      ∫⁻ ω, (∫⁻ r in Set.Ioc (0 : ℝ) (a + T), ENNReal.ofReal (t25p_w cr a r) * ‖t25p_y d s ρ X j r ω‖ₑ) ∂P ≤
      ENNReal.ofReal (c0 * B / Real.sqrt N * Lattice.jp j.1 ^ 2) * ENNReal.ofReal (1 / cr + T) := by
    intro j
    have hf : AEMeasurable (fun p : ℝ × Ω => ENNReal.ofReal (t25p_w cr a p.1) * ‖t25p_y d s ρ X j p.1 p.2‖ₑ)
        ((volume.restrict (Set.Ioc (0 : ℝ) (a + T))).prod P) :=
      (ENNReal.measurable_ofReal.comp (hwm.comp measurable_fst)).aemeasurable.mul (hAE j).enorm
    rw [← lintegral_lintegral_swap (μ := volume.restrict (Set.Ioc (0 : ℝ) (a + T))) (ν := P)
      (f := fun r ω => ENNReal.ofReal (t25p_w cr a r) * ‖t25p_y d s ρ X j r ω‖ₑ) hf]
    have hpair : ∀ r ∈ Set.Icc (0 : ℝ) (a + T), ∫⁻ ω, ‖t25p_y d s ρ X j r ω‖ₑ ∂P ≤
        ENNReal.ofReal (c0 * B / Real.sqrt N * Lattice.jp j.1 ^ 2) := by
      intro r hr
      have := hc0 N hN (a + T) hT'.le P X₀ W X hP ⟨ℱ, W', hF⟩ hfin j r hr
      refine this.trans (le_of_eq ?_)
      congr 1
      ring
    calc ∫⁻ r in Set.Ioc (0 : ℝ) (a + T), ∫⁻ ω, ENNReal.ofReal (t25p_w cr a r) * ‖t25p_y d s ρ X j r ω‖ₑ ∂P
        = ∫⁻ r in Set.Ioc (0 : ℝ) (a + T), ENNReal.ofReal (t25p_w cr a r) *
            ∫⁻ ω, ‖t25p_y d s ρ X j r ω‖ₑ ∂P := by
          refine lintegral_congr fun r => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ∫⁻ r in Set.Ioc (0 : ℝ) (a + T), ENNReal.ofReal (t25p_w cr a r) *
            ENNReal.ofReal (c0 * B / Real.sqrt N * Lattice.jp j.1 ^ 2) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
          exact mul_le_mul' le_rfl (hpair r ⟨hr.1.le, hr.2⟩)
      _ = (∫⁻ r in Set.Ioc (0 : ℝ) (a + T), ENNReal.ofReal (t25p_w cr a r)) *
            ENNReal.ofReal (c0 * B / Real.sqrt N * Lattice.jp j.1 ^ 2) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (1 / cr + T) * ENNReal.ofReal (c0 * B / Real.sqrt N * Lattice.jp j.1 ^ 2) :=
          mul_le_mul' (t25p_w_lintegral_le hcr ha hT.le) le_rfl
      _ = _ := mul_comm _ _
  have hmeasj : ∀ j : NonzeroLattice d, AEMeasurable (fun ω => ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
      ∫⁻ r in Set.Ioc (0 : ℝ) (a + T), ENNReal.ofReal (t25p_w cr a r) * ‖t25p_y d s ρ X j r ω‖ₑ) P := by
    intro j
    have hf : AEMeasurable (fun p : ℝ × Ω => ENNReal.ofReal (t25p_w cr a p.1) * ‖t25p_y d s ρ X j p.1 p.2‖ₑ)
        ((volume.restrict (Set.Ioc (0 : ℝ) (a + T))).prod P) :=
      (ENNReal.measurable_ofReal.comp (hwm.comp measurable_fst)).aemeasurable.mul (hAE j).enorm
    exact (hf.lintegral_prod_left').const_mul _
  unfold t25p_Psi
  rw [lintegral_tsum hmeasj]
  have hstep : ∀ j : NonzeroLattice d, ∫⁻ ω, (ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
      ∫⁻ r in Set.Ioc (0 : ℝ) (a + T), ENNReal.ofReal (t25p_w cr a r) * ‖t25p_y d s ρ X j r ω‖ₑ) ∂P ≤
        ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
          (ENNReal.ofReal (c0 * B / Real.sqrt N * Lattice.jp j.1 ^ 2) * ENNReal.ofReal (1 / cr + T)) := by
    intro j
    have hf : AEMeasurable (fun p : ℝ × Ω => ENNReal.ofReal (t25p_w cr a p.1) * ‖t25p_y d s ρ X j p.1 p.2‖ₑ)
        ((volume.restrict (Set.Ioc (0 : ℝ) (a + T))).prod P) :=
      (ENNReal.measurable_ofReal.comp (hwm.comp measurable_fst)).aemeasurable.mul (hAE j).enorm
    rw [lintegral_const_mul'' _ (hf.lintegral_prod_left')]
    exact mul_le_mul' le_rfl (hmodeInt j)
  refine (ENNReal.tsum_le_tsum hstep).trans (le_of_eq ?_)
  have hterm : ∀ j : NonzeroLattice d, ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
      (ENNReal.ofReal (c0 * B / Real.sqrt N * Lattice.jp j.1 ^ 2) * ENNReal.ofReal (1 / cr + T)) =
      ENNReal.ofReal ((Lattice.jp j.1 ^ (-m) * Lattice.jp j.1 ^ (2 : ℝ)) *
        (c0 * B / Real.sqrt N * (1 / cr + T))) := by
    intro j
    have hw0 : 0 ≤ Lattice.jp j.1 ^ (-m) := Real.rpow_nonneg (Torus.jp_pos _).le _
    have hjp0 : 0 ≤ c0 * B / Real.sqrt N * Lattice.jp j.1 ^ 2 := by positivity
    have hcT : 0 ≤ 1 / cr + T := by positivity
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

end HRS.T25P
