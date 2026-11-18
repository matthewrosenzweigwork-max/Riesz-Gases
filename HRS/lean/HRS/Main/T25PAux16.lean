import HRS.Main.T25PAux15

/-!
# T25P, part 16: the expected trace-norm discrepancy of the covariations
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.Uniform.Q48c

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem t25p_trace_L1 (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) + 2 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ T' : ℝ, 0 < T' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn T' X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        ∀ r ∈ Set.Icc (0 : ℝ) T',
          ∫⁻ ω, ENNReal.ofReal (traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
              covForm m β⁻¹ (withDensityReal (ρ r)))) ∂P ≤
            ENNReal.ofReal (C * Real.sqrt (entropyScale d s N (P.map X₀)
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / N)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hm2 : (d : ℝ) + 1 < m := by linarith
  have hq0 : 0 ≤ β⁻¹ := inv_nonneg.2 htr.hβ.le
  obtain ⟨Cl, hCl0, hCl⟩ := T25.t25_linear_input hd htr
  have hs := summable_s (d := d) (m := m) hm2
  set S₂ : ℝ := ∑' k : NonzeroLattice d, wt m k * Lattice.jp k.1 with hS₂
  have hnn : ∀ k : NonzeroLattice d, 0 ≤ wt m k * Lattice.jp k.1 := fun k =>
    mul_nonneg (wt_pos k).le (Torus.jp_pos k.1).le
  have hS₂0 : 0 ≤ S₂ := tsum_nonneg hnn
  refine ⟨4 * β⁻¹ * d * Cl * S₂ ^ 2, by positivity, ?_⟩
  intro N hN T' hT' Ω _ P _ X₀ W X hP hfilt hfin r hr
  obtain ⟨ℱ, W', hF⟩ := hfilt
  set B : ℝ := entropyScale d s N (P.map X₀)
    (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) with hB
  have hB0 : 0 ≤ B := by
    have hδ := one_le_mul_deltaN (d := d) htr.hs0 N (by omega)
    have := ENNReal.toReal_nonneg (a := relEntropy (P.map X₀)
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))
    rw [hB]; unfold entropyScale; linarith
  have hNpos : 0 < N := by omega
  have hjc := Q40b.q40b_jointCont hd1 htr T'
  have hMF := Q40b.q40b_meanField hd1 htr hT'
  have hρP : IsProbDensity (ρ r) := hMF.density r hr
  have hρc : Continuous (ρ r) :=
    hjc.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hr, Set.mem_univ _⟩)
  haveI := isProb_withDensityReal hρP
  have hXm : Measurable (X r.toNNReal) := hP.sol.adapted _
  -- pointwise bound by the entries
  have hpt : ∀ ω, ENNReal.ofReal (traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
      covForm m β⁻¹ (withDensityReal (ρ r)))) ≤
      ∑' p : NonzeroLattice d × NonzeroLattice d,
        ENNReal.ofReal |t25pEntry d m β⁻¹ (withDensityReal (ρ r)) (X r.toNNReal ω) p| := by
    intro ω
    have hsum2 : Summable fun p : NonzeroLattice d × NonzeroLattice d =>
        (wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1) := hs.mul_of_nonneg hs hnn hnn
    have hsum : Summable fun p : NonzeroLattice d × NonzeroLattice d =>
        |t25pEntry d m β⁻¹ (withDensityReal (ρ r)) (X r.toNNReal ω) p| :=
      Summable.of_nonneg_of_le (fun p => abs_nonneg _)
        (fun p => t25p_entry_abs_le hm hq0 (by omega) (X r.toNNReal ω) p) (hsum2.mul_left (8 * β⁻¹ * d))
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => abs_nonneg _) hsum]
    exact ENNReal.ofReal_le_ofReal (t25p_trace_le_entries hm hq0 hρc hρP (by omega) _)
  -- each entry
  have hent : ∀ p : NonzeroLattice d × NonzeroLattice d,
      ∫⁻ ω, ENNReal.ofReal |t25pEntry d m β⁻¹ (withDensityReal (ρ r)) (X r.toNNReal ω) p| ∂P ≤
        ENNReal.ofReal ((4 * β⁻¹ * d * Cl * Real.sqrt (B / N)) *
          ((wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1))) := by
    intro p
    have hFm : Measurable (Fkl p.1 p.2) := (continuous_Fkl p.1 p.2).measurable
    have hw1 := wt_pos (m := m) p.1
    have hw2 := wt_pos (m := m) p.2
    have hj1 := Torus.jp_pos p.1.1
    have hj2 := Torus.jp_pos p.2.1
    set K : ℝ := 2 * d * (Lattice.jp p.1.1 * Lattice.jp p.2.1) with hK
    have hK0 : 0 ≤ K := by positivity
    obtain ⟨hint, hle⟩ := hCl N hN T' hT'.le P X₀ W X hP ⟨ℱ, W', hF⟩ hfin (Fkl p.1 p.2) hFm K hK0
      (fun u => abs_Fkl_le p.1 p.2 u) r hr
    set c0 : ℝ := 2 * β⁻¹ * (wt m p.1 * wt m p.2) with hc0
    have hc00 : 0 ≤ c0 := by positivity
    have heq : ∀ ω, |t25pEntry d m β⁻¹ (withDensityReal (ρ r)) (X r.toNNReal ω) p| =
        c0 * |(1 / (N : ℝ)) * ∑ i, Fkl p.1 p.2 (X r.toNNReal ω i) -
          ∫ x, Fkl p.1 p.2 x ∂(withDensityReal (ρ r))| := by
      intro ω
      unfold t25pEntry
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * β⁻¹ * (wt m p.1 * wt m p.2))]
      simp only [one_div, hc0]
    simp_rw [heq]
    have hint' : Integrable (fun ω => c0 * |(1 / (N : ℝ)) * ∑ i, Fkl p.1 p.2 (X r.toNNReal ω i) -
          ∫ x, Fkl p.1 p.2 x ∂(withDensityReal (ρ r))|) P := hint.const_mul c0
    rw [← ofReal_integral_eq_lintegral_ofReal hint' (Filter.Eventually.of_forall fun ω => by positivity),
      integral_const_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    calc c0 * ∫ ω, |(1 / (N : ℝ)) * ∑ i, Fkl p.1 p.2 (X r.toNNReal ω i) -
          ∫ x, Fkl p.1 p.2 x ∂(withDensityReal (ρ r))| ∂P
        ≤ c0 * (Cl * K * Real.sqrt (B / N)) := mul_le_mul_of_nonneg_left hle hc00
      _ = (4 * β⁻¹ * d * Cl * Real.sqrt (B / N)) *
            ((wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1)) := by
          rw [hc0, hK]; ring
  have hmeasp : ∀ p : NonzeroLattice d × NonzeroLattice d, Measurable fun ω =>
      ENNReal.ofReal |t25pEntry d m β⁻¹ (withDensityReal (ρ r)) (X r.toNNReal ω) p| := by
    intro p
    have hFm : Measurable (Fkl p.1 p.2) := (continuous_Fkl p.1 p.2).measurable
    unfold t25pEntry
    refine ENNReal.measurable_ofReal.comp (measurable_abs.comp ?_)
    refine measurable_const.mul ((measurable_const.mul ?_).sub measurable_const)
    exact Finset.measurable_sum _ fun i _ => hFm.comp ((measurable_pi_apply i).comp hXm)
  have hK0 : 0 ≤ 4 * β⁻¹ * d * Cl * Real.sqrt (B / N) := by positivity
  calc ∫⁻ ω, ENNReal.ofReal (traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
          covForm m β⁻¹ (withDensityReal (ρ r)))) ∂P
      ≤ ∫⁻ ω, ∑' p : NonzeroLattice d × NonzeroLattice d,
          ENNReal.ofReal |t25pEntry d m β⁻¹ (withDensityReal (ρ r)) (X r.toNNReal ω) p| ∂P :=
        lintegral_mono hpt
    _ = ∑' p : NonzeroLattice d × NonzeroLattice d,
          ∫⁻ ω, ENNReal.ofReal |t25pEntry d m β⁻¹ (withDensityReal (ρ r)) (X r.toNNReal ω) p| ∂P :=
        lintegral_tsum fun p => (hmeasp p).aemeasurable
    _ ≤ ∑' p : NonzeroLattice d × NonzeroLattice d, ENNReal.ofReal
          ((4 * β⁻¹ * d * Cl * Real.sqrt (B / N)) *
            ((wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1))) :=
        ENNReal.tsum_le_tsum hent
    _ = ENNReal.ofReal ((4 * β⁻¹ * d * Cl * Real.sqrt (B / N)) * S₂ ^ 2) :=
        sum_s_le hm2 _ hK0
    _ = ENNReal.ofReal ((4 * β⁻¹ * d * Cl * S₂ ^ 2) * Real.sqrt (B / N)) := by
        congr 1; ring

end HRS.T25P
