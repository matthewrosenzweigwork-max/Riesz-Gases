import HRS.Sections.AdjKGlue
import HRS.Main.GFB2Aux2

/-!
# ADJKD, part 1: measurability of `toPath` and `flucPath` (packets M0b, M0a of `AdjKSpec`)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ}

theorem adjkd_toPath_aemeasurable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (m T : ℝ)
    (Y : ℝ → Ω → NegSobolev d m) (hmeas : ∀ t, Measurable (Y t))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) :
    AEMeasurable (toPath m T Y) P := by
  classical
  have hcont' : ∀ᵐ ω ∂P, Continuous fun t : Set.Icc (0 : ℝ) T => Y t ω := by
    filter_upwards [hcont] with ω hω
    exact continuousOn_iff_continuous_restrict.1 hω
  obtain ⟨Nn, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hcont')
  let g : Ω → PathSpace d m T := fun ω => if ω ∈ Nn then 0 else toPath m T Y ω
  have hg : Measurable g := by
    refine ContinuousMap.measurable_iff_eval.2 fun s => ?_
    have hfun : (fun ω => (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from g ω) s) =
        fun ω => if ω ∈ Nn then 0 else Y s ω := by
      funext ω
      by_cases hω : ω ∈ Nn
      · simp [g, hω]
        rfl
      · have hc : Continuous fun t : Set.Icc (0 : ℝ) T => Y t ω := by
          by_contra hnc
          exact hω (hNsub hnc)
        simp only [g, hω, if_false]
        have e : toPath m T Y ω = (show PathSpace d m T from
            (⟨fun t : Set.Icc (0 : ℝ) T => Y t ω, hc⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m))) := by
          unfold toPath
          exact dif_pos hc
        rw [e]
        rfl
    rw [hfun]
    exact Measurable.ite hNm measurable_const (hmeas s)
  refine ⟨g, hg, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
  simp [g, hω]


/-! ### `flucPath` -/

variable {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjkd_weak_cont (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (T : ℝ)
    (ψ : Torus d → ℝ) (hψ : Continuous ψ) :
    ContinuousOn (fun t => ∫ x, ψ x * ρ t x) (Set.Icc 0 T) := by
  have hjc := Q40b.q40b_jointCont (by omega) htr T
  have hF : Continuous (Function.uncurry fun (t : Set.Icc (0 : ℝ) T) (x : Torus d) => ψ x * ρ t.1 x) := by
    have h1 : Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => (p.1.1, p.2) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    have h2 : Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => ρ p.1.1 p.2 :=
      hjc.comp_continuous h1 (fun p => ⟨p.1.2, Set.mem_univ _⟩)
    exact (hψ.comp continuous_snd).mul h2
  have := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Torus d))) hF
    isCompact_univ
  rw [continuousOn_iff_continuous_restrict]
  simpa [Measure.restrict_univ, Function.comp_def, Set.restrict_def] using this

theorem adjkd_fluc_cont_path (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (m : ℝ) (hm : (d : ℝ) / 2 < m) (T : ℝ) (hT : 0 ≤ T) {N : ℕ} {Ω : Type*}
    (X : ℝ≥0 → Ω → Config d N) (σ : ℝ) (ω : Ω)
    (hc : ∀ i, Continuous fun t : ℝ≥0 => X t ω i) :
    Continuous fun t : Set.Icc (0 : ℝ) T =>
      σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t)) := by
  have hm2 : (d : ℝ) < 2 * m := by linarith
  have hMFN := Q40b.q40b_meanField (by omega) htr (T := T + 1) (by linarith)
  have hweak := adjkd_weak_cont hd htr T
  have hprob : ∀ t : Set.Icc (0 : ℝ) T, IsProbabilityMeasure (withDensityReal (ρ t)) :=
    fun t => isProb_withDensityReal (hMFN.density t.1 ⟨t.2.1, t.2.2.trans (by linarith)⟩)
  have hb : Summable fun k : NonzeroLattice d => σ ^ 2 * (8 * Lattice.jp k.1 ^ (-(2 * m))) :=
    ((summable_jp_rpow (d := d) m hm2).mul_left 8).mul_left (σ ^ 2)
  have hcoord : ∀ (t : Set.Icc (0 : ℝ) T) (k : NonzeroLattice d),
      NegSobolev.coord (σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω))
          (withDensityReal (ρ t))) k =
        σ * (Lattice.jp k.1 ^ (-m) * ((N : ℝ)⁻¹ * ∑ i, Torus.realMode k (X (Real.toNNReal t) ω i) -
          ∫ x, Torus.realMode k x * ρ t x)) := by
    intro t k
    haveI := hprob t
    have h1 : NegSobolev.coord (σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω))
        (withDensityReal (ρ t))) k =
        σ * NegSobolev.coord (NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω))
        (withDensityReal (ρ t))) k := rfl
    rw [h1, coord_ofMeasureDiff hm2]
    congr 2
    congr 1
    · unfold Torus.measureRealCoeff
      exact integral_empirical _ (continuous_realMode' k)
    · have hd' := hMFN.density t.1 ⟨t.2.1, t.2.2.trans (by linarith)⟩
      unfold Torus.measureRealCoeff
      rw [integral_withDensityReal_eq _ hd'.measurable hd'.nonneg]
      exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  refine GF.gfb2_continuous_of_coords _ _ hb (fun t k => ?_) (fun k => ?_)
  · haveI := hprob t
    have := GF.gfb2_coord_sq_le (m := m) hm2 (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t))
      (by
        have := GF.gfb2_empirical_mass (X (Real.toNNReal t) ω)
        have h2 := ENNReal.toReal_mono ENNReal.one_ne_top this
        simpa using h2)
      (by simp) k
    have e : NegSobolev.coord (σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω))
          (withDensityReal (ρ t))) k =
        σ * NegSobolev.coord (NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω))
          (withDensityReal (ρ t))) k := rfl
    rw [e, mul_pow]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg σ)
  · simp only [hcoord]
    refine continuous_const.mul (continuous_const.mul (Continuous.sub ?_ ?_))
    · refine continuous_const.mul (continuous_finset_sum _ fun i _ => ?_)
      exact (continuous_realMode' k).comp ((hc i).comp (continuous_real_toNNReal.comp continuous_subtype_val))
    · exact (hweak (Torus.realMode k) (continuous_realMode' k)).comp_continuous continuous_subtype_val
        (fun t => t.2)

theorem adjkd_flucPath_aemeasurable (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (m : ℝ) (hm : (d : ℝ) / 2 < m) (T : ℝ) (hT : 0 ≤ T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsParticleSystem P htr.dyn T X₀ W X) :
    AEMeasurable (fun ω => flucPath m T (Real.sqrt N) X ρ ω) P := by
  classical
  set σ := Real.sqrt N with hσ
  have hcont : ∀ᵐ ω ∂P, Continuous fun t : Set.Icc (0 : ℝ) T =>
      σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t)) := by
    filter_upwards [hX.sol.cont] with ω hω using adjkd_fluc_cont_path hd htr m hm T hT X σ ω hω
  obtain ⟨Nn, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hcont)
  let g : Ω → PathSpace d m T := fun ω => if ω ∈ Nn then 0 else flucPath m T σ X ρ ω
  have hmeas : ∀ s : ℝ, Measurable fun ω =>
      σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal s) ω)) (withDensityReal (ρ s)) := by
    intro s
    refine (measurable_const_smul σ).comp ?_
    exact (GF.gf_measurable_ofMeasureDiff_proof (N := N) m hm _).comp (hX.sol.adapted _)
  have hg : Measurable g := by
    refine ContinuousMap.measurable_iff_eval.2 fun s => ?_
    have hfun : (fun ω => (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from g ω) s) =
        fun ω => if ω ∈ Nn then 0 else σ • NegSobolev.ofMeasureDiff m
          (empirical (X (Real.toNNReal s) ω)) (withDensityReal (ρ s)) := by
      funext ω
      by_cases hω : ω ∈ Nn
      · simp [g, hω]
        rfl
      · have hc : Continuous fun t : Set.Icc (0 : ℝ) T => σ • NegSobolev.ofMeasureDiff m
            (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t)) := by
          by_contra hnc
          exact hω (hNsub hnc)
        simp only [g, hω, if_false]
        have e : flucPath m T σ X ρ ω = (show PathSpace d m T from
            (⟨fun t : Set.Icc (0 : ℝ) T => σ • NegSobolev.ofMeasureDiff m
              (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t)), hc⟩ :
              C(Set.Icc (0 : ℝ) T, NegSobolev d m))) := by
          unfold flucPath
          exact dif_pos hc
        rw [e]
        rfl
    rw [hfun]
    exact Measurable.ite hNm measurable_const (hmeas s)
  refine ⟨g, hg, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
  simp [g, hω]

end HRS.AdjK
