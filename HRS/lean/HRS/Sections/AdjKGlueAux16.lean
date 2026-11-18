import HRS.Sections.AdjKGlueAux15

/-!
# ADJK-GLUE, part 16: finite-dimensional convergence of the fluctuation paths

For smooth tests `φ_a` and times `t_a ∈ [0,T]`, the vectors `(⟨φ_a, η_N^{t_a}⟩)_a` converge in law to
`(⟨φ_a, Y^{t_a}⟩)_a` (`dynamic_comparison_proof'` on the product extension, Lévy's continuity theorem, `hlaw`, `hY`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

universe u

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjkg_smooth_sobolev {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (m' : ℝ) :
    Summable fun j : NonzeroLattice d => Lattice.jp j.1 ^ (2 * m') * Torus.funRealCoeff φ j ^ 2 := by
  have hint := adjkg_isSmooth_integrable hφ
  obtain ⟨M, hM⟩ : ∃ M : ℕ, m' + (d : ℝ) + 1 ≤ M := ⟨⌈m' + d + 1⌉₊, Nat.le_ceil _⟩
  obtain ⟨B, hB⟩ := Torus.fcoef_pow_decay (φ := φ) (n := M) (adjkd_isCk_of_smooth M hφ)
  refine adjkd_sobolev_summable (m := (M : ℝ)) (m' := m') ?_ (B := Real.sqrt 2 * B) _ ?_
  · have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  · intro j
    have hj := Torus.jp_pos j.1
    have h1 := Torus.abs_funRealCoeff_le hint j
    have h2 := hB j
    have hp : 0 < Lattice.jp j.1 ^ M := pow_pos hj _
    have h3 : ‖Torus.fcoef φ j.1‖ ≤ B * Lattice.jp j.1 ^ (-(M : ℝ)) := by
      rw [Real.rpow_neg hj.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hp]
      exact h2
    calc |Torus.funRealCoeff φ j| ≤ Real.sqrt 2 * ‖Torus.fcoef φ j.1‖ := h1
      _ ≤ Real.sqrt 2 * (B * Lattice.jp j.1 ^ (-(M : ℝ))) :=
          mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
      _ = Real.sqrt 2 * B * Lattice.jp j.1 ^ (-(M : ℝ)) := by ring

theorem adjkg_smooth_cont_summable {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Continuous φ ∧ Summable fun k : Lattice d => ‖Torus.fcoef φ k‖ :=
  ⟨Torus.continuous_of_continuous_lift ((adjkd_isCk_of_smooth 0 hφ).continuous),
    Torus.summable_fcoef_of_contDiff fun n => adjkd_isCk_of_smooth n hφ⟩

theorem adjkg_entropyScale_nonneg (hs0 : 0 ≤ s) (N : ℕ) (hN : 1 ≤ N) (f Q : Measure (Config d N)) :
    0 ≤ entropyScale d s N f Q := by
  have hδ := one_le_mul_deltaN (d := d) hs0 N hN
  have := ENNReal.toReal_nonneg (a := relEntropy f Q)
  unfold entropyScale
  linarith

theorem adjkg_hcont (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {T : ℝ} (hT : 0 ≤ T)
    {m : ℝ} (hm : (d : ℝ) / 2 < m) (S : ParticleSeq d) (hS : S.IsSolutionOn htr.dyn T) (n : ℕ) :
    ∀ᵐ ω ∂(S.P n), Continuous fun t : Set.Icc (0 : ℝ) T =>
      Real.sqrt ((n + 2 : ℕ) : ℝ) • NegSobolev.ofMeasureDiff m
        (empirical (S.X n (Real.toNNReal t) ω)) (withDensityReal (ρ t)) := by
  filter_upwards [(hS n).sol.cont] with ω hω
  exact adjkd_fluc_cont_path hd htr m hm T hT (S.X n) _ ω hω

theorem adjkg_toPath_at {Ω : Type*} (m T : ℝ) (Y : ℝ → Ω → NegSobolev d m) (ω : Ω)
    (hc : Continuous fun t : Set.Icc (0 : ℝ) T => Y t ω) (t : Set.Icc (0 : ℝ) T) :
    (toPath m T Y ω).at' t = Y t ω := by
  have e : toPath m T Y ω = (show PathSpace d m T from
      (⟨fun t : Set.Icc (0 : ℝ) T => Y t ω, hc⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m))) := by
    unfold toPath
    exact dif_pos hc
  rw [e]
  rfl

theorem adjkg_fdd (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {T : ℝ} (hT : 0 ≤ T)
    (S : ParticleSeq d) (hS : S.IsSolutionOn htr.dyn T)
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
      (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n))
    (hfin : ∀ n, relEntropy ((S.P n).map (S.X₀ n))
      (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) ≠ ⊤)
    (hB : Tendsto (fun n : ℕ => entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) /
          Real.sqrt ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0))
    {m : ℝ} (hm : (d : ℝ) / 2 < m)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {η₀ : Ω' → NegSobolev d m}
    (hlaw : MeasureTheory.TendstoInDistribution
      (fun n ω => etaE m (S.X₀ n ω) (withDensityReal (ρ 0))) atTop η₀ S.P P')
    {Y : ℝ → Ω' → NegSobolev d m} (hY : IsLinearFluctuationSolution P' htr.dyn ρ m β⁻¹ T η₀ Y)
    (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    TendstoInDistribution
      (fun n ω => (WithLp.toLp 2 fun a => NegSobolev.eval
        ((flucPath m T (Real.sqrt ((n + 2 : ℕ) : ℝ)) (S.X n) ρ ω).at' ⟨ts a, hts a⟩) (φ a) :
          EuclideanSpace ℝ (Fin p)))
      atTop
      (fun ω' => (WithLp.toLp 2 fun a => NegSobolev.eval
        ((toPath m T Y ω').at' ⟨ts a, hts a⟩) (φ a) : EuclideanSpace ℝ (Fin p)))
      S.P P' := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hm2 : (d : ℝ) < 2 * m := by linarith
  obtain ⟨c₀, hc₀, Λ, hΛ⟩ := Q40b.q40b_rho_bounds hd1 htr
  have hprob : ∀ t : ℝ, 0 ≤ t → IsProbabilityMeasure (withDensityReal (ρ t)) := fun t ht =>
    isProb_withDensityReal (hΛ t ht).1
  set f : Fin p → Torus d → ℝ := fun a => propagator htr.dyn ρ 0 (ts a) (φ a) with hf
  -- the limit pieces
  set Lφ : ∀ n, S.Ω n → EuclideanSpace ℝ (Fin p) := fun n ω => (WithLp.toLp 2 fun a =>
    linCoord (withDensityReal (ρ (ts a))) (φ a) (S.X n (ts a).toNNReal ω) :
      EuclideanSpace ℝ (Fin p)) with hLφ
  set Aφ : ∀ n, S.Ω n → EuclideanSpace ℝ (Fin p) := fun n ω => (WithLp.toLp 2 fun a =>
    linCoord (withDensityReal (ρ 0)) (f a) (S.X₀ n ω) : EuclideanSpace ℝ (Fin p)) with hAφ
  set g : NegSobolev d m → EuclideanSpace ℝ (Fin p) := fun z => (WithLp.toLp 2 fun a =>
    NegSobolev.eval z (f a) : EuclideanSpace ℝ (Fin p)) with hg
  have hgc : Continuous g := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).comp (continuous_pi fun a => ?_)
    exact adjkg_eval_continuous (adjkg_prop_sobolev hd htr (hts a).1 (hφ a) m)
  set A' : Ω' → EuclideanSpace ℝ (Fin p) := fun ω => g (η₀ ω) with hA'
  obtain ⟨hindG, hlawG⟩ := hY.gaussian_part p ts φ hts hφ
  set G' : Ω' → EuclideanSpace ℝ (Fin p) := fun ω => (WithLp.toLp 2 fun a =>
    NegSobolev.eval (Y (ts a) ω) (φ a) - NegSobolev.eval (η₀ ω) (propagator htr.dyn ρ 0 (ts a) (φ a)) :
      EuclideanSpace ℝ (Fin p)) with hG'
  have hevc : ∀ a, Continuous fun z : NegSobolev d m => NegSobolev.eval z (φ a) := fun a =>
    adjkg_eval_continuous (adjkg_smooth_sobolev (hφ a) m)
  have hη₀m : AEMeasurable η₀ P' := hlaw.aemeasurable_limit
  have hG'm : AEMeasurable G' P' := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp_aemeasurable
      (aemeasurable_pi_iff.2 fun a => ?_)
    exact ((hevc a).measurable.comp (hY.meas _)).aemeasurable.sub
      ((adjkg_eval_continuous (adjkg_prop_sobolev hd htr (hts a).1 (hφ a) m)).measurable.comp_aemeasurable
        hη₀m)
  have hA'm : AEMeasurable A' P' := hgc.measurable.comp_aemeasurable hη₀m
  have hind : IndepFun A' G' P' := hindG.symm.comp hgc.measurable measurable_id
  have hlawG' : P'.map G' = multivariateGaussian 0 (noiseCovMatrix htr.dyn ρ β⁻¹ ts φ) := hlawG
  have hφc : ∀ a, Continuous (φ a) := fun a => (adjkg_smooth_cont_summable (hφ a)).1
  have hLm : ∀ n, AEMeasurable (Lφ n) (S.P n) := fun n => by
    refine ((PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => ?_)).aemeasurable
    exact (adjkg_linCoord_measurable (N := n + 2) _ (hφc a).measurable).comp
      ((hS n).sol.adapted _)
  -- `A_n ⇒ A'`
  have hconv0 := hlaw.continuous_comp hgc
  have hAconv : TendstoInDistribution Aφ atTop A' S.P P' := by
    refine hconv0.congr (fun n => Filter.Eventually.of_forall fun ω => ?_)
      (Filter.Eventually.of_forall fun ω' => rfl)
    ext a
    obtain ⟨hc, hs⟩ := adjkg_prop_fcoef_summable hd htr (hts a).1 (hφ a)
    haveI : IsProbabilityMeasure (withDensityReal (ρ 0)) := hprob 0 le_rfl
    exact (adjkg_linCoord_eq_eval hm2 (by omega : 0 < n + 2) (μ := withDensityReal (ρ 0)) hc hs
      (S.X₀ n ω)).symm
  -- the characteristic function comparison
  obtain ⟨C, hC0, hC⟩ := adjkg_cmp hd htr hT φ hφ
  have hcmp : ∀ t, Tendsto (fun n => ‖charFun ((S.P n).map (Lφ n)) t -
      charFun ((S.P n).map (Aφ n)) t *
        charFun (multivariateGaussian 0 (noiseCovMatrix htr.dyn ρ β⁻¹ ts φ)) t‖) atTop (𝓝 0) := by
    intro t
    set b : ℕ → ℝ := fun n => entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
      (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) /
        Real.sqrt ((n + 2 : ℕ) : ℝ) with hb
    have hb0 : ∀ n, 0 ≤ b n := fun n =>
      div_nonneg (adjkg_entropyScale_nonneg htr.hs0 (n + 2) (by omega) _ _) (Real.sqrt_nonneg _)
    have hN1 : ∀ n : ℕ, (1 : ℝ) ≤ Real.sqrt ((n + 2 : ℕ) : ℝ) := fun n => by
      rw [Real.one_le_sqrt]
      have : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith
    have hle : ∀ n, entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) / ((n + 2 : ℕ) : ℝ) ≤
          b n := by
      intro n
      have hpos : 0 < Real.sqrt ((n + 2 : ℕ) : ℝ) := lt_of_lt_of_le one_pos (hN1 n)
      have hsqsq : Real.sqrt ((n + 2 : ℕ) : ℝ) * Real.sqrt ((n + 2 : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have key : ∀ B : ℝ, B / ((n + 2 : ℕ) : ℝ) =
          B / Real.sqrt ((n + 2 : ℕ) : ℝ) / Real.sqrt ((n + 2 : ℕ) : ℝ) := fun B => by
        rw [div_div, hsqsq]
      rw [key]
      exact div_le_self (hb0 n) (hN1 n)
    have hc : Tendsto (fun n : ℕ => Real.sqrt (entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) /
          ((n + 2 : ℕ) : ℝ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => Real.sqrt (b n)) atTop (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto 0).comp hB
        simpa [Function.comp_def] using this
      exact squeeze_zero (fun n => Real.sqrt_nonneg _) (fun n => Real.sqrt_le_sqrt (hle n)) h1
    have hu : Tendsto (fun n : ℕ => 6 * max 1 (‖t‖ ^ 2) * (C * (b n + Real.sqrt (entropyScale d s (n + 2)
        ((S.P n).map (S.X₀ n))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) /
          ((n + 2 : ℕ) : ℝ))))) atTop (𝓝 0) := by
      have := tendsto_const_nhds.mul ((tendsto_const_nhds (x := C)).mul (hB.add hc))
        (f := fun _ : ℕ => 6 * max 1 (‖t‖ ^ 2))
      simpa using this
    exact squeeze_zero (fun n => norm_nonneg _) (fun n =>
      hC (n + 2) (by omega) (S.P n) (S.X₀ n) (S.W n) (S.X n) (hS n) (hSF n) (hfin n) ts hts t) hu
  have hmain := adjkg_conv_of_comparison S.P Lφ Aφ hLm (multivariateGaussian 0
    (noiseCovMatrix htr.dyn ρ β⁻¹ ts φ)) P' A' G' hA'm hG'm hind hlawG' hAconv hcmp
  refine hmain.congr (fun n => ?_) ?_
  · -- honest paths
    filter_upwards [adjkg_hcont hd htr hT hm S hS n] with ω hcω
    ext a
    simp only [WithLp.ofLp_toLp]
    obtain ⟨hc, hs⟩ := adjkg_smooth_cont_summable (hφ a)
    haveI : IsProbabilityMeasure (withDensityReal (ρ (ts a))) := hprob (ts a) (hts a).1
    rw [adjkg_flucPath_at m T _ (S.X n) ρ ω hcω ⟨ts a, hts a⟩]
    exact adjkg_linCoord_eq_eval hm2 (by omega : 0 < n + 2) (μ := withDensityReal (ρ (ts a))) hc hs
      (S.X n (ts a).toNNReal ω)
  · filter_upwards [hY.cont] with ω' hω'
    have hc : Continuous fun t : Set.Icc (0 : ℝ) T => Y t ω' := continuousOn_iff_continuous_restrict.1 hω'
    ext a
    simp only [WithLp.ofLp_toLp]
    rw [adjkg_toPath_at m T Y ω' hc ⟨ts a, hts a⟩]
    simp [hA', hg, hG', hf]

end HRS.AdjK
