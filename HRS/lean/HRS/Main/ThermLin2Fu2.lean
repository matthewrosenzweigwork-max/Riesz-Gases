import HRS.Main.ThermLin2Fu1

/-!
# THERMLIN2 Fu2: setup and basic facts for the variance computation of `tl2_dyson_fubini` (B4)

`Tl2FuSetup` bundles the hypotheses of `tl2_dyson_fubini` that do not involve the test functions.
Facts: `Cd σ` is a trace-class covariance with `∫ ‖Cd σ‖₁ < ∞` (`Tl2FuSetup.cov_facts`), the pairings of the stochastic
convolutions with `H^m` tests are in `L²` (`Tl2FuSetup.memLp_Zs`, `memLp_Zw`), and the cross second moments
(`tl2_cov_mixed_proof`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c

variable {d : ℕ}

/-- The hypotheses of `tl2_dyson_fubini` that do not involve the test functions. -/
structure Tl2FuSetup {d : ℕ} (m T' K : ℝ) (Vev Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (G : ℝ → Ω → NegSobolev d m) (Cd : ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)
    (Zs Zw : ℝ → Ω → NegSobolev d m) : Prop where
  hK : 0 ≤ K
  hT0 : 0 < T'
  hVc : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T'}
  hWc : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => Wev p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T'}
  hVb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Vev t r‖ ≤ K
  hWb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Wev t r‖ ≤ K
  hG : IsHilbertMartingaleWithCovariation P ℱ T' G (fun r _ => Cd r)
  hGc : ∀ ω, Continuous fun s => G s ω
  hGz : ∀ ω, G 0 ω = 0
  hZs : ∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zs t)
  hZw : ∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P Wev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zw t)
  hZsm : ∀ t, Measurable (Zs t)
  hZwm : ∀ t, Measurable (Zw t)
  hZwc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zw t ω) (Set.Icc 0 T')

section Setup

variable {m T' K : ℝ} {Vev Wev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
  {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
  {G : ℝ → Ω → NegSobolev d m} {Cd : ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ}
  {Zs Zw : ℝ → Ω → NegSobolev d m}

/-- Trace class, trace-norm integrability and measurability of the covariation forms. -/
theorem Tl2FuSetup.cov_facts (D : Tl2FuSetup m T' K Vev Wev P ℱ G Cd Zs Zw) :
    (∀ σ ∈ Set.Icc (0 : ℝ) T', IsTraceClassCov (Cd σ)) ∧
      IntegrableOn (fun σ => traceNormForm (Cd σ)) (Set.Icc 0 T') ∧
      ∀ u v : NegSobolev d m, Measurable fun σ => Cd σ u v := by
  obtain ⟨ω₀, h1, h3⟩ := (D.hG.sigma_traceClass.and D.hG.sigma_pathint).exists
  exact ⟨h1, h3, fun u v => (D.hG.sigma_meas u v).comp (measurable_id.prodMk (measurable_const (a := ω₀)))⟩

/-- Pairings of a stochastic convolution with an `H^m` test are in `L²`. -/
theorem tl2fu_memLp_of_conv (hK : 0 ≤ K) (hT0 : 0 < T')
    (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hVc : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T'})
    (hVb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖V t r‖ ≤ K)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T' G (fun r _ => Cd r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0)
    (Zb : ℝ → Ω → NegSobolev d m)
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) T', IsStochConv P V (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zb t))
    (hZbm : ∀ t, Measurable (Zb t)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T') {φ : Torus d → ℝ}
    (hφ : MemSobolev m φ) :
    MemLp (fun ω => NegSobolev.eval (Zb t ω) φ) 2 P := by
  have hlaw := t25p_Zb_gaussian hK hT0 V hVc hVb P G Cd hG hGc hGz Zb hZb hZbm (p := 1)
    (fun _ => t) (fun _ => ht) (fun _ => φ) (fun _ => hφ)
  set X : Ω → EuclideanSpace ℝ (Fin 1) :=
    fun ω => WithLp.toLp 2 fun a : Fin 1 => NegSobolev.eval (Zb t ω) φ with hX
  have hXm : Measurable X := by
    refine measurable_toLp_eval fun a => ?_
    exact (continuous_eval_const hφ).measurable.comp (hZbm _)
  have hmap : MemLp id 2 (P.map X) := by
    rw [hlaw]; exact IsGaussian.memLp_id _ 2 (by simp)
  have h0 : MemLp (fun x : EuclideanSpace ℝ (Fin 1) => x 0) 2 (P.map X) :=
    (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).comp_memLp' hmap
  have h1 := h0.comp_of_map hXm.aemeasurable
  simpa [hX, Function.comp_def] using h1

end Setup

end HRS.ThermLin.Plan2
