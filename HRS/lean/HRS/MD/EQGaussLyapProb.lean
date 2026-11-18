import HRS.Main.GFB4Aux1
import HRS.Main.GFB4Aux7

/-!
# EQ-GAUSS (a), probabilistic part: the stochastic convolution of a martingale with deterministic covariation

Adaptations of the `GFB4` machinery (`gfb4_modify`, `gfb4_vec_gaussian`, `gfb4_Zb_gaussian`, `gfb4_indep_pairing`) that
(i) do not need the vanishing of the covariance density outside the horizon, (ii) do not use `EvolData.MaxHyp`, and
(iii) also return the positive semidefiniteness of the covariance matrix.

For a Hilbert martingale `G` with constant covariation form `Cd`, a strongly continuous evolution `V` and functionals `ℓ_a`, the
vector `(ℓ_a(Z̄_{t_a}))_a` of the stochastic convolution `Z̄_t = ∫_0^t V(t,r) dG_r` is centered Gaussian with covariance
`∫_0^{t_a ∧ t_b} Cd(V(t_a,σ)^*ℓ_a, V(t_b,σ)^*ℓ_b) dσ` and independent of any `ℱ_0`-measurable variable.
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.MD.EQGaussLyapProb

open HRS HRS.GF HRS.Uniform HRS.Uniform.Q54c HRS.Uniform.Q07c HRS.Uniform.Q45

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem eqgp_ind_apply (S : Set ℝ) (Cd : ℝ → H →L[ℝ] H →L[ℝ] ℝ) (σ : ℝ) (x y : H) :
    (S.indicator Cd σ) x y = S.indicator (fun σ => Cd σ x y) σ := by
  by_cases h : σ ∈ S <;> simp [Set.indicator, h]

theorem eqgp_clamp_int (Cd : ℝ → H →L[ℝ] H →L[ℝ] ℝ) {T : ℝ} (hT : 0 ≤ T) (x y : H) (τ : ℝ) :
    ∫ σ in Set.Icc 0 τ, ((Set.Icc 0 T).indicator Cd σ) x y =
      ∫ σ in Set.Icc 0 (max 0 (min τ T)), Cd σ x y := by
  have h1 := gfb4_integral_Icc_clamp ((Set.Icc 0 T).indicator Cd) hT
    (fun σ hσ => Set.indicator_of_notMem hσ _) x y τ
  rw [h1]
  refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
  have hc : max 0 (min τ T) ≤ T := max_le hT (min_le_right _ _)
  have hm : σ ∈ Set.Icc (0 : ℝ) T := ⟨hσ.1, hσ.2.trans hc⟩
  rw [Set.indicator_of_mem hm]

open Classical in
/-- Replacement of a Hilbert martingale with a.s. continuous paths and constant (in `ω`) covariation density `Cd` by one with
everywhere continuous paths, for the augmented filtration; the covariation density becomes `Cd` on `[0,T]` and `0` outside. -/
theorem eqgp_modify {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) {T : ℝ} (hT : 0 ≤ T) (G : ℝ → Ω → H) (Cd : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Cd r)) :
    ∃ G' : ℝ → Ω → H, IsHilbertMartingaleWithCovariation P (gfb4_aug P ℱ) T G'
        (fun r _ => (Set.Icc 0 T).indicator Cd r) ∧
      (∀ ω, Continuous fun s => G' s ω) ∧ (∀ ω, G' 0 ω = 0) ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) T, G' τ =ᵐ[P] G τ := by
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null
    (show P {ω | ¬ (ContinuousOn (fun τ => G τ ω) (Set.Icc 0 T) ∧ G 0 ω = 0)} = 0 from by
      rw [← ae_iff]
      filter_upwards [hG.cont, hG.zero] with ω h1 h2 using ⟨h1, h2⟩)
  have hgood : ∀ ω, ω ∉ N → ContinuousOn (fun τ => G τ ω) (Set.Icc 0 T) ∧ G 0 ω = 0 := by
    intro ω hω
    by_contra h
    exact hω (hsub h)
  set c : ℝ → ℝ := fun τ => max 0 (min τ T) with hc
  have hcmem : ∀ τ, c τ ∈ Set.Icc 0 T := fun τ => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hcc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by rw [ae_iff]; simpa using hN0
  have hc0 : c 0 = 0 := by simp [hc, hT]
  have hcτ : ∀ τ ∈ Set.Icc (0 : ℝ) T, c τ = τ := fun τ hτ => by
    simp only [hc]; rw [min_eq_left hτ.2, max_eq_right hτ.1]
  refine ⟨fun τ ω => if ω ∈ N then 0 else G (c τ) ω, ?_, ?_, ?_, ?_⟩
  · -- the martingale structure
    refine
      { martingale := ?_, zero := ?_, cont := ?_, sq_int := ?_, sigma_meas := ?_,
        sigma_adapted := fun σ x y => measurable_const,
        sigma_traceClass := ?_, sigma_int := ?_,
        sigma_pathint := ?_, sigma_entry_int := ?_, covariation := ?_ }
    · intro x
      have := gfb4_mart_mod P ℱ (hG.martingale x) hT hNm hN0
        (fun ω hω => by simp [(hgood ω hω).2]) (fun _ => 0)
      have e : (fun (τ : ℝ) (ω : Ω) => inner ℝ (if ω ∈ N then (0 : H) else G (c τ) ω) x) =
          (fun τ ω => if ω ∈ N then (fun _ : ℝ => (0 : ℝ)) τ else inner ℝ (G (max 0 (min τ T)) ω) x) := by
        funext τ ω
        by_cases hω : ω ∈ N <;> simp [hω, hc]
      rw [e]
      exact this
    · refine Filter.Eventually.of_forall fun ω => ?_
      by_cases hω : ω ∈ N
      · simp [hω]
      · simp [hω, hc0, (hgood ω hω).2]
    · refine Filter.Eventually.of_forall fun ω => ?_
      refine Continuous.continuousOn ?_
      by_cases hω : ω ∈ N
      · simp only [hω, ite_true]; exact continuous_const
      · simp only [hω, ite_false]
        exact (hgood ω hω).1.comp_continuous hcc hcmem
    · intro τ hτ
      refine (hG.sq_int (c τ) (hcmem τ)).ae_eq ?_
      filter_upwards [hNae] with ω hω
      simp [hω, hcτ τ hτ]
    · intro x y
      have h := hG.sigma_meas x y
      have e : (Function.uncurry fun (σ : ℝ) (_ : Ω) => ((Set.Icc 0 T).indicator Cd σ) x y) =
          fun p : ℝ × Ω => (Set.Icc 0 T).indicator (fun σ => Cd σ x y) p.1 := by
        funext p
        simp only [Function.uncurry, eqgp_ind_apply]
      rw [e]
      have e2 : (fun p : ℝ × Ω => (Set.Icc 0 T).indicator (fun σ => Cd σ x y) p.1) =
          fun p : ℝ × Ω => if p.1 ∈ Set.Icc 0 T then Cd p.1 x y else 0 := by
        funext p; simp [Set.indicator]
      rw [e2]
      exact Measurable.ite (measurableSet_Icc.preimage measurable_fst) h measurable_const
    · filter_upwards [hG.sigma_traceClass] with ω h σ hσ
      simpa [Set.indicator_of_mem hσ] using h σ hσ
    · refine hG.sigma_int.congr (Filter.Eventually.of_forall fun ω => ?_)
      exact setIntegral_congr_fun measurableSet_Icc fun σ hσ => by simp [Set.indicator_of_mem hσ]
    · filter_upwards [hG.sigma_pathint] with ω h
      exact h.congr_fun (fun σ hσ => by simp [Set.indicator_of_mem hσ]) measurableSet_Icc
    · filter_upwards [hG.sigma_entry_int] with ω h x y
      exact (h x y).congr_fun (fun σ hσ => by simp [eqgp_ind_apply, Set.indicator_of_mem hσ])
        measurableSet_Icc
    · intro x y
      have h0 : ∀ ω, ω ∉ N → (inner ℝ (G 0 ω) x * inner ℝ (G 0 ω) y -
          ∫ σ in Set.Icc 0 (0 : ℝ), Cd σ x y) = 0 := by
        intro ω hω
        simp [(hgood ω hω).2]
      have := gfb4_mart_mod P ℱ (hG.covariation x y) hT hNm hN0 h0
        (fun τ => -∫ σ in Set.Icc 0 τ, ((Set.Icc 0 T).indicator Cd σ) x y)
      have e : (fun (τ : ℝ) (ω : Ω) => inner ℝ (if ω ∈ N then (0 : H) else G (c τ) ω) x *
          inner ℝ (if ω ∈ N then (0 : H) else G (c τ) ω) y -
            ∫ σ in Set.Icc 0 τ, ((Set.Icc 0 T).indicator Cd σ) x y) =
          (fun τ ω => if ω ∈ N then (fun τ => -∫ σ in Set.Icc 0 τ, ((Set.Icc 0 T).indicator Cd σ) x y) τ else
            (inner ℝ (G (max 0 (min τ T)) ω) x * inner ℝ (G (max 0 (min τ T)) ω) y -
              ∫ σ in Set.Icc 0 (max 0 (min τ T)), Cd σ x y)) := by
        funext τ ω
        by_cases hω : ω ∈ N
        · simp [hω]
        · simp only [hω, ite_false, hc]
          rw [eqgp_clamp_int Cd hT x y τ]
      rw [e]
      exact this
  · intro ω
    by_cases hω : ω ∈ N
    · simp only [hω, ite_true]; exact continuous_const
    · simp only [hω, ite_false]
      exact (hgood ω hω).1.comp_continuous hcc hcmem
  · intro ω
    by_cases hω : ω ∈ N
    · simp [hω]
    · simp [hω, hc0, (hgood ω hω).2]
  · intro τ hτ
    filter_upwards [hNae] with ω hω
    simp [hω, hcτ τ hτ]

section VecG

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {G : ℝ → Ω → H} {C : ℝ → H →L[ℝ] H →L[ℝ] ℝ} {T : ℝ}

theorem eqgp_vec_gaussian (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0) (hT : 0 < T)
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc 0 T) (ys : Fin p → ℝ → H) {B : ℝ}
    (hB : ∀ a, ∀ σ ∈ Set.Icc 0 (ts a), ‖ys a σ‖ ≤ B)
    (hw : ∀ a, ∀ x : H, ContinuousOn (fun σ => inner ℝ (ys a σ) x) (Set.Icc 0 (ts a)))
    (X : Ω → EuclideanSpace ℝ (Fin p)) (hXm : Measurable X)
    (hL2 : ∀ a, Tendsto (fun N => ∫⁻ ω, ‖X ω a - isum (fun σ => G σ ω) (ys a) T (ts a) N‖ₑ ^ 2 ∂P)
      atTop (𝓝 0)) :
    (Matrix.of fun a b =>
      ∫ σ in Set.Icc 0 (min (ts a) (ts b)), C σ (ys a σ) (ys b σ)).PosSemidef ∧
    P.map X = multivariateGaussian 0 (Matrix.of fun a b =>
      ∫ σ in Set.Icc 0 (min (ts a) (ts b)), C σ (ys a σ) (ys b σ)) := by
  classical
  have hT0 : 0 ≤ T := hT.le
  set yc : Fin p → ℝ → H := fun a => clampPath (ys a) (ts a) with hyc
  have hcc : ∀ a, Continuous fun σ : ℝ => max 0 (min σ (ts a)) := fun a =>
    continuous_const.max (continuous_id.min continuous_const)
  have hcmem : ∀ a σ, max 0 (min σ (ts a)) ∈ Set.Icc 0 (ts a) := fun a σ =>
    ⟨le_max_left _ _, max_le (hts a).1 (min_le_right _ _)⟩
  have hycy : ∀ a, ∀ σ ∈ Set.Icc 0 (ts a), yc a σ = ys a σ := by
    intro a σ hσ
    simp only [hyc, clampPath]
    rw [min_eq_left hσ.2, max_eq_right hσ.1]
  have hycB : ∀ a σ, ‖yc a σ‖ ≤ B := fun a σ => hB a _ (hcmem a σ)
  have hycw : ∀ a x, Continuous fun σ => inner ℝ (yc a σ) x := fun a x =>
    (hw a x).comp_continuous (hcc a) (hcmem a)
  have hycm : ∀ a, Measurable (yc a) := fun a => gfb4_measurable_of_weak fun x => (hycw a x).measurable
  have hsame : ∀ a ω N, isum (fun σ => G σ ω) (ys a) T (ts a) N =
      isum (fun σ => G σ ω) (yc a) T (ts a) N := fun a ω N =>
    (isum_clamp (fun σ => G σ ω) (ys a) hT0 (hts a).1 N).symm
  set XN : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun N ω =>
    WithLp.toLp 2 fun a => isum (fun σ => G σ ω) (ys a) T (ts a) N with hXN
  have hXNm : ∀ N, Measurable (XN N) := by
    intro N
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp ?_
    exact measurable_pi_iff.2 fun a => measurable_isum hG (ys a) (ts a) N
  obtain ⟨ω₀, hω₀tc, hω₀path⟩ : ∃ ω₀ : Ω, (∀ σ ∈ Set.Icc 0 T, IsTraceClassCov (C σ)) ∧
      IntegrableOn (fun σ => traceNormForm (C σ)) (Set.Icc 0 T) := by
    obtain ⟨ω, h1, h3⟩ := (hG.sigma_traceClass.and hG.sigma_pathint).exists
    exact ⟨ω, h1, h3⟩
  have hCm : ∀ u v : H, Measurable fun σ => C σ u v := fun u v =>
    (hG.sigma_meas u v).comp (measurable_id.prodMk (measurable_const (a := ω₀)))
  have hcov : ∀ a b, Tendsto (fun N : ℕ => ∫ ω, isum (fun σ => G σ ω) (ys a) T (ts a) N *
      isum (fun σ => G σ ω) (ys b) T (ts b) N ∂P) atTop
      (𝓝 (∫ σ in Set.Icc 0 (min (ts a) (ts b)), C σ (ys a σ) (ys b σ))) := by
    intro a b
    have hlim' := gfb4_cov_sum_tendsto (T := T) (ta := ts a) (tb := ts b) hT (hts a) (hts b)
      (hycm a) (hycm b) (hycB a) (hycB b) (hycw a) (hycw b) (C := C) (c := fun σ => traceNormForm (C σ))
      hω₀tc (fun σ => traceNormForm_nonneg _)
      (fun σ hσ u v => abs_apply_le_tn (hω₀tc σ hσ) u v) hω₀path hCm
    have e1 : (fun N : ℕ => ∫ ω, isum (fun σ => G σ ω) (ys a) T (ts a) N *
        isum (fun σ => G σ ω) (ys b) T (ts b) N ∂P) = fun N => ∑ i ∈ Finset.range (N + 1),
          ∫ σ in Set.Ioc (gridPt T N i) (gridPt T N (i + 1)) ∩ Set.Iic (min (ts a) (ts b)),
            C σ (yc a (min (gridPt T N i) (ts a))) (yc b (min (gridPt T N i) (ts b))) := by
      funext N
      simp_rw [hsame]
      exact isum_cov hG hT0 (hts a) (hts b) (yc a) (yc b) N
    rw [e1]
    have e2 : ∫ σ in Set.Icc 0 (min (ts a) (ts b)), C σ (yc a σ) (yc b σ) =
        ∫ σ in Set.Icc 0 (min (ts a) (ts b)), C σ (ys a σ) (ys b σ) :=
      setIntegral_congr_fun measurableSet_Icc fun σ hσ => by
        rw [hycy a σ ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩, hycy b σ ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩]
    rw [← e2]
    exact hlim'
  set S : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b =>
    ∫ σ in Set.Icc 0 (min (ts a) (ts b)), C σ (ys a σ) (ys b σ) with hS
  set Zx : ℕ → EuclideanSpace ℝ (Fin p) → Ω → ℝ := fun N x ω =>
    ∑ a, x a * isum (fun σ => G σ ω) (ys a) T (ts a) N with hZx
  set QN : ℕ → EuclideanSpace ℝ (Fin p) → ℝ := fun N x => ∫ ω, (Zx N x ω) ^ 2 ∂P with hQN
  have hZm : ∀ N x, Measurable (Zx N x) := fun N x =>
    Finset.measurable_sum _ fun a _ => (measurable_isum hG (ys a) (ts a) N).const_mul _
  have hinner : ∀ N x ω, inner ℝ (XN N ω) x = Zx N x ω := by
    intro N x ω
    simp only [hXN, hZx, PiLp.inner_apply, WithLp.ofLp_toLp]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [mul_comm]
  have hchar : ∀ N x, charFun (P.map (XN N)) x = Complex.exp (-(QN N x : ℂ) / 2) := by
    intro N x
    obtain ⟨v, hv⟩ := isum_comb_law hG hGc hGz hT0 ts hts ys N (fun a => x a)
    exact charFun_vec_of_gauss (hZm N x) v hv (XN N) (hXNm N) x (hinner N x)
  have hL2' : ∀ N a, MemLp (fun ω => isum (fun σ => G σ ω) (ys a) T (ts a) N) 2 P :=
    fun N a => isum_memLp hG hT0 (hts a) (ys a) N
  have hQexp : ∀ N x, QN N x = ∑ a, ∑ b, x a * x b *
      ∫ ω, isum (fun σ => G σ ω) (ys a) T (ts a) N * isum (fun σ => G σ ω) (ys b) T (ts b) N ∂P := by
    intro N x
    simp only [hQN, hZx, sq, Finset.sum_mul_sum]
    have hi : ∀ a b, Integrable (fun ω => x a * isum (fun σ => G σ ω) (ys a) T (ts a) N *
        (x b * isum (fun σ => G σ ω) (ys b) T (ts b) N)) P := by
      intro a b
      have := ((hL2' N a).const_mul (x a)).integrable_mul ((hL2' N b).const_mul (x b))
      exact this
    rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun b _ => hi a b)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ (fun b _ => hi a b)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only []
    ring
  have hQ : ∀ x : EuclideanSpace ℝ (Fin p), Tendsto (fun N => QN N x) atTop (𝓝 (x ⬝ᵥ S *ᵥ x)) := by
    intro x
    simp_rw [hQexp]
    have : x ⬝ᵥ S *ᵥ x = ∑ a, ∑ b, x a * x b * S a b := by
      simp only [dotProduct, Matrix.mulVec, hS, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [this]
    refine tendsto_finset_sum _ fun a _ => tendsto_finset_sum _ fun b _ => ?_
    exact (hcov a b).const_mul _
  obtain ⟨ns, hns, hae⟩ := gfb4_subseq_ae P hXNm hXm hL2
  have hchar_lim : ∀ x, charFun (P.map X) x = Complex.exp (-((x ⬝ᵥ S *ᵥ x : ℝ) : ℂ) / 2) := fun x =>
    gfb4_charFun_limit_ae P (fun k => hXNm (ns k)) hXm hae (fun x => x ⬝ᵥ S *ᵥ x)
      (fun k x => QN (ns k) x) (fun x => (hQ x).comp hns.tendsto_atTop) (fun k x => hchar (ns k) x) x
  have hSsymm : ∀ a b, S a b = S b a := by
    intro a b
    simp only [hS, Matrix.of_apply]
    rw [min_comm]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    exact C_symm hG ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans (hts b).2)⟩ _ _
  have hPSD : S.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x => ?_⟩
    · ext a b
      simp [Matrix.conjTranspose_apply, hSsymm a b]
    · have := ge_of_tendsto (hQ (WithLp.toLp 2 x)) (Filter.Eventually.of_forall fun N =>
        integral_nonneg fun ω => sq_nonneg _)
      simpa using this
  exact ⟨hPSD, eq_multivariateGaussian P hXm hPSD hchar_lim⟩

end VecG

section Pair

theorem eqgp_indep_pairing {T : ℝ} (hT0 : 0 < T) (EV : EvolData H H)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} (P' : Measure Ω') [IsProbabilityMeasure P']
    {ℱ'' : Filtration ℝ mΩ'} (G : ℝ → Ω' → H) (Cd : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (hG : IsHilbertMartingaleWithCovariation P' ℱ'' T G (fun r _ => Cd r))
    (Zb : ℝ → Ω' → H)
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P' EV.VE EV.j G 0 t (Zb t))
    (hZbm : ∀ t, Measurable (Zb t)) (Y₀' : Ω' → H)
    (hind : Indep (MeasurableSpace.comap Y₀' inferInstance)
      (⨆ τ ∈ Set.Icc (0 : ℝ) T, MeasurableSpace.comap (G τ) inferInstance) P')
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (ℓ : Fin p → H →L[ℝ] ℝ) :
    IndepFun (fun ω => (WithLp.toLp 2 fun a => ℓ a (Zb (ts a) ω) : EuclideanSpace ℝ (Fin p))) Y₀' P' := by
  have hT : 0 ≤ T := hT0.le
  set ys : Fin p → ℝ → H := fun a σ => pullbackVec EV (ts a) σ (ℓ a) with hys
  set X : Ω' → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a => ℓ a (Zb (ts a) ω)
    with hX
  have hXm : Measurable X := measurable_toLp_eval fun a => (ℓ a).continuous.measurable.comp (hZbm _)
  set XN : ℕ → Ω' → EuclideanSpace ℝ (Fin p) := fun N ω =>
    WithLp.toLp 2 fun a => isum (fun σ => G σ ω) (ys a) T (ts a) N with hXN
  have hXNm : ∀ N, Measurable (XN N) := fun N =>
    measurable_toLp_eval fun a => measurable_isum hG (ys a) (ts a) N
  have hL2 : ∀ a, Tendsto (fun N => ∫⁻ ω, ‖X ω a - isum (fun σ => G σ ω) (ys a) T (ts a) N‖ₑ ^ 2 ∂P')
      atTop (𝓝 0) := by
    intro a
    refine gfb4_L2_of_stochConv P' EV G hT (hts a).1 (hts a).2 (Zb (ts a)) (hZb _ (hts a))
      (ℓ a) _ ?_
    intro ω
    rfl
  obtain ⟨ns, hns, hae⟩ := gfb4_subseq_ae P' hXNm hXm hL2
  -- the σ-algebra generated by the process
  set 𝒢 : MeasurableSpace Ω' := ⨆ τ ∈ Set.Icc (0 : ℝ) T, MeasurableSpace.comap (G τ) inferInstance with h𝒢
  have h𝒢le : 𝒢 ≤ mΩ' := iSup₂_le fun τ hτ => (measurable_of_isHM hG τ).comap_le
  have hG𝒢 : ∀ τ ∈ Set.Icc (0 : ℝ) T, @Measurable Ω' _ 𝒢 _ (G τ) := fun τ hτ =>
    (comap_measurable (G τ)).mono (le_iSup₂ (f := fun τ (_ : τ ∈ Set.Icc (0 : ℝ) T) =>
      MeasurableSpace.comap (G τ) inferInstance) τ hτ) le_rfl
  set XN0 : ℕ → Ω' → EuclideanSpace ℝ (Fin p) := fun N ω =>
    WithLp.toLp 2 fun a => isum (fun σ => G σ ω) (ys a) T (ts a) N with hXN0
  have hXN0𝒢 : ∀ N, @Measurable Ω' _ 𝒢 _ (XN0 N) := fun N =>
    @measurable_toLp_eval p Ω' 𝒢 _ fun a =>
      @gfb4_isum_measurable Ω' 𝒢 _ _ _ _ _ _ _ G T hT hG𝒢 (ys a) (ts a) (hts a) N
  set L : Ω' → EuclideanSpace ℝ (Fin p) := fun ω => limUnder atTop (fun k => XN0 (ns k) ω) with hL
  have hL𝒢 : @Measurable Ω' _ 𝒢 _ L :=
    @gfb4_limUnder_meas Ω' 𝒢 p (fun k => XN0 (ns k)) (fun k => hXN0𝒢 (ns k))
  have hXL : X =ᵐ[P'] L := by
    filter_upwards [hae] with ω h1
    have h3 : Tendsto (fun k => XN0 (ns k) ω) atTop (𝓝 (X ω)) := h1
    exact (h3.limUnder_eq).symm
  have hLind : IndepFun L Y₀' P' := by
    have := indep_of_indep_of_le_left hind.symm (@Measurable.comap_le Ω' _ 𝒢 _ L hL𝒢)
    exact this
  exact hLind.congr hXL.symm (Filter.EventuallyEq.refl _ _)

end Pair

section Package

/-- The evolution data with `j = id` (only `VE` and `j` are used by the stochastic-convolution machinery). -/
def eqgp_ev (Vev : ℝ → ℝ → H →L[ℝ] H) : EvolData H H where
  j := ContinuousLinearMap.id ℝ H
  VH := Vev
  VE := Vev
  D := ⊥
  A := 0

theorem eqgp_pullback_norm_le (Vev : ℝ → ℝ → H →L[ℝ] H) (t r : ℝ) (ℓ : H →L[ℝ] ℝ) {K : ℝ}
    (hK : ‖Vev t r‖ ≤ K) : ‖pullbackVec (eqgp_ev Vev) t r ℓ‖ ≤ ‖ℓ‖ * K := by
  unfold pullbackVec
  rw [LinearIsometryEquiv.norm_map]
  have : ((eqgp_ev Vev).VE t r).comp (eqgp_ev Vev).j = Vev t r := ContinuousLinearMap.comp_id _
  rw [this]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left hK (norm_nonneg _))

theorem eqgp_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (G : ℝ → Ω → H) (Cd : H →L[ℝ] H →L[ℝ] ℝ) {S : ℝ} (hS : 0 < S)
    (hG : IsHilbertMartingaleWithCovariation P ℱ S G (fun _ _ => Cd))
    (Vev : ℝ → ℝ → H →L[ℝ] H) {K : ℝ} (hK : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S → ‖Vev t r‖ ≤ K)
    (hcont : ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 x)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ S})
    (Zb : ℝ → Ω → H)
    (hZb : ∀ t ∈ Set.Icc (0 : ℝ) S,
      IsStochConv P Vev (ContinuousLinearMap.id ℝ H) G 0 t (Zb t))
    (hZbm : ∀ t, Measurable (Zb t))
    (Z0 : Ω → H) (hZ0 : Measurable[ℱ 0] Z0)
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S) (ℓ : Fin p → H →L[ℝ] ℝ) :
    (Matrix.of fun a b => ∫ σ in Set.Icc 0 (min (ts a) (ts b)),
        Cd (pullbackVec (eqgp_ev Vev) (ts a) σ (ℓ a))
          (pullbackVec (eqgp_ev Vev) (ts b) σ (ℓ b))).PosSemidef ∧
    P.map (fun ω => (WithLp.toLp 2 fun a => ℓ a (Zb (ts a) ω) : EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun a b => ∫ σ in Set.Icc 0 (min (ts a) (ts b)),
        Cd (pullbackVec (eqgp_ev Vev) (ts a) σ (ℓ a))
          (pullbackVec (eqgp_ev Vev) (ts b) σ (ℓ b))) ∧
    IndepFun (fun ω => (WithLp.toLp 2 fun a => ℓ a (Zb (ts a) ω) : EuclideanSpace ℝ (Fin p))) Z0 P := by
  have hS0 : 0 ≤ S := hS.le
  obtain ⟨G', hG', hGc, hGz, hGG⟩ := eqgp_modify P ℱ hS0 G (fun _ => Cd) hG
  set EV := eqgp_ev Vev with hEV
  have hZb' : ∀ t ∈ Set.Icc (0 : ℝ) S, IsStochConv P EV.VE EV.j G' 0 t (Zb t) := fun t ht =>
    gfb4_isStochConv_congr P Vev (ContinuousLinearMap.id ℝ H) (G := G) (G' := G') ht.1
      (fun τ hτ => hGG τ ⟨hτ.1, hτ.2.trans ht.2⟩) (hZb t ht)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 0 le_rfl le_rfl hS0)
  set B : ℝ := K * ∑ b, ‖ℓ b‖ with hB
  have hbound : ∀ a, ∀ σ ∈ Set.Icc 0 (ts a), ‖pullbackVec EV (ts a) σ (ℓ a)‖ ≤ B := by
    intro a σ hσ
    refine (eqgp_pullback_norm_le Vev (ts a) σ (ℓ a) (hK σ (ts a) hσ.1 hσ.2 (hts a).2)).trans ?_
    rw [hB, mul_comm K]
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun b => ‖ℓ b‖) (fun b _ => norm_nonneg _) (Finset.mem_univ a)) hK0
  have hw : ∀ a (x : H), ContinuousOn (fun σ => inner ℝ (pullbackVec EV (ts a) σ (ℓ a)) x)
      (Set.Icc 0 (ts a)) := by
    intro a x
    have e : (fun σ => inner ℝ (pullbackVec EV (ts a) σ (ℓ a)) x) = fun σ => ℓ a (Vev (ts a) σ x) :=
      funext fun σ => pullback_inner EV (ts a) σ (ℓ a) x
    rw [e]
    have hc := hcont x
    have hmap : Set.MapsTo (fun r : ℝ => (ts a, r)) (Set.Icc 0 (ts a))
        {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ S} := fun r hr => ⟨hr.1, hr.2, (hts a).2⟩
    exact (ℓ a).continuous.comp_continuousOn (hc.comp (Continuous.continuousOn (by fun_prop)) hmap)
  have hXm : Measurable (fun ω => (WithLp.toLp 2 fun a => ℓ a (Zb (ts a) ω) : EuclideanSpace ℝ (Fin p))) :=
    measurable_toLp_eval fun a => (ℓ a).continuous.measurable.comp (hZbm _)
  have hL2 : ∀ a, Tendsto (fun N => ∫⁻ ω, ‖(WithLp.toLp 2 fun a => ℓ a (Zb (ts a) ω) :
      EuclideanSpace ℝ (Fin p)) a - isum (fun σ => G' σ ω) (fun σ => pullbackVec EV (ts a) σ (ℓ a)) S
        (ts a) N‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
    intro a
    exact gfb4_L2_of_stochConv P EV G' hS0 (hts a).1 (hts a).2 (Zb (ts a)) (hZb' _ (hts a)) (ℓ a) _
      (fun ω => rfl)
  obtain ⟨hPSD, hlaw⟩ := eqgp_vec_gaussian hG' hGc hGz hS ts hts (fun a σ => pullbackVec EV (ts a) σ (ℓ a))
    (B := B) hbound hw _ hXm hL2
  have hmat : (Matrix.of fun a b => ∫ σ in Set.Icc 0 (min (ts a) (ts b)),
      (Set.Icc 0 S).indicator (fun _ => Cd) σ (pullbackVec EV (ts a) σ (ℓ a))
        (pullbackVec EV (ts b) σ (ℓ b))) =
      Matrix.of fun a b => ∫ σ in Set.Icc 0 (min (ts a) (ts b)),
        Cd (pullbackVec EV (ts a) σ (ℓ a)) (pullbackVec EV (ts b) σ (ℓ b)) := by
    ext a b
    simp only [Matrix.of_apply]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    have hσS : σ ∈ Set.Icc 0 S := ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans (hts a).2)⟩
    rw [Set.indicator_of_mem hσS]
  rw [hmat] at hPSD hlaw
  refine ⟨hPSD, hlaw, ?_⟩
  -- independence
  let 𝒢 : InitialSigma (gfb4_aug P ℱ) :=
    ⟨MeasurableSpace.comap Z0 inferInstance, hZ0.comap_le.trans (gfb4_aug_le P ℱ 0)⟩
  have hind := indep_path hG' hS0 hGc hGz 𝒢
  exact eqgp_indep_pairing hS EV P (ℱ'' := gfb4_aug P ℱ) G' _ hG' Zb hZb' hZbm Z0 hind ts hts ℓ

end Package

end HRS.MD.EQGaussLyapProb

end
