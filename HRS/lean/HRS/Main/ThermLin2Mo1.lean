import HRS.Main.ThermLinPlan2

/-!
# THERMLIN2 Mo1: `tl2_cov_mixed` (B3), cross second moment of two stochastic convolutions

`tl2Mo_vec_gaussian_psd` is `gfb4_vec_gaussian` (GFB4Aux4) with the positive semidefiniteness of the covariance matrix
added to the conclusion (same proof).
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.GF

open HRS HRS.Uniform.Q54c HRS.Uniform.Q07c

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {G : ℝ → Ω → H} {C : ℝ → H →L[ℝ] H →L[ℝ] ℝ} {T : ℝ}

theorem tl2Mo_vec_gaussian_psd (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0) (hT : 0 < T)
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc 0 T) (ys : Fin p → ℝ → H) {B : ℝ}
    (hB : ∀ a, ∀ σ ∈ Set.Icc 0 (ts a), ‖ys a σ‖ ≤ B)
    (hw : ∀ a, ∀ x : H, ContinuousOn (fun σ => inner ℝ (ys a σ) x) (Set.Icc 0 (ts a)))
    (X : Ω → EuclideanSpace ℝ (Fin p)) (hXm : Measurable X)
    (hL2 : ∀ a, Tendsto (fun N => ∫⁻ ω, ‖X ω a - isum (fun σ => G σ ω) (ys a) T (ts a) N‖ₑ ^ 2 ∂P)
      atTop (𝓝 0)) :
    (Matrix.of fun a b => ∫ σ in Set.Icc 0 (min (ts a) (ts b)), C σ (ys a σ) (ys b σ)).PosSemidef ∧
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

end HRS.GF

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

theorem tl2Mo_integral_mul_mvGaussian {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : S.PosSemidef) :
    ∫ x, x 0 * x 1 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S) = S 0 1 := by
  have h := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin 2))) hS 0 1
  have hm : ∀ i : Fin 2, ∫ x, x i ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S) = 0 := by
    intro i
    have := integral_id_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin 2))) (S := S)
    have h2 := ContinuousLinearMap.integral_comp_id_comm
        (IsGaussian.integrable_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S))
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    simp only [EuclideanSpace.coe_proj, id] at h2
    rw [h2, show (∫ x, x ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S)) = 0 from this]
    rfl
  unfold ProbabilityTheory.covariance at h
  simpa [hm] using h

open HRS.Uniform.Q54c HRS.Uniform.Q07c HRS.Uniform.Q45 in
/-- B3 (proof): `tl2Mo_vec_gaussian_psd` with `p = 2` and two different integrand families: the cross second moment
of two stochastic convolutions of the SAME martingale against two plain evolutions (the single-evolution case is
`t25p_Zb_gaussian`). -/
theorem tl2_cov_mixed_proof {m T K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hT0 : 0 < T)
    (V₁ V₂ : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
    (hV₁c : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => V₁ p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    (hV₂c : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => V₂ p.1 p.2 y) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T})
    (hV₁b : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖V₁ t r‖ ≤ K₁)
    (hV₂b : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖V₂ t r‖ ≤ K₂)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    (G : ℝ → Ω → NegSobolev d m) (Cd : ℝ → NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => Cd r))
    (hGc : ∀ ω, Continuous fun s => G s ω) (hGz : ∀ ω, G 0 ω = 0)
    (Z₁ Z₂ : ℝ → Ω → NegSobolev d m)
    (hZ₁ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P V₁ (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Z₁ t))
    (hZ₂ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P V₂ (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Z₂ t))
    (hZ₁m : ∀ t, Measurable (Z₁ t)) (hZ₂m : ∀ t, Measurable (Z₂ t))
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Set.Icc (0 : ℝ) T) (ht₂ : t₂ ∈ Set.Icc (0 : ℝ) T)
    {φ₁ φ₂ : Torus d → ℝ} (hφ₁ : MemSobolev m φ₁) (hφ₂ : MemSobolev m φ₂) :
    ∫ ω, NegSobolev.eval (Z₁ t₁ ω) φ₁ * NegSobolev.eval (Z₂ t₂ ω) φ₂ ∂P =
      ∫ σ in Set.Icc 0 (min t₁ t₂),
        Cd σ (pullbackVec (HRS.Uniform.Comp28.plainData V₁) t₁ σ (gfb4_ell m φ₁))
          (pullbackVec (HRS.Uniform.Comp28.plainData V₂) t₂ σ (gfb4_ell m φ₂)) := by
  classical
  have hT : 0 ≤ T := hT0.le
  set ℓ₁ := gfb4_ell m φ₁ with hℓ₁
  set ℓ₂ := gfb4_ell m φ₂ with hℓ₂
  set EV₁ := HRS.Uniform.Comp28.plainData V₁ with hEV₁
  set EV₂ := HRS.Uniform.Comp28.plainData V₂ with hEV₂
  set ys : Fin 2 → ℝ → NegSobolev d m :=
    ![fun σ => pullbackVec EV₁ t₁ σ ℓ₁, fun σ => pullbackVec EV₂ t₂ σ ℓ₂] with hys
  set ts : Fin 2 → ℝ := ![t₁, t₂] with hts
  set X : Ω → EuclideanSpace ℝ (Fin 2) :=
    fun ω => WithLp.toLp 2 ![NegSobolev.eval (Z₁ t₁ ω) φ₁, NegSobolev.eval (Z₂ t₂ ω) φ₂] with hX
  have hts' : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T := by
    intro a; fin_cases a
    · exact ht₁
    · exact ht₂
  have hB : ∀ a, ∀ σ ∈ Set.Icc 0 (ts a), ‖ys a σ‖ ≤ max (K₁ * ‖ℓ₁‖) (K₂ * ‖ℓ₂‖) := by
    intro a σ hσ
    fin_cases a
    · exact (t25p_norm_pullback_le V₁ hV₁b hK₁ hσ.1 hσ.2 ht₁.2 ℓ₁).trans (le_max_left _ _)
    · exact (t25p_norm_pullback_le V₂ hV₂b hK₂ hσ.1 hσ.2 ht₂.2 ℓ₂).trans (le_max_right _ _)
  have hw : ∀ a, ∀ x : NegSobolev d m, ContinuousOn (fun σ => inner ℝ (ys a σ) x) (Set.Icc 0 (ts a)) := by
    intro a x
    fin_cases a
    · exact t25p_pullback_weak V₁ hV₁c ht₁ ℓ₁ x
    · exact t25p_pullback_weak V₂ hV₂c ht₂ ℓ₂ x
  have hXm : Measurable X := by
    refine measurable_toLp_eval fun a => ?_
    fin_cases a
    · exact (continuous_eval_const hφ₁).measurable.comp (hZ₁m _)
    · exact (continuous_eval_const hφ₂).measurable.comp (hZ₂m _)
  have hL2 : ∀ a, Tendsto (fun N => ∫⁻ ω, ‖X ω a - isum (fun σ => G σ ω) (ys a) T (ts a) N‖ₑ ^ 2 ∂P)
      atTop (𝓝 0) := by
    intro a
    fin_cases a
    · refine gfb4_L2_of_stochConv P EV₁ G hT ht₁.1 ht₁.2 (Z₁ t₁) (hZ₁ _ ht₁) ℓ₁ _ ?_
      intro ω
      simp [hX, hℓ₁, gfb4_ell_apply hφ₁]
    · refine gfb4_L2_of_stochConv P EV₂ G hT ht₂.1 ht₂.2 (Z₂ t₂) (hZ₂ _ ht₂) ℓ₂ _ ?_
      intro ω
      simp [hX, hℓ₂, gfb4_ell_apply hφ₂]
  obtain ⟨hpsd, hlaw⟩ := tl2Mo_vec_gaussian_psd hG hGc hGz hT0 ts hts' ys hB hw X hXm hL2
  have hint : ∫ ω, NegSobolev.eval (Z₁ t₁ ω) φ₁ * NegSobolev.eval (Z₂ t₂ ω) φ₂ ∂P =
      ∫ x, x 0 * x 1 ∂(P.map X) := by
    rw [integral_map hXm.aemeasurable]
    · rfl
    · exact (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin 2) => x 0 * x 1).aestronglyMeasurable
  rw [hint, hlaw, tl2Mo_integral_mul_mvGaussian hpsd]
  simp [hys, hts]

example := (@tl2_cov_mixed_proof : type_of% @tl2_cov_mixed)

end HRS.ThermLin.Plan2
