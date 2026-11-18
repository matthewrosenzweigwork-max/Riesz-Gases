import HRS.MS.R2IidPathAux2

/-!
# S11P: the iid initial-path row of `Round2.lean`, assembly and tie

`r2_static_observation_path_iid_proof` proves the frozen row `HRS.Whole.r2_static_observation_path_iid`
(`R2InitPathEdgeworth` at `(s, γ) = (0, 0)` along the quadratic mean-field coefficients) from the Hilbert-space Edgeworth
expansion `HRS.hilbert_edgeworth_C4` (through `s11iid_core`, `HRS/MS/R2IidAux1.lean`) on `K = ℓ²(ℕ × ℕ^d)`:
the cosine expansion of the orbit (`HRS/MS/R2IidPathAux1.lean`) writes the path `t ↦ U^{0,t}φ_α(x)` as `J(f(x))`, `J : K → C([0,T]; B_m)`
bounded linear of norm `≤ 1` (`HRS/MS/R2IidPathAux2.lean`).  No statement was adjusted.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace HRS.Whole

section Bridge

variable {d : ℕ}

open Classical in
theorem s11p_ellVec_coord {M : ℝ} (e : OscDual d M) : ellVec M (fun α => OscDual.coord e α) = e := by
  unfold ellVec
  show (if h : Memℓp (fun α => OscDual.coord e α) 2 then
    (⟨fun α => OscDual.coord e α, h⟩ : lp (fun _ : MultiIndex d => ℝ) 2) else 0) =
    (show lp (fun _ : MultiIndex d => ℝ) 2 from e)
  have hm : Memℓp (fun α => OscDual.coord e α) 2 := lp.memℓp (show lp (fun _ : MultiIndex d => ℝ) 2 from e)
  rw [dif_pos hm]
  exact lp.ext rfl

open Classical in
theorem s11p_windowPathOf_eq (M T : ℝ) (f : ℝ → OscDual d M) (p : OscPath d M T)
    (h : ∀ t : Set.Icc (0 : ℝ) T, f t = OscPath.at' p t) : windowPathOf M T 0 f = p := by
  unfold windowPathOf
  have hc : Continuous fun t : Set.Icc (0 : ℝ) T => f (0 + (t : ℝ)) := by
    have : (fun t : Set.Icc (0 : ℝ) T => f (0 + (t : ℝ))) = fun t => OscPath.at' p t :=
      funext fun t => by rw [zero_add]; exact h t
    rw [this]
    exact (show C(Set.Icc (0 : ℝ) T, OscDual d M) from p).continuous
  show (if h : Continuous fun t : Set.Icc (0 : ℝ) T => f (0 + (t : ℝ)) then
    (⟨fun t => f (0 + (t : ℝ)), h⟩ : C(Set.Icc (0 : ℝ) T, OscDual d M)) else 0) =
    (show C(Set.Icc (0 : ℝ) T, OscDual d M) from p)
  rw [dif_pos hc]
  refine ContinuousMap.ext fun t => ?_
  show f (0 + (t : ℝ)) = OscPath.at' p t
  rw [zero_add]; exact h t

theorem s11p_responseRepW_zero (g : Euc d → ℝ) (μ : Measure (Euc d)) (ψ : Euc d → ℝ) (x : Euc d) :
    responseRepW g μ 0 ψ x = ψ x - ∫ y, ψ y ∂μ := by
  simp [responseRepW, projMean, pair]

end Bridge

section Setup

variable {d : ℕ} (C : WholeCoeff d) (M : ℝ) {T : ℝ} (hT : 0 < T) {k : ℕ}
  (hmem : ∀ n α, MemCb k (r2CosOrbitTest C M T n α))
  (hsum : Summable fun q : ℕ × MultiIndex d => cbNorm k (r2CosOrbitTest C M T q.1 q.2))
  (hcont : ∀ (α : MultiIndex d) (x : Euc d),
    ContinuousOn (fun t => propagatorW C 0 t (oscTestFun M α) x) (Set.Icc (0 : ℝ) T))
  (μ : Measure (Euc d)) [IsProbabilityMeasure μ]

include hT hcont in
theorem s11p_series : S11pSeries (s11p_orbitData C M hmem hsum) T
    (fun α t x => propagatorW C 0 t (oscTestFun M α) x) :=
  fun α t ht x => s11p_orbit_hasSum C M hT hmem hsum hcont α x t ht

include hT hcont in
theorem s11p_ell_eq (g : Euc d → ℝ) (x : Euc d) (t : Set.Icc (0 : ℝ) T) :
    r2EllFun C g μ 0 M x t =
      OscPath.at' (s11p_J hT M (((s11p_orbitData C M hmem hsum).Y μ (s11p_cJ T)) x)) t := by
  have hU := s11p_series C M hT hmem hsum hcont
  unfold r2EllFun
  have : (fun α => responseRepW g μ 0 (propagatorW C 0 (t : ℝ) (oscTestFun M α)) x) =
      fun α => OscDual.coord (OscPath.at' (s11p_J hT M (((s11p_orbitData C M hmem hsum).Y μ (s11p_cJ T)) x)) t) α := by
    funext α
    rw [s11p_responseRepW_zero, ← s11p_inner_vec hT M _ t α, s11p_inner_vec_Y μ hT hU α t t.2 x]
  rw [this, s11p_ellVec_coord]

include hT hcont in
theorem s11p_init_eq (g : Euc d → ℝ) (N : ℕ) (hN : 1 ≤ N) (X : EucConfig d N) (t : Set.Icc (0 : ℝ) T) :
    r2InitFun C M (modulatedGibbs g N 0 μ) X t =
      OscPath.at' (s11p_J hT M (HRS.StaticLimitAux.Ssum ((s11p_orbitData C M hmem hsum).Y μ (s11p_cJ T)) N X)) t := by
  have hU := s11p_series C M hT hmem hsum hcont
  unfold r2InitFun
  have hN0 : 0 < N := hN
  have : (fun α => Real.sqrt N * (pair (empirical X) (propagatorW C 0 (t : ℝ) (oscTestFun M α)) -
      pair (meanEmpirical (modulatedGibbs g N 0 μ)) (propagatorW C 0 (t : ℝ) (oscTestFun M α)))) =
      fun α => OscDual.coord (OscPath.at' (s11p_J hT M
        (HRS.StaticLimitAux.Ssum ((s11p_orbitData C M hmem hsum).Y μ (s11p_cJ T)) N X)) t) α := by
    funext α
    rw [← s11p_inner_vec hT M _ t α, s11iid_gibbs_zero, s11iid_meanEmpirical_pi N hN μ,
      pair_empirical hN0]
    unfold HRS.StaticLimitAux.Ssum
    rw [inner_smul_right, inner_sum]
    simp_rw [s11p_inner_vec_Y μ hT hU α t t.2]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold pair
    have hr : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
    have hr0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
    generalize Real.sqrt (N : ℝ) = r at hr hr0 ⊢
    rw [← hr]
    field_simp
  rw [this, s11p_ellVec_coord]

end Setup

section Aux

variable {d : ℕ}

theorem s11p_abs_coord_le {M : ℝ} (u : OscDual d M) (α : MultiIndex d) : |OscDual.coord u α| ≤ ‖u‖ := by
  have := lp.norm_apply_le_norm (by simp : (2 : ℝ≥0∞) ≠ 0) (show lp (fun _ : MultiIndex d => ℝ) 2 from u) α
  rw [Real.norm_eq_abs] at this
  exact this

theorem s11p_coord_at_continuous (M T : ℝ) (t : Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    Continuous fun w : OscPath d M T => OscDual.coord (OscPath.at' w t) α := by
  rw [Metric.continuous_iff]
  intro b ε hε
  refine ⟨ε, hε, fun a hab => ?_⟩
  rw [Real.dist_eq]
  have h1 : OscDual.coord (OscPath.at' a t) α - OscDual.coord (OscPath.at' b t) α =
      OscDual.coord (OscPath.at' a t - OscPath.at' b t) α := rfl
  rw [h1]
  refine (s11p_abs_coord_le _ _).trans_lt (lt_of_le_of_lt ?_ hab)
  rw [dist_eq_norm]
  exact ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T, OscDual d M) from (a - b)) t

theorem s11p_tensor {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (ℓ : Euc d → B) (hℓ : Continuous ℓ) {Cb : ℝ} (hC : ∀ x, ‖ℓ x‖ ≤ Cb) :
    ∃ K : projTensor B 3, ∀ T : B [×3]→L[ℝ] ℝ, (K : TensorDual B 3) T = ∫ x, T ![ℓ x, ℓ x, ℓ x] ∂μ := by
  have hasm : AEStronglyMeasurable ℓ μ := hℓ.aestronglyMeasurable
  have hint : Integrable (fun x => ‖ℓ x‖ * ‖ℓ x‖ * ‖ℓ x‖) μ := by
    refine Integrable.of_bound (C := Cb * Cb * Cb) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((hℓ.norm.mul hℓ.norm).mul hℓ.norm).aestronglyMeasurable
    · have h0 : 0 ≤ ‖ℓ x‖ := norm_nonneg _
      have h1 := hC x
      have hC0 : 0 ≤ Cb := h0.trans h1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
  refine ⟨⟨HRS.MC.E213T.bochTensor3 μ ℓ ℓ ℓ, HRS.MC.E213T.bochTensor3_mem hasm hasm hasm hint⟩, fun T => ?_⟩
  exact HRS.MC.E213T.bochTensor3_apply hasm hasm hasm hint T

end Aux

section Main

variable {d : ℕ}

/-- The path Edgeworth expansion at `(s, γ) = (0, 0)` along arbitrary coefficients `C` under the orbit hypotheses. -/
theorem s11p_main (C : WholeCoeff d) (m : ℕ) {T : ℝ} (hT : 0 < T) {k : ℕ}
    (hmem : ∀ n α, MemCb k (r2CosOrbitTest C (m : ℝ) T n α))
    (hsum : Summable fun q : ℕ × MultiIndex d => cbNorm k (r2CosOrbitTest C (m : ℝ) T q.1 q.2))
    (hcont : ∀ (α : MultiIndex d) (x : Euc d),
      ContinuousOn (fun t => propagatorW C 0 t (oscTestFun (m : ℝ) α) x) (Set.Icc (0 : ℝ) T))
    (ρ0 : Euc d → ℝ) (hμ : IsProbabilityMeasure (withDensityReal ρ0)) :
    R2InitPathEdgeworth C 0 0 m T ρ0 := by
  haveI := hμ
  unfold R2InitPathEdgeworth
  set μ := withDensityReal ρ0 with hμdef
  set M : ℝ := (m : ℝ) with hM
  set D := s11p_orbitData C M hmem hsum with hD
  set c0 := s11p_cJ T with hc0
  set Y := D.Y μ c0 with hY
  set J := s11p_J hT M (d := d) with hJ
  have hU := s11p_series C M hT hmem hsum hcont
  obtain ⟨GK, hGp, hGg, hGcov⟩ := D.exists_gaussian μ c0
  haveI := hGp
  obtain ⟨σ⟩ := s11p_exists_equiv (d := d)
  have hcore := s11iid_core μ (s11p_basis σ) Y (D.Y_continuous μ c0) (D.Cb c0) (D.norm_Y_le μ c0)
    (D.Y_integral_zero μ c0) _ (D.tail_summable c0 σ) (fun n x => D.tail_bound μ c0 σ n x) GK hGg hGcov
  have hpathE : ∀ x, r2EllPath C (rieszKernel d 0) μ 0 M T x = J (Y x) := fun x =>
    s11p_windowPathOf_eq M T _ _ (fun t => s11p_ell_eq C M hT hmem hsum hcont μ _ x t)
  have hpathI : ∀ N : ℕ, 1 ≤ N → ∀ X, r2InitPath C M T (modulatedGibbs (rieszKernel d 0) N 0 μ) X =
      J (HRS.StaticLimitAux.Ssum Y N X) := fun N hN X =>
    s11p_windowPathOf_eq M T _ _ (fun t => s11p_init_eq C M hT hmem hsum hcont μ _ N hN X t)
  have hYm : Measurable Y := (D.Y_continuous μ c0).measurable
  have hbdJ : ∀ x, ‖J (Y x)‖ ≤ D.Cb c0 := fun x =>
    ((J.le_opNorm _).trans (by
      have := s11p_J_norm_le hT M (d := d)
      calc ‖J‖ * ‖Y x‖ ≤ 1 * D.Cb c0 := mul_le_mul this (D.norm_Y_le μ c0 x) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _))
  refine ⟨GK.map J, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · infer_instance
  · have := hGg.1
    refine ⟨inferInstance, fun L => ?_⟩
    rw [integral_map J.continuous.aemeasurable L.continuous.aestronglyMeasurable]
    simpa using hGg.2 (L.comp J)
  · intro t t' α α'
    have key := s11p_gauss_pair μ c0 GK hGg hGcov (s11p_vec hT t α) (s11p_vec hT t' α')
    have hF : Continuous fun w : OscPath d M T =>
        OscDual.coord (OscPath.at' w t) α * OscDual.coord (OscPath.at' w t') α' :=
      (s11p_coord_at_continuous M T t α).mul (s11p_coord_at_continuous M T t' α')
    have hFJ : (fun z => OscDual.coord (OscPath.at' (J z) t) α * OscDual.coord (OscPath.at' (J z) t') α') =
        fun z => inner ℝ (s11p_vec hT t α) z * inner ℝ (s11p_vec hT t' α') z :=
      funext fun z => by rw [s11p_inner_vec hT M z t α, s11p_inner_vec hT M z t' α']
    refine ⟨?_, ?_⟩
    · rw [integrable_map_measure hF.aestronglyMeasurable J.continuous.aemeasurable]
      exact (show Integrable (fun z => OscDual.coord (OscPath.at' (J z) t) α *
          OscDual.coord (OscPath.at' (J z) t') α') GK by rw [hFJ]; exact key.1)
    · rw [integral_map J.continuous.aemeasurable hF.aestronglyMeasurable]
      show ∫ z, OscDual.coord (OscPath.at' (J z) t) α * OscDual.coord (OscPath.at' (J z) t') α' ∂GK = _
      rw [hFJ, key.2]
      obtain ⟨Cb', hCb'⟩ := s11p_U_bound hT hU α' t' t'.2
      rw [s11p_susc μ (rieszKernel d 0) (s11p_U_continuous hT hU α' t' t'.2) hCb'
        (propagatorW C 0 (t : ℝ) (oscTestFun M α))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [s11p_inner_vec_Y μ hT hU α t t.2 x, s11p_inner_vec_Y μ hT hU α' t' t'.2 x]
  · intro x
    have : (fun t : Set.Icc (0 : ℝ) T => r2EllFun C (rieszKernel d 0) μ 0 M x t) =
        fun t => OscPath.at' (J (Y x)) t := funext (s11p_ell_eq C M hT hmem hsum hcont μ _ x)
    rw [this]
    exact (show C(Set.Icc (0 : ℝ) T, OscDual d M) from J (Y x)).continuous
  · intro N hN X
    have : (fun t : Set.Icc (0 : ℝ) T => r2InitFun C M (modulatedGibbs (rieszKernel d 0) N 0 μ) X t) =
        fun t => OscPath.at' (J (HRS.StaticLimitAux.Ssum Y N X)) t :=
      funext (s11p_init_eq C M hT hmem hsum hcont μ _ N (by omega) X)
    rw [this]
    exact (show C(Set.Icc (0 : ℝ) T, OscDual d M) from J (HRS.StaticLimitAux.Ssum Y N X)).continuous
  · exact ⟨D.Cb c0, fun x => by rw [hpathE]; exact hbdJ x⟩
  · simp only [hpathE]
    exact s11p_tensor μ (fun x => J (Y x)) (J.continuous.comp (D.Y_continuous μ c0)) hbdJ
  · intro N hN
    have : r2InitPath C M T (modulatedGibbs (rieszKernel d 0) N 0 μ) =
        fun X => J (HRS.StaticLimitAux.Ssum Y N X) := funext (hpathI N (by omega))
    rw [this]
    exact J.continuous.measurable.comp (HRS.StaticLimitAux.measurable_Ssum' hYm N)
  · intro ε hε
    obtain ⟨N₀, hN₀⟩ := hcore ε hε
    refine ⟨max N₀ 2, fun N hN hN2 Φ hΦ => ?_⟩
    have hΦ' : (Φ ∘ J) ∈ CbUnitBall (s11p_K d) 5 := cbUnitBall_comp_clm J (s11p_J_norm_le hT M) hΦ
    have h := hN₀ N (le_trans (le_max_left _ _) hN) (by omega) (Φ ∘ J) hΦ'
    have hΦc : Continuous Φ := hΦ.1.continuous
    have e1 : ∫ X, Φ (r2InitPath C M T (modulatedGibbs (rieszKernel d 0) N 0 μ) X)
        ∂(modulatedGibbs (rieszKernel d 0) N 0 μ) =
        ∫ z, (Φ ∘ J) (HRS.StaticLimitAux.Ssum Y N z) ∂(Measure.pi fun _ : Fin N => μ) := by
      have h1 : (fun X => Φ (r2InitPath C M T (modulatedGibbs (rieszKernel d 0) N 0 μ) X)) =
          fun X => (Φ ∘ J) (HRS.StaticLimitAux.Ssum Y N X) := funext fun X => by
        simp only [Function.comp_apply]; rw [hpathI N (by omega) X]
      rw [h1, s11iid_gibbs_zero]
    have e2 : ∫ F, Φ F ∂(GK.map J) = ∫ F, (Φ ∘ J) F ∂GK :=
      integral_map J.continuous.aemeasurable hΦc.aestronglyMeasurable
    set ℓ : Euc d → OscPath d M T := fun x => J (Y x) with hℓ
    have hcont3 : Continuous fun q : OscPath d M T × Euc d =>
        iteratedFDeriv ℝ 3 Φ q.1 ![ℓ q.2, ℓ q.2, ℓ q.2] := by
      have h1 : Continuous fun q : OscPath d M T × Euc d => iteratedFDeriv ℝ 3 Φ q.1 :=
        (hΦ.1.continuous_iteratedFDeriv (by norm_num)).comp continuous_fst
      have hv : Continuous fun q : OscPath d M T × Euc d => (![ℓ q.2, ℓ q.2, ℓ q.2] : Fin 3 → OscPath d M T) := by
        refine continuous_pi fun i => ?_
        fin_cases i <;> exact (J.continuous.comp (D.Y_continuous μ c0)).comp continuous_snd
      exact h1.eval hv
    have hsm : StronglyMeasurable fun F : OscPath d M T => ∫ x, iteratedFDeriv ℝ 3 Φ F ![ℓ x, ℓ x, ℓ x] ∂μ :=
      StronglyMeasurable.integral_prod_right (f := fun F x => iteratedFDeriv ℝ 3 Φ F ![ℓ x, ℓ x, ℓ x])
        hcont3.stronglyMeasurable
    have e3 : ∫ F, ∫ x, iteratedFDeriv ℝ 3 Φ F ![ℓ x, ℓ x, ℓ x] ∂μ ∂(GK.map J) =
        ∫ F, ∫ x, iteratedFDeriv ℝ 3 (Φ ∘ J) F ![Y x, Y x, Y x] ∂μ ∂GK := by
      rw [integral_map J.continuous.aemeasurable hsm.aestronglyMeasurable]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [J.iteratedFDeriv_comp_right hΦ.1 z (by norm_num : ((3 : ℕ) : WithTop ℕ∞) ≤ 5),
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
      congr 1
      funext i
      fin_cases i <;> rfl
    simp only [hpathE]
    rw [e1, e2, e3]
    exact h

end Main

section Final

/-- **The path iid row.** -/
theorem s11p_path_iid {d : ℕ} (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (T : ℝ) (hT : 0 < T)
    (k m : ℕ) (hk : 4 * d + 40 ≤ k) (hm : (k : ℝ) + 2 * d + 4 < m) :
    ∀ ρ : ℝ → Euc d → ℝ, IsProbDensity (ρ 0) →
      (∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ f : ℝ → Euc d → ℝ,
        IsClassicalAdjointW ((quadraticGradientDyn d 0 a β).coeff ρ) t (oscTestFun (m : ℝ) α) f) →
      (∀ n α, MemCb k (r2CosOrbitTest ((quadraticGradientDyn d 0 a β).coeff ρ) (m : ℝ) T n α)) →
      (Summable fun q : ℕ × MultiIndex d =>
        cbNorm k (r2CosOrbitTest ((quadraticGradientDyn d 0 a β).coeff ρ) (m : ℝ) T q.1 q.2)) →
      (∀ (α : MultiIndex d) (x : Euc d),
        ContinuousOn (fun t => propagatorW ((quadraticGradientDyn d 0 a β).coeff ρ) 0 t
          (oscTestFun (m : ℝ) α) x) (Set.Icc (0 : ℝ) T)) →
      R2InitPathEdgeworth ((quadraticGradientDyn d 0 a β).coeff ρ) 0 0 m T (ρ 0) := by
  intro ρ hρ _ hmem hsum hcont
  exact s11p_main _ m hT hmem hsum hcont (ρ 0) (s11iid_prob hρ.nonneg hρ.integral_one)

end Final

end HRS.Whole

namespace HRS.MS.R2IidPath

theorem r2_static_observation_path_iid_proof : type_of% @HRS.Whole.r2_static_observation_path_iid :=
  @HRS.Whole.s11p_path_iid

example := (@r2_static_observation_path_iid_proof : type_of% @HRS.Whole.r2_static_observation_path_iid)

end HRS.MS.R2IidPath
