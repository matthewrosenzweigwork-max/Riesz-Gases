import HRS.MC.E214E2

/-!
# E214E3: the joint Gaussian law of the two noise convolutions driven by the same martingale

For the block Gaussian martingale `Gp` on `E_m × E_m` and the convolutions `Zs`, `Zs'` of its two components
against the dual evolutions `Vev`, `Vev'` of the two trajectories, the vector
`(Zs(t_a)(φ_a))_a, (Zs'(t'_b)(ψ_b))_b ∈ ℝ^{p ⊕ p'}` has the law `multivariateGaussian 0 Σ` with `Σ` the block matrix
of `crossNoiseCov` (`gfb4_vec_gaussian` on `E_m × E_m` with the stacked pull-back vectors, reindexed from
`Fin (p+p')` to `Fin p ⊕ Fin p'`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214E

open HRS HRS.Sec7 HRS.Uniform HRS.Uniform.Q14 HRS.Uniform.Q54c HRS.GF HRS.T25P HRS.AdjK HRS.MC.E213N
  HRS.MC.E214D

variable {d : ℕ}

theorem inner_inl2 {γ : ℝ} (y : NegSobolev d γ) (x : H2 d γ) : inner ℝ (inl2 γ y) x = inner ℝ y x.fst := by
  simp [inl2, WithLp.prod_inner_apply]

theorem inner_inr2 {γ : ℝ} (y : NegSobolev d γ) (x : H2 d γ) : inner ℝ (inr2 γ y) x = inner ℝ y x.snd := by
  simp [inr2, WithLp.prod_inner_apply]

theorem norm_inl2 {γ : ℝ} (y : NegSobolev d γ) : ‖inl2 γ y‖ = ‖y‖ := by
  simp [inl2, WithLp.prod_norm_eq_of_L2]

theorem norm_inr2 {γ : ℝ} (y : NegSobolev d γ) : ‖inr2 γ y‖ = ‖y‖ := by
  simp [inr2, WithLp.prod_norm_eq_of_L2]

theorem pair_noise_gaussian (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {s' β' : ℝ} {V' ρ₀' : Torus d → ℝ}
    {ρ' : ℝ → Torus d → ℝ} (htr' : IsSmoothPositiveTrajectory d s' β' V' ρ₀' ρ') {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (hq : 0 ≤ q) {D : DynData d} (hD : htr.dyn = D)
    (hD' : htr'.dyn = D)
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {Gp : ℝ → Ω → H2 d m} (hGc : ∀ ω, Continuous fun τ => Gp τ ω) (hGz : ∀ ω, Gp 0 ω = 0)
    (hG : ∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P ℱ S Gp (fun r _ => blockDens m q ρ ρ' r))
    {Cr : ℝ} (hCr : 0 ≤ Cr) {Vev Vev' : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hdual : IsDualEvolution htr.dyn ρ m Vev) (hdual' : IsDualEvolution htr'.dyn ρ' m Vev')
    (hplain : ∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) (hplain' : ∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev' T)
    (hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → ‖Vev t r‖ ≤ Cr) (hKb' : ∀ r t : ℝ, 0 ≤ r → r ≤ t → ‖Vev' t r‖ ≤ Cr)
    {Zs Zs' : ℝ → Ω → NegSobolev d m} (hZm : ∀ t, Measurable (Zs t)) (hZm' : ∀ t, Measurable (Zs' t))
    (hZ : ∀ t : ℝ, 0 ≤ t → IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m))
      (fun τ ω => (Gp τ ω).fst) 0 t (Zs t))
    (hZ' : ∀ t : ℝ, 0 ≤ t → IsStochConv P Vev' (ContinuousLinearMap.id ℝ (NegSobolev d m))
      (fun τ ω => (Gp τ ω).snd) 0 t (Zs' t))
    {p p' : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ) (ts' : Fin p' → ℝ) (ψ : Fin p' → Torus d → ℝ)
    (hts : ∀ a, 0 ≤ ts a) (hts' : ∀ b, 0 ≤ ts' b) (hφ : ∀ a, Torus.IsSmooth (φ a))
    (hψ : ∀ b, Torus.IsSmooth (ψ b)) :
    P.map (fun ω => (WithLp.toLp 2 (Sum.elim (fun a => NegSobolev.eval (Zs (ts a) ω) (φ a))
        (fun b => NegSobolev.eval (Zs' (ts' b) ω) (ψ b))) : EuclideanSpace ℝ (Fin p ⊕ Fin p'))) =
      multivariateGaussian 0 (Matrix.of fun i j => match i, j with
        | Sum.inl a, Sum.inl b => crossNoiseCov D q ρ ρ (ts a) (ts b) (φ a) (φ b)
        | Sum.inl a, Sum.inr b => crossNoiseCov D q ρ ρ' (ts a) (ts' b) (φ a) (ψ b)
        | Sum.inr a, Sum.inl b => crossNoiseCov D q ρ' ρ (ts' a) (ts b) (ψ a) (φ b)
        | Sum.inr a, Sum.inr b => crossNoiseCov D q ρ' ρ' (ts' a) (ts' b) (ψ a) (ψ b)) := by
  classical
  subst hD
  obtain ⟨hρprob, hρc, hρm⟩ := traj_facts hd htr
  obtain ⟨hρprob', hρc', hρm'⟩ := traj_facts hd htr'
  have hφmem : ∀ a, MemSobolev m (φ a) := fun a => HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ a) m
  have hψmem : ∀ b, MemSobolev m (ψ b) := fun b => HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hψ b) m
  -- a common horizon
  set T : ℝ := 1 + ∑ a, ts a + ∑ b, ts' b with hT
  have hsa : 0 ≤ ∑ a, ts a := Finset.sum_nonneg fun a _ => hts a
  have hsb : 0 ≤ ∑ b, ts' b := Finset.sum_nonneg fun b _ => hts' b
  have hT0 : 0 < T := by rw [hT]; linarith
  have htsT : ∀ a, ts a ∈ Icc 0 T := fun a => ⟨hts a, by
    have := Finset.single_le_sum (f := ts) (fun a _ => hts a) (Finset.mem_univ a); rw [hT]; linarith⟩
  have hts'T : ∀ b, ts' b ∈ Icc 0 T := fun b => ⟨hts' b, by
    have := Finset.single_le_sum (f := ts') (fun a _ => hts' a) (Finset.mem_univ b); rw [hT]; linarith⟩
  have hKbT : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖Vev t r‖ ≤ Cr := fun r t hr hrt _ => hKb r t hr hrt
  have hKbT' : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖Vev' t r‖ ≤ Cr := fun r t hr hrt _ => hKb' r t hr hrt
  -- indexing
  set e : Fin p ⊕ Fin p' ≃ Fin (p + p') := finSumFinEquiv with he
  set tall : Fin (p + p') → ℝ := fun i => Sum.elim ts ts' (e.symm i) with htall
  set ys : Fin (p + p') → ℝ → H2 d m := fun i σ => Sum.elim
    (fun a => inl2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev) (ts a) σ (gfb4_ell m (φ a))))
    (fun b => inr2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev') (ts' b) σ (gfb4_ell m (ψ b))))
    (e.symm i) with hys
  set X : Ω → EuclideanSpace ℝ (Fin (p + p')) := fun ω => WithLp.toLp 2 fun i =>
    Sum.elim (fun a => NegSobolev.eval (Zs (ts a) ω) (φ a))
      (fun b => NegSobolev.eval (Zs' (ts' b) ω) (ψ b)) (e.symm i) with hX
  have hXm : Measurable X := by
    refine measurable_toLp_eval fun i => ?_
    rcases (e.symm i) with a | b
    · exact (continuous_eval_const (hφmem a)).measurable.comp (hZm _)
    · exact (continuous_eval_const (hψmem b)).measurable.comp (hZm' _)
  have htallT : ∀ i, tall i ∈ Icc 0 T := fun i => by
    simp only [htall]; rcases (e.symm i) with a | b
    · exact htsT a
    · exact hts'T b
  set N : Fin (p + p') → ℝ := fun i =>
    Sum.elim (fun a => ‖gfb4_ell m (φ a)‖) (fun b => ‖gfb4_ell m (ψ b)‖) (e.symm i) with hN
  have hN0 : ∀ i, 0 ≤ N i := fun i => by
    simp only [hN]; rcases (e.symm i) with a | b <;> exact norm_nonneg _
  have hNle : ∀ i, N i ≤ ∑ j, N j := fun i =>
    Finset.single_le_sum (f := N) (fun j _ => hN0 j) (Finset.mem_univ i)
  set B : ℝ := Cr * ∑ j, N j with hB
  have hBd : ∀ i, ∀ σ ∈ Icc 0 (tall i), ‖ys i σ‖ ≤ B := by
    intro i σ hσ
    obtain ⟨s, rfl⟩ := e.surjective i
    rcases s with a | b
    · simp only [htall, hys, Equiv.symm_apply_apply, Sum.elim_inl] at hσ ⊢
      rw [norm_inl2]
      refine (t25p_norm_pullback_le Vev hKbT hCr hσ.1 hσ.2 (htsT a).2 _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCr
      have := hNle (e (Sum.inl a))
      simpa [hN] using this
    · simp only [htall, hys, Equiv.symm_apply_apply, Sum.elim_inr] at hσ ⊢
      rw [norm_inr2]
      refine (t25p_norm_pullback_le Vev' hKbT' hCr hσ.1 hσ.2 (hts'T b).2 _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCr
      have := hNle (e (Sum.inr b))
      simpa [hN] using this
  have hw : ∀ i, ∀ x : H2 d m, ContinuousOn (fun σ => inner ℝ (ys i σ) x) (Icc 0 (tall i)) := by
    intro i x
    obtain ⟨s, rfl⟩ := e.surjective i
    rcases s with a | b
    · simp only [htall, hys, Equiv.symm_apply_apply, Sum.elim_inl, inner_inl2]
      exact t25p_pullback_weak Vev (hplain T hT0.le).2.2 (htsT a) _ x.fst
    · simp only [htall, hys, Equiv.symm_apply_apply, Sum.elim_inr, inner_inr2]
      exact t25p_pullback_weak Vev' (hplain' T hT0.le).2.2 (hts'T b) _ x.snd
  have hL2 : ∀ i, Tendsto (fun N => ∫⁻ ω, ‖X ω i - isum (fun σ => Gp σ ω) (ys i) T (tall i) N‖ₑ ^ 2 ∂P)
      atTop (𝓝 0) := by
    intro i
    obtain ⟨s, rfl⟩ := e.surjective i
    rcases s with a | b
    · have h1 := gfb4_L2_of_stochConv P (pairEvol (WithLp.fstL 2 ℝ (NegSobolev d m) (NegSobolev d m)) Vev)
        Gp hT0.le (hts a) (htsT a).2 (Zs (ts a))
        (isStochConv_of_map (WithLp.fstL 2 ℝ (NegSobolev d m) (NegSobolev d m)) (hZ (ts a) (hts a)))
        (gfb4_ell m (φ a)) (fun ω => X ω (e (Sum.inl a))) (fun ω => by
          simp [hX, gfb4_ell_apply (hφmem a)])
      simp only [pullbackVec_pairEvol_fstL] at h1
      simpa only [htall, hys, Equiv.symm_apply_apply, Sum.elim_inl] using h1
    · have h1 := gfb4_L2_of_stochConv P (pairEvol (WithLp.sndL 2 ℝ (NegSobolev d m) (NegSobolev d m)) Vev')
        Gp hT0.le (hts' b) (hts'T b).2 (Zs' (ts' b))
        (isStochConv_of_map (WithLp.sndL 2 ℝ (NegSobolev d m) (NegSobolev d m)) (hZ' (ts' b) (hts' b)))
        (gfb4_ell m (ψ b)) (fun ω => X ω (e (Sum.inr b))) (fun ω => by
          simp [hX, gfb4_ell_apply (hψmem b)])
      simp only [pullbackVec_pairEvol_sndL] at h1
      simpa only [htall, hys, Equiv.symm_apply_apply, Sum.elim_inr] using h1
  have hgauss := gfb4_vec_gaussian (hG T hT0.le) hGc hGz hT0 tall htallT ys hBd hw X hXm hL2
  -- the four kinds of entries
  have hll : ∀ a b, ∫ σ in Icc 0 (min (ts a) (ts b)), blockDens m q ρ ρ' σ
      (inl2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev) (ts a) σ (gfb4_ell m (φ a))))
      (inl2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev) (ts b) σ (gfb4_ell m (φ b)))) =
      crossNoiseCov htr.dyn q ρ ρ (ts a) (ts b) (φ a) (φ b) := by
    intro a b
    unfold crossNoiseCov
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Icc fun σ hσ =>
      entry_ll hd htr hρc' hm hT0 hdual hCr hKbT hq (htsT a) (htsT b) hσ (hφ a) (hφ b)
  have hrr : ∀ a b, ∫ σ in Icc 0 (min (ts' a) (ts' b)), blockDens m q ρ ρ' σ
      (inr2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev') (ts' a) σ (gfb4_ell m (ψ a))))
      (inr2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev') (ts' b) σ (gfb4_ell m (ψ b)))) =
      crossNoiseCov htr.dyn q ρ' ρ' (ts' a) (ts' b) (ψ a) (ψ b) := by
    intro a b
    unfold crossNoiseCov
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    have := entry_rr hd hρc htr' hm hT0 hdual' hCr hKbT' hq (hts'T a) (hts'T b) hσ (hψ a) (hψ b)
    rw [hD'] at this
    exact this
  have hlr : ∀ a b, ∫ σ in Icc 0 (min (ts a) (ts' b)), blockDens m q ρ ρ' σ
      (inl2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev) (ts a) σ (gfb4_ell m (φ a))))
      (inr2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev') (ts' b) σ (gfb4_ell m (ψ b)))) =
      crossNoiseCov htr.dyn q ρ ρ' (ts a) (ts' b) (φ a) (ψ b) := by
    intro a b
    unfold crossNoiseCov
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    have := e214d_cross_cov hd htr htr' hm hdual hdual' hCr hq hσ
      (hKb σ (ts a) hσ.1 (hσ.2.trans (min_le_left _ _)))
      (hKb' σ (ts' b) hσ.1 (hσ.2.trans (min_le_right _ _))) (hφ a) (hψ b)
    rw [hD'] at this
    exact this
  have hrl : ∀ a b, ∫ σ in Icc 0 (min (ts' a) (ts b)), blockDens m q ρ ρ' σ
      (inr2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev') (ts' a) σ (gfb4_ell m (ψ a))))
      (inl2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev) (ts b) σ (gfb4_ell m (φ b)))) =
      crossNoiseCov htr.dyn q ρ' ρ (ts' a) (ts b) (ψ a) (φ b) := by
    intro a b
    unfold crossNoiseCov
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    have := entry_rl hd htr htr' hm hdual hdual' hCr hq hσ
      (hKb σ (ts b) hσ.1 (hσ.2.trans (min_le_right _ _)))
      (hKb' σ (ts' a) hσ.1 (hσ.2.trans (min_le_left _ _))) (ψ := φ b) (φ := ψ a) (hψ a) (hφ b)
    rw [hD'] at this
    exact this
  have hmap : (fun ω => (WithLp.toLp 2 (Sum.elim (fun a => NegSobolev.eval (Zs (ts a) ω) (φ a))
        (fun b => NegSobolev.eval (Zs' (ts' b) ω) (ψ b))) : EuclideanSpace ℝ (Fin p ⊕ Fin p'))) =
      fun ω => (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm) (X ω) := by
    funext ω
    ext j
    simp [hX, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]
  rw [hmap]
  have hcomp : P.map (fun ω => (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm) (X ω)) =
      (P.map X).map (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm) :=
    (Measure.map_map (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm).continuous.measurable hXm).symm
  rw [hcomp, hgauss, map_reindex_multivariateGaussian e.symm]
  congr 1
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · simpa only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.symm_symm, htall, hys,
      Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] using hll a b
  · simpa only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.symm_symm, htall, hys,
      Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] using hlr a b
  · simpa only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.symm_symm, htall, hys,
      Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] using hrl a b
  · simpa only [Matrix.submatrix_apply, Matrix.of_apply, Equiv.symm_symm, htall, hys,
      Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] using hrr a b

end HRS.MC.E214E

end
