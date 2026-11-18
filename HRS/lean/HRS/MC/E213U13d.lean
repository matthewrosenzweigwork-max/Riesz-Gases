import HRS.MC.E213U13c
open MeasureTheory ProbabilityTheory Filter Topology HRS
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U13

section GaussClosure

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem integral_sq_gaussianReal (v : ℝ≥0) : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have h := variance_of_integral_eq_zero (μ := gaussianReal 0 v) (X := fun x => x) aemeasurable_id
    (by simp [integral_id_gaussianReal])
  rw [← h]
  exact variance_fun_id_gaussianReal

theorem lp_sqnorm_of_gaussian {z : Lp ℝ 2 P} {v : ℝ≥0} (h : P.map (z : Ω → ℝ) = gaussianReal 0 v) :
    ‖z‖ ^ 2 = v := by
  rw [Lp2_norm_sq z, ← integral_sq_gaussianReal v, ← h,
    integral_map (Lp.aestronglyMeasurable z).aemeasurable (by fun_prop)]

theorem charFun_map_eq_integral (z : Ω → ℝ) (hz : AEMeasurable z P) (t : ℝ) :
    charFun (P.map z) t = ∫ ω, Complex.exp (t * z ω * Complex.I) ∂P := by
  rw [charFun_apply_real, integral_map hz (by fun_prop)]

theorem isClosed_gaussian : IsClosed {z : Lp ℝ 2 P | ∃ v : ℝ≥0, P.map (z : Ω → ℝ) = gaussianReal 0 v} := by
  refine isSeqClosed_iff_isClosed.1 (fun zn z hzn hlim => ?_)
  choose vn hvn using hzn
  set v : ℝ≥0 := ⟨‖z‖ ^ 2, sq_nonneg _⟩ with hv
  refine ⟨v, ?_⟩
  have hzm : AEMeasurable (z : Ω → ℝ) P := (Lp.aestronglyMeasurable z).aemeasurable
  haveI : IsProbabilityMeasure (P.map (z : Ω → ℝ)) := (Measure.isProbabilityMeasure_map_iff hzm).2 inferInstance
  haveI : IsProbabilityMeasure (gaussianReal 0 v) := inferInstance
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hL2 : Tendsto (fun n => eLpNorm ((zn n : Ω → ℝ) - (z : Ω → ℝ)) 2 P) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => dist (zn n) z) atTop (𝓝 0) := (tendsto_iff_dist_tendsto_zero.1 hlim)
    have h2 : ∀ n, eLpNorm ((zn n : Ω → ℝ) - (z : Ω → ℝ)) 2 P = ENNReal.ofReal (dist (zn n) z) := by
      intro n
      have h3 : eLpNorm ((zn n : Ω → ℝ) - (z : Ω → ℝ)) 2 P
          = eLpNorm ((zn n - z : Lp ℝ 2 P) : Ω → ℝ) 2 P := eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm
      have hfin : eLpNorm ((zn n : Ω → ℝ) - (z : Ω → ℝ)) 2 P ≠ ∞ := by
        rw [h3]; exact (Lp.memLp _).eLpNorm_lt_top.ne
      rw [Lp.dist_def, ENNReal.ofReal_toReal hfin]
    simp_rw [h2]
    simpa using ENNReal.tendsto_ofReal h1
  have hmeas : TendstoInMeasure P (fun n => (zn n : Ω → ℝ)) atTop (z : Ω → ℝ) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hL2
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hcont : Continuous fun x : ℝ => Complex.exp (t * x * Complex.I) := by fun_prop
  have hDCT : Tendsto (fun i => ∫ ω, Complex.exp (t * (zn (ns i) : Ω → ℝ) ω * Complex.I) ∂P) atTop
      (𝓝 (∫ ω, Complex.exp (t * z ω * Complex.I) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun i => ?_) (integrable_const _) (fun i => ?_) ?_
    · exact (hcont.measurable.comp_aemeasurable
        (Lp.aestronglyMeasurable (zn (ns i))).aemeasurable).aestronglyMeasurable
    · refine Eventually.of_forall fun ω => ?_
      rw [Complex.norm_exp]
      simp
    · filter_upwards [hae] with ω hω
      exact (hcont.tendsto _).comp hω
  have hlhs : ∀ i, ∫ ω, Complex.exp (t * (zn (ns i) : Ω → ℝ) ω * Complex.I) ∂P
      = Complex.exp (-(vn (ns i) : ℝ) * t ^ 2 / 2) := by
    intro i
    have hz' : AEMeasurable (zn (ns i) : Ω → ℝ) P := (Lp.aestronglyMeasurable _).aemeasurable
    rw [← charFun_map_eq_integral _ hz', hvn, charFun_gaussianReal]
    simp
    ring_nf
  have hvto : Tendsto (fun n => (vn n : ℝ)) atTop (𝓝 (v : ℝ)) := by
    have : ∀ n, (vn n : ℝ) = ‖zn n‖ ^ 2 := fun n => (lp_sqnorm_of_gaussian (hvn n)).symm
    simp_rw [this]
    exact ((continuous_norm.tendsto z).comp hlim).pow 2
  have hrhs : Tendsto (fun i => Complex.exp (-(vn (ns i) : ℝ) * t ^ 2 / 2)) atTop
      (𝓝 (Complex.exp (-(v : ℝ) * t ^ 2 / 2))) := by
    have h1 := hvto.comp hns.tendsto_atTop
    refine (Complex.continuous_exp.tendsto _).comp ?_
    have : Tendsto (fun i => (-(vn (ns i) : ℝ) * t ^ 2 / 2 : ℝ)) atTop (𝓝 (-(v : ℝ) * t ^ 2 / 2)) := by
      exact ((h1.neg.mul_const _).div_const _)
    have h2 := (Complex.continuous_ofReal.tendsto _).comp this
    simpa [Function.comp_def] using h2
  simp_rw [hlhs] at hDCT
  have := tendsto_nhds_unique hDCT hrhs
  rw [charFun_map_eq_integral _ hzm, this, charFun_gaussianReal]
  simp
  ring_nf


theorem hasGaussianLaw_of_combos {I : Type*} [Fintype I] (Y : I → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (h : ∀ c : I → ℝ, ∃ v : ℝ≥0, P.map (fun ω => ∑ i, c i * Y i ω) = gaussianReal 0 v) :
    HasGaussianLaw (fun ω i => Y i ω) P := by
  classical
  have hmeas : Measurable (fun ω i => Y i ω) := measurable_pi_iff.2 hY
  haveI : IsGaussian (P.map (fun ω i => Y i ω)) := by
    refine isGaussian_of_map_eq_gaussianReal fun L => ?_
    obtain ⟨v, hv⟩ := h fun i => L (fun j => if i = j then 1 else 0)
    refine ⟨0, v, ?_⟩
    rw [Measure.map_map L.continuous.measurable hmeas]
    convert hv using 2
    funext ω
    rw [Function.comp_apply]
    have := LinearMap.pi_apply_eq_sum_univ (L : (I → ℝ) →ₗ[ℝ] ℝ) (fun i => Y i ω)
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this]
    simp [mul_comm]
  exact IsGaussian.hasGaussianLaw hmeas.aemeasurable

theorem isGaussianProcess_of_combos {T : Type*} (X : T → Ω → ℝ) (hX : ∀ t, Measurable (X t))
    (h : ∀ (I : Finset T) (c : I → ℝ), ∃ v : ℝ≥0, P.map (fun ω => ∑ i : I, c i * X i ω) = gaussianReal 0 v) :
    IsGaussianProcess X P := by
  refine ⟨fun I => ?_⟩
  exact hasGaussianLaw_of_combos (fun (i : I) ω => X i ω) (fun i => hX i) (h I)


theorem gaussian_of_mem_closure {ι : Type*} (x : ι → Lp ℝ 2 P)
    (hG : ∀ z ∈ Submodule.span ℝ (Set.range x), ∃ v : ℝ≥0, P.map (z : Ω → ℝ) = gaussianReal 0 v) :
    ∀ z ∈ (Submodule.span ℝ (Set.range x)).topologicalClosure,
      ∃ v : ℝ≥0, P.map (z : Ω → ℝ) = gaussianReal 0 v := by
  intro z hz
  have h : ((Submodule.span ℝ (Set.range x) : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) ⊆
      {z : Lp ℝ 2 P | ∃ v : ℝ≥0, P.map (z : Ω → ℝ) = gaussianReal 0 v} := fun z hz => hG z hz
  have := closure_minimal h isClosed_gaussian
  rw [← Submodule.topologicalClosure_coe] at this
  exact this hz

end GaussClosure

section Construction

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem integral_mul_eq_inner (f g : Lp ℝ 2 P) {a b : Ω → ℝ} (ha : (f : Ω → ℝ) =ᵐ[P] a)
    (hb : (g : Ω → ℝ) =ᵐ[P] b) : ∫ ω, a ω * b ω ∂P = inner ℝ f g := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ha, hb] with ω h1 h2
  rw [← h1, ← h2, RCLike.inner_apply, conj_trivial, mul_comm]

open Submodule InnerProductSpace in
theorem exists_stdGaussianSeq (x : ℕ → Lp ℝ 2 P)
    (hG : ∀ z ∈ Submodule.span ℝ (Set.range x), ∃ v : ℝ≥0, P.map (z : Ω → ℝ) = gaussianReal 0 v)
    (hinf : ¬ FiniteDimensional ℝ (Submodule.span ℝ (Set.range x))) :
    ∃ (ξ : ℕ → Ω → ℝ) (hm : ∀ i, Measurable (ξ i)) (hξ : IsStdGaussianSeq P ξ),
      ∀ z ∈ (Submodule.span ℝ (Set.range x)).topologicalClosure, InQ1 hξ hm (z : Ω → ℝ) := by
  classical
  set W := (Submodule.span ℝ (Set.range x)).topologicalClosure with hWdef
  have hW := gaussian_of_mem_closure x hG
  set e : ℕ → Lp ℝ 2 P := gramSchmidtNormed ℝ x with he
  set N : Set ℕ := {n | e n ≠ 0} with hN
  have hspan : Submodule.span ℝ (Set.range x) = Submodule.span ℝ (Set.range fun i : N => e i) := by
    rw [← span_gramSchmidt ℝ x, ← span_gramSchmidtNormed_range]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨n, rfl⟩
      by_cases h : gramSchmidtNormed ℝ x n = 0
      · rw [h]; exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨n, h⟩, rfl⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨i.1, rfl⟩
  have hNinf : N.Infinite := by
    by_contra h
    rw [Set.not_infinite] at h
    haveI : Finite N := h.to_subtype
    apply hinf
    rw [hspan]
    exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  haveI : Infinite N := hNinf.to_subtype
  let σ : ℕ ≃o N := Nat.Subtype.orderIsoOfNat N
  set u : ℕ → Lp ℝ 2 P := fun i => e (σ i).1 with hu
  have hon : Orthonormal ℝ u := by
    have := (gramSchmidtNormed_orthonormal' (𝕜 := ℝ) x).comp (fun i => σ i) σ.injective
    exact this
  have hspanu : Submodule.span ℝ (Set.range u) = Submodule.span ℝ (Set.range x) := by
    rw [hspan]
    congr 1
    ext y
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨σ i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨σ.symm i, by simp [hu]⟩
  -- measurable representatives
  set ξ : ℕ → Ω → ℝ := fun i => (Lp.aestronglyMeasurable (u i)).mk (u i) with hξdef
  have hm : ∀ i, Measurable (ξ i) := fun i => (Lp.aestronglyMeasurable (u i)).stronglyMeasurable_mk.measurable
  have hae : ∀ i, (u i : Ω → ℝ) =ᵐ[P] ξ i := fun i => (Lp.aestronglyMeasurable (u i)).ae_eq_mk
  have huW : ∀ i, u i ∈ W := fun i => by
    rw [hWdef, ← hspanu]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)
  -- finite combinations of ξ are centred Gaussians
  have hcomb : ∀ (J : Finset ℕ) (c : J → ℝ), ∃ v : ℝ≥0,
      P.map (fun ω => ∑ i : J, c i * ξ i ω) = gaussianReal 0 v := by
    intro J c
    have hz : (∑ i : J, c i • u i) ∈ W := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (huW i)
    obtain ⟨v, hv⟩ := hW _ hz
    refine ⟨v, ?_⟩
    rw [← hv]
    refine Measure.map_congr ?_
    have h1 : ∀ i : J, (fun ω => c i * ξ i ω) =ᵐ[P] (c i • (u i : Ω → ℝ)) := fun i => by
      filter_upwards [hae i] with ω hω
      simp [hω]
    have h2 := Lp.coeFn_fun_finsetSum (Finset.univ : Finset J) (fun i => c i • u i)
    have h3 : ∀ i : J, (⇑(c i • u i) : Ω → ℝ) =ᵐ[P] fun ω => c i * ξ i ω := fun i => by
      filter_upwards [Lp.coeFn_smul (c i) (u i), hae i] with ω h1 h2
      simp [h1, h2]
    have h4 : ∀ᵐ ω ∂P, ∀ i : J, (⇑(c i • u i) : Ω → ℝ) ω = c i * ξ i ω := ae_all_iff.2 h3
    filter_upwards [h2, h4] with ω a b
    rw [a]
    exact Finset.sum_congr rfl fun i _ => (b i).symm
  have hgp : IsGaussianProcess ξ P := isGaussianProcess_of_combos ξ hm hcomb
  have hmean : ∀ i, ∫ ω, ξ i ω ∂P = 0 := by
    intro i
    obtain ⟨v, hv⟩ := hW (u i) (huW i)
    have h1 : P.map (ξ i) = gaussianReal 0 v := by
      rw [← hv]; exact Measure.map_congr (hae i).symm
    rw [← integral_map (hm i).aemeasurable aestronglyMeasurable_id (f := fun x : ℝ => x), h1,
      integral_id_gaussianReal]
  have hlaw : ∀ i, law P (ξ i) = gaussianReal 0 1 := by
    intro i
    obtain ⟨v, hv⟩ := hW (u i) (huW i)
    have h1 : P.map (ξ i) = gaussianReal 0 v := by
      rw [← hv]; exact Measure.map_congr (hae i).symm
    have h2 := lp_sqnorm_of_gaussian hv
    rw [hon.1 i] at h2
    have : v = 1 := by
      have : (v : ℝ) = 1 := by simpa using h2.symm
      exact_mod_cast this
    show P.map (ξ i) = _
    rw [h1, this]
  have hmem2 : ∀ i, MemLp (ξ i) 2 P := fun i => (Lp.memLp (u i)).ae_eq (hae i)
  have hcov : ∀ i j, i ≠ j → cov[ξ i, ξ j; P] = 0 := by
    intro i j hij
    rw [covariance_eq_sub (hmem2 i) (hmem2 j), hmean i, zero_mul, sub_zero]
    have h0 : inner ℝ (u i) (u j) = 0 := hon.2 hij
    rw [L2.inner_def] at h0
    rw [Pi.mul_def, integral_mul_eq_inner (u i) (u j) (hae i) (hae j)]
    exact h0
  have hind : iIndepFun ξ P := by
    have hX' : IsGaussianProcess (fun (p : (_ : ℕ) × Unit) ω => ξ p.1 ω) P :=
      hgp.comp_right (fun p : (_ : ℕ) × Unit => p.1)
    have := IsGaussianProcess.iIndepFun_of_covariance_eq_zero (S := fun _ : ℕ => Unit)
      (X := fun t _ => ξ t) hX' (fun t _ => (hm t).aemeasurable)
      (fun t₁ t₂ h _ _ => hcov t₁ t₂ h)
    exact this.comp (fun _ (f : Unit → ℝ) => f ()) (fun _ => measurable_pi_apply ())
  have hξ : IsStdGaussianSeq P ξ := ⟨hind, hlaw⟩
  refine ⟨ξ, hm, hξ, fun z hz => ?_⟩
  refine ⟨Lp.memLp z, ?_⟩
  rw [Lp.toLp_coeFn]
  have hg : ∀ i, g1 hξ hm i = u i := fun i => by
    refine Lp.ext ?_
    exact (coe_g1 hξ hm i).trans (hae i).symm
  have hsub : Submodule.span ℝ (Set.range u) ≤ ⨆ n, K1 hξ hm n := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    refine (le_iSup (K1 hξ hm) (i + 1)) ?_
    refine Submodule.subset_span ⟨⟨i, Nat.lt_succ_self i⟩, ?_⟩
    exact hg i
  have : W ≤ Qc (K1 hξ hm) := by
    rw [hWdef, ← hspanu]
    exact Submodule.topologicalClosure_mono hsub
  exact this hz

end Construction
end HRS.MC.E213U13
