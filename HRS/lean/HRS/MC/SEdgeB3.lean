import HRS.MC.SEdgeVocab

/-!
# Packet B3: `sed_B3_onb` (existence of an orthonormal basis of `L^2_0(mu)` indexed by `ℕ`)

Route: `L^2(mu)` for the probability measure `mu = rho dx` (`rho` smooth positive) is separable and
infinite dimensional (the powers of a nonconstant continuous function are linearly independent, as
`mu` charges every nonempty open set); take a Hilbert basis of the orthogonal complement of the
constants, which is countable and infinite, and enumerate it by `ℕ`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.SEdge.B3

open HRS

variable {d : ℕ}

/-! ### The measure `mu = rho dx` -/

theorem b3_prob {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    IsProbabilityMeasure (withDensityReal ρ) := by
  have hint : Integrable ρ := by
    by_contra h
    have := hρ.density.integral_one
    rw [integral_undef h] at this
    norm_num at this
  refine ⟨?_⟩
  rw [withDensityReal, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hρ.density.nonneg),
    hρ.density.integral_one]
  simp

theorem b3_openPos {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    (withDensityReal ρ).IsOpenPosMeasure := by
  refine ⟨fun U hU hne h0 => ?_⟩
  have h1 : volume.withDensity (fun x => ENNReal.ofReal (ρ x)) U = 0 := h0
  rw [withDensity_apply_eq_zero'
    (hρ.density.measurable.ennreal_ofReal.aemeasurable)] at h1
  have hset : {x | ENNReal.ofReal (ρ x) ≠ 0} = Set.univ := by
    ext x
    simp [hρ.pos x]
  rw [hset, Set.univ_inter] at h1
  exact hU.measure_ne_zero volume hne h1

/-! ### Infinite dimensionality of `L^2(mu)` -/

/-- A continuous nonconstant real function on the torus: the real part of the first Fourier mode. -/
def b3_s (hd : 1 ≤ d) : C(Torus d, ℝ) where
  toFun x := ((AddCircle.toCircle (x ⟨0, hd⟩) : Circle) : ℂ).re
  continuous_toFun := by
    have h1 : Continuous fun x : Torus d => x ⟨0, hd⟩ := continuous_apply _
    exact Complex.continuous_re.comp
      (continuous_subtype_val.comp (AddCircle.continuous_toCircle.comp h1))

theorem b3_s_surj (hd : 1 ≤ d) (y : ℝ) (hy : y ∈ Set.Icc (-1 : ℝ) 1) : ∃ x, b3_s hd x = y := by
  refine ⟨Function.update (0 : Torus d) ⟨0, hd⟩ ((Real.arccos y / (2 * Real.pi) : ℝ) : UnitAddCircle), ?_⟩
  simp only [b3_s, ContinuousMap.coe_mk, Function.update_self]
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  have hpi : (Real.pi) ≠ 0 := Real.pi_ne_zero
  have : 2 * Real.pi / 1 * (Real.arccos y / (2 * Real.pi)) = Real.arccos y := by
    field_simp
  rw [this, Real.cos_arccos hy.1 hy.2]

theorem b3_aeval_apply (hd : 1 ≤ d) (p : Polynomial ℝ) (x : Torus d) :
    (Polynomial.aeval (b3_s hd) p) x = p.eval (b3_s hd x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

theorem b3_not_fd (hd : 1 ≤ d) (μ : Measure (Torus d)) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    [Fact ((2 : ℝ≥0∞) ≠ ∞)] : ¬ Module.Finite ℝ (Lp ℝ 2 μ) := by
  intro hfin
  let Φ : Polynomial ℝ →ₗ[ℝ] Lp ℝ 2 μ :=
    ((ContinuousMap.toLp 2 μ ℝ : C(Torus d, ℝ) →L[ℝ] Lp ℝ 2 μ) : C(Torus d, ℝ) →ₗ[ℝ] Lp ℝ 2 μ) ∘ₗ
      (Polynomial.aeval (b3_s hd)).toLinearMap
  have hinj : Function.Injective Φ := by
    intro p q hpq
    have h1 : Polynomial.aeval (b3_s hd) p = Polynomial.aeval (b3_s hd) q :=
      (ContinuousMap.toLp_injective (E := ℝ) (p := 2) μ) hpq
    by_contra hne
    have hz : ∀ y ∈ Set.Icc (-1 : ℝ) 1, (p - q).eval y = 0 := by
      intro y hy
      obtain ⟨x, hx⟩ := b3_s_surj hd y hy
      have := congrArg (fun g : C(Torus d, ℝ) => g x) h1
      simp only [b3_aeval_apply, hx] at this
      simp [this]
    have : p - q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      exact (Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono fun y hy => hz y hy
    exact hne (sub_eq_zero.mp this)
  exact Polynomial.not_finite (Module.Finite.of_injective Φ hinj)


/-! ### Hilbert bases of a separable space -/

theorem b3_hb_countable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [SecondCountableTopology E] {ι : Type*} (b : HilbertBasis ι ℝ E) : Countable ι := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense E
  have hpos : (0 : ℝ) < Real.sqrt 2 / 2 := by positivity
  have hex : ∀ i, ∃ y ∈ D, dist (b i) y < Real.sqrt 2 / 2 := fun i => hDd.exists_dist_lt (b i) hpos
  choose f hfD hf using hex
  have hinj : Function.Injective fun i => (⟨f i, hfD i⟩ : D) := by
    intro i j hij
    by_contra hne
    have hfij : f i = f j := congrArg Subtype.val hij
    have hdist : dist (b i) (b j) < Real.sqrt 2 := by
      calc dist (b i) (b j) ≤ dist (b i) (f i) + dist (f i) (b j) := dist_triangle _ _ _
        _ = dist (b i) (f i) + dist (b j) (f j) := by rw [hfij, dist_comm (f j)]
        _ < Real.sqrt 2 / 2 + Real.sqrt 2 / 2 := add_lt_add (hf i) (hf j)
        _ = Real.sqrt 2 := by ring
    have hon := b.orthonormal
    have h1 : ‖b i‖ = 1 := hon.1 i
    have h2 : ‖b j‖ = 1 := hon.1 j
    have h3 : ⟪b i, b j⟫ = 0 := hon.2 hne
    have h4 : dist (b i) (b j) ^ 2 = 2 := by
      rw [dist_eq_norm, @norm_sub_sq_real, h1, h2, h3]; norm_num
    have h5 : dist (b i) (b j) ^ 2 < 2 := by
      have h0 : 0 ≤ dist (b i) (b j) := dist_nonneg
      calc dist (b i) (b j) ^ 2 < Real.sqrt 2 ^ 2 := by gcongr
        _ = 2 := Real.sq_sqrt (by norm_num)
    linarith
  haveI : Countable D := hDc.to_subtype
  exact hinj.countable

theorem b3_hb_infinite {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (U : Submodule ℝ E) [FiniteDimensional ℝ U] (hE : ¬ Module.Finite ℝ E)
    {ι : Type*} (b : HilbertBasis ι ℝ ↥Uᗮ) : Infinite ι := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  apply hE
  have hspan : Submodule.span ℝ (Set.range b) = ⊤ := by
    have h := b.dense_span
    have hcl : IsClosed (Submodule.span ℝ (Set.range b) : Set ↥Uᗮ) := by
      haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range b)) :=
        FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
      exact Submodule.closed_of_finiteDimensional _
    rwa [hcl.submodule_topologicalClosure_eq] at h
  haveI : Module.Finite ℝ ↥Uᗮ := by
    rw [Module.finite_def, ← hspan]
    exact Submodule.fg_span (Set.finite_range _)
  haveI : FiniteDimensional ℝ ↥Uᗮ := inferInstance
  have htop : U ⊔ Uᗮ = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection
  haveI : FiniteDimensional ℝ ↥(U ⊔ Uᗮ) := inferInstance
  rw [htop] at this
  exact Module.Finite.equiv (Submodule.topEquiv (R := ℝ) (M := E))


/-! ### The basis -/

theorem b3_l2Inner_eq {μ : Measure (Torus d)} (f g : Lp ℝ 2 μ) : l2Inner μ f g = ⟪f, g⟫ := by
  unfold l2Inner
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

theorem b3_main (hd : 1 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ e : ℕ → Torus d → ℝ, IsONBL2Zero (withDensityReal ρ) e := by
  classical
  haveI := b3_prob hρ
  haveI := b3_openPos hρ
  set μ := withDensityReal ρ with hμ
  haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  haveI : SecondCountableTopology (Lp ℝ 2 μ) := inferInstance
  let c : Lp ℝ 2 μ := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ _) (1 : ℝ)
  let U : Submodule ℝ (Lp ℝ 2 μ) := ℝ ∙ c
  have hcen : ∀ f : Lp ℝ 2 μ, f ∈ Uᗮ ↔ ∫ x, f x ∂μ = 0 := by
    intro f
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have := L2.inner_indicatorConstLp_one (𝕜 := ℝ) MeasurableSet.univ (measure_ne_top μ _) f
    rw [Measure.restrict_univ] at this
    exact ⟨fun h => by rw [← this]; exact h, fun h => by rw [this]; exact h⟩
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ ↥Uᗮ
  haveI : Countable w := b3_hb_countable b
  haveI : Infinite w := b3_hb_infinite U (b3_not_fd hd μ) b
  obtain ⟨σ⟩ : Nonempty (ℕ ≃ w) := nonempty_equiv_of_countable
  let E : ℕ → Lp ℝ 2 μ := fun n => ((b (σ n) : ↥Uᗮ) : Lp ℝ 2 μ)
  refine ⟨fun n => (E n : Torus d → ℝ), ?_⟩
  refine ⟨fun i => Lp.memLp (E i), fun i => ?_, fun i j => ?_, fun f hf hf0 hfe => ?_⟩
  · exact (hcen (E i)).1 (b (σ i)).2
  · rw [b3_l2Inner_eq]
    have h := orthonormal_iff_ite.1 b.orthonormal (σ i) (σ j)
    have h2 : ⟪E i, E j⟫ = ⟪b (σ i), b (σ j)⟫ := rfl
    rw [h2, h]
    simp [σ.apply_eq_iff_eq]
  · -- completeness
    set F : Lp ℝ 2 μ := hf.toLp f with hF
    have hFae : (F : Torus d → ℝ) =ᵐ[μ] f := MemLp.coeFn_toLp hf
    have hFmem : F ∈ Uᗮ := (hcen F).2 (by rw [integral_congr_ae hFae]; exact hf0)
    let F' : ↥Uᗮ := ⟨F, hFmem⟩
    have hzero : b.repr F' = 0 := by
      ext v
      obtain ⟨i, rfl⟩ := σ.surjective v
      rw [b.repr_apply_apply]
      have h1 : l2Inner μ f (E i) = ⟪F, E i⟫ := by
        rw [← b3_l2Inner_eq]
        unfold l2Inner
        refine integral_congr_ae ?_
        filter_upwards [hFae] with x hx
        rw [hx]
      have h2 : ⟪b (σ i), F'⟫ = ⟪E i, F⟫ := rfl
      rw [h2, real_inner_comm, ← h1]
      simpa using hfe i
    have hF0 : F' = 0 := by
      have := b.repr.map_eq_zero_iff.1 hzero
      exact this
    have hF00 : F = 0 := congrArg Subtype.val hF0
    filter_upwards [hFae, Lp.coeFn_zero ℝ 2 μ] with x hx hx0
    rw [← hx, hF00]
    simpa using hx0


theorem sed_B3_onb_proof (hd : 1 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ e : ℕ → Torus d → ℝ, IsONBL2Zero (withDensityReal ρ) e :=
  b3_main hd hρ


end HRS.MC.SEdge.B3
