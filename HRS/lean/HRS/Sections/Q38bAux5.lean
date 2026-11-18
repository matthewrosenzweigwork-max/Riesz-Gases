import HRS.Sections.Q38bAux4

/-!
# Packet Q38b, part 5: tools for the non-tightness argument

* compact sets of `C([0,T];ℝ)` are uniformly equicontinuous;
* the law of `x₀ - x₁` under a centred Gaussian vector in `ℝ²`;
* a Gaussian small-ball (large-deviation) lower bound for variances `≥ 1`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS

/-- Compact subsets of `C([0,T];ℝ)` are uniformly equicontinuous. -/
theorem q38b_equicont {T : ℝ} {K : Set C(Set.Icc (0 : ℝ) T, ℝ)} (hK : IsCompact K) {η : ℝ}
    (hη : 0 < η) :
    ∃ δ > 0, ∀ f ∈ K, ∀ s t : Set.Icc (0 : ℝ) T, dist s t < δ → dist (f s) (f t) < η := by
  have hc : Continuous (fun p : C(Set.Icc (0 : ℝ) T, ℝ) × Set.Icc (0 : ℝ) T => p.1 p.2) :=
    continuous_eval
  have hu := (hK.prod (isCompact_univ : IsCompact (Set.univ : Set (Set.Icc (0 : ℝ) T))))
    |>.uniformContinuousOn_of_continuous hc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, h⟩ := hu η hη
  refine ⟨δ, hδ, fun f hf s t hst => h (f, s) ⟨hf, trivial⟩ (f, t) ⟨hf, trivial⟩ ?_⟩
  rw [Prod.dist_eq]
  simpa using hst

/-- The law of `x₀ - x₁` under a centred Gaussian vector in `ℝ²`. -/
theorem q38b_gauss_diff_map (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.PosSemidef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S).map (fun x => x 0 - x 1) =
      gaussianReal 0 (S 0 0 + S 1 1 - 2 * S 0 1).toNNReal := by
  set γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S with hγ
  have hmem : ∀ i : Fin 2, MemLp (fun x : EuclideanSpace ℝ (Fin 2) => x i) 2 γ := by
    intro i
    have := (IsGaussian.memLp_two_id (μ := γ))
    exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp_memLp' this
  have hmean : ∀ i : Fin 2, ∫ x, x i ∂γ = 0 := by
    intro i
    have h := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).integral_comp_id_comm
      (μ := γ) IsGaussian.integrable_id
    simpa [hγ, integral_id_multivariateGaussian] using h
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin 2)) :=
    (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) -
      (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
  have hL : (⇑L : EuclideanSpace ℝ (Fin 2) → ℝ) = fun x => x 0 - x 1 := by
    ext x; simp [L]
  have h1 := IsGaussian.map_eq_gaussianReal (μ := γ) L
  rw [hL] at h1
  rw [h1]
  congr 1
  · rw [integral_sub ((hmem 0).integrable one_le_two) ((hmem 1).integrable one_le_two), hmean 0,
      hmean 1]
    simp
  · congr 1
    rw [variance_fun_sub (hmem 0) (hmem 1), variance_eval_multivariateGaussian hS,
      variance_eval_multivariateGaussian hS, covariance_eval_multivariateGaussian hS]
    ring

/-- Small-ball lower bound: a centred Gaussian with variance `≥ 1` charges `{|x| ≥ 1}` at least as
much as the standard Gaussian. -/
theorem q38b_gaussian_lower {v : ℝ≥0} (hv : 1 ≤ v) :
    gaussianReal 0 1 {x : ℝ | 1 ≤ |x|} ≤ gaussianReal 0 v {x : ℝ | 1 ≤ |x|} := by
  have hv0 : (0 : ℝ) ≤ (v : ℝ) := v.coe_nonneg
  have hv1 : (1 : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  set c : ℝ := Real.sqrt v with hc
  have hc1 : 1 ≤ c := by
    rw [hc]; exact Real.one_le_sqrt.2 hv1
  have hmap := gaussianReal_map_const_mul (μ := 0) (v := 1) c
  have hvar : (NNReal.mk (c ^ 2) (sq_nonneg _)) * 1 = v := by
    apply NNReal.eq
    simp [hc, Real.sq_sqrt hv0]
  rw [hvar, mul_zero] at hmap
  rw [← hmap, Measure.map_apply (measurable_const_mul c)
    (measurableSet_le measurable_const (by fun_prop))]
  refine measure_mono fun x hx => ?_
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hx ⊢
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ c)]
  nlinarith [abs_nonneg x]

/-- The standard Gaussian charges `{|x| ≥ 1}`. -/
theorem q38b_gaussian_pos : gaussianReal 0 1 {x : ℝ | 1 ≤ |x|} ≠ 0 := by
  intro h
  have hac := gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) one_ne_zero
  have h0 : (volume : Measure ℝ) {x : ℝ | 1 ≤ |x|} = 0 := hac h
  have : (volume : Measure ℝ) (Set.Ici 1) = 0 := by
    refine measure_mono_null (fun x hx => ?_) h0
    simp only [Set.mem_Ici] at hx
    simp only [Set.mem_setOf_eq]
    rw [abs_of_nonneg (by linarith)]
    exact hx
  simp at this

theorem q38b_enorm_pos {d : ℕ} (k : NonzeroLattice d) : 0 < Lattice.enorm k.1 := by
  unfold Lattice.enorm
  rw [norm_pos_iff]
  intro h
  apply k.2
  funext i
  have := congrArg (fun x : Euc d => x i) h
  simpa [Lattice.toEuc] using this

end HRS
