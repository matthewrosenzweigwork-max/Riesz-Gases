import HRS.Prob.Gaussian

/-!
# Auxiliary lemmas for the Edgeworth expansion (Lemma 7.1)

Lindeberg replacement in a separable real Hilbert space.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Nat

namespace HRS

namespace EdgeAux

set_option linter.unusedSectionVars false

section Taylor

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Taylor's formula with a Lagrange-type bound for the remainder. -/
lemma taylor_bound {f : H → ℝ} {n : ℕ} (hf : ContDiff ℝ (n + 1) f) {L : ℝ}
    (hL : ∀ x, ‖iteratedFDeriv ℝ (n + 1) f x‖ ≤ L) (r h : H) :
    |f (r + h) - ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹) * iteratedFDeriv ℝ k f r (fun _ => h)|
      ≤ L * ‖h‖ ^ (n + 1) / ((n + 1)! : ℝ) := by
  have h1 := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := r) (y := h) (n := n)
    (fun t _ => (hf.contDiffAt))
  rw [h1]
  simp only [smul_eq_mul, add_sub_cancel_left]
  set c : ℝ := L * ‖h‖ ^ (n + 1) with hc
  have hbd : ‖∫ t in (0:ℝ)..1, (1 - t) ^ n * iteratedFDeriv ℝ (n + 1) f (r + t • h) (fun _ => h)‖
      ≤ ∫ t in (0:ℝ)..1, (1 - t) ^ n * c := by
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ ?_
    · refine Filter.Eventually.of_forall fun t ht => ?_
      rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 ht.2)]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (sub_nonneg.2 ht.2) n)
      · calc ‖iteratedFDeriv ℝ (n + 1) f (r + t • h) (fun _ => h)‖
            ≤ ‖iteratedFDeriv ℝ (n + 1) f (r + t • h)‖ * ∏ _i : Fin (n + 1), ‖h‖ :=
              ContinuousMultilinearMap.le_opNorm _ _
          _ ≤ L * ‖h‖ ^ (n + 1) := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
              gcongr
              exact hL _
    · exact (by fun_prop : Continuous fun t : ℝ => (1 - t) ^ n * c).intervalIntegrable _ _
  have hI : ∫ t in (0:ℝ)..1, (1 - t) ^ n * c = c / (n + 1) := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ n) 1]
    simp [integral_pow]
    ring
  rw [Real.norm_eq_abs] at *
  have hn : (0:ℝ) ≤ ((n ! : ℝ))⁻¹ := by positivity
  calc |((n ! : ℝ))⁻¹ * ∫ t in (0:ℝ)..1, (1 - t) ^ n * iteratedFDeriv ℝ (n + 1) f (r + t • h) (fun _ => h)|
      = ((n ! : ℝ))⁻¹ * |∫ t in (0:ℝ)..1, (1 - t) ^ n * iteratedFDeriv ℝ (n + 1) f (r + t • h) (fun _ => h)| := by
        rw [abs_mul, abs_of_nonneg hn]
    _ ≤ ((n ! : ℝ))⁻¹ * (c / (n + 1)) := by
        gcongr
        exact hbd.trans_eq hI
    _ = L * ‖h‖ ^ (n + 1) / ((n + 1)! : ℝ) := by
        rw [hc, Nat.factorial_succ]; push_cast
        field_simp

end Taylor

section Moments

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H]

/-- The diagonal moment functional `m ↦ ∫ m(a,…,a) dμ(a)`. -/
def momF (μ : Measure H) (j : ℕ) (m : H [×j]→L[ℝ] ℝ) : ℝ := ∫ a, m (fun _ => a) ∂μ

lemma norm_apply_diag_le {j : ℕ} (m : H [×j]→L[ℝ] ℝ) (a : H) :
    ‖m (fun _ => a)‖ ≤ ‖m‖ * ‖a‖ ^ j := by
  calc ‖m (fun _ => a)‖ ≤ ‖m‖ * ∏ _i : Fin j, ‖a‖ := m.le_opNorm _
    _ = ‖m‖ * ‖a‖ ^ j := by simp

lemma continuous_apply_diag {j : ℕ} (m : H [×j]→L[ℝ] ℝ) : Continuous fun a : H => m (fun _ => a) :=
  m.cont.comp (continuous_pi fun _ => continuous_id)

lemma integrable_apply_diag {μ : Measure H} {j : ℕ} (hμ : Integrable (fun a : H => ‖a‖ ^ j) μ)
    (m : H [×j]→L[ℝ] ℝ) : Integrable (fun a => m (fun _ => a)) μ := by
  refine Integrable.mono' (hμ.const_mul ‖m‖) (continuous_apply_diag m).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun a => norm_apply_diag_le m a

lemma abs_momF_le {μ : Measure H} {j : ℕ} (hμ : Integrable (fun a : H => ‖a‖ ^ j) μ)
    (m : H [×j]→L[ℝ] ℝ) : |momF μ j m| ≤ ‖m‖ * ∫ a, ‖a‖ ^ j ∂μ := by
  rw [momF, ← Real.norm_eq_abs, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans ?_
  exact integral_mono (integrable_apply_diag hμ m).norm (hμ.const_mul _)
    (fun a => norm_apply_diag_le m a)

lemma momF_add {μ : Measure H} {j : ℕ} (hμ : Integrable (fun a : H => ‖a‖ ^ j) μ)
    (m n : H [×j]→L[ℝ] ℝ) : momF μ j (m + n) = momF μ j m + momF μ j n := by
  simp only [momF, add_apply]
  exact integral_add (integrable_apply_diag hμ m) (integrable_apply_diag hμ n)

lemma momF_smul {μ : Measure H} {j : ℕ} (c : ℝ) (m : H [×j]→L[ℝ] ℝ) :
    momF μ j (c • m) = c * momF μ j m := by
  simp only [momF, smul_apply, smul_eq_mul]
  exact integral_const_mul _ _

/-- The diagonal moment functional as a continuous linear map. -/
def momCLM (μ : Measure H) {j : ℕ} (hμ : Integrable (fun a : H => ‖a‖ ^ j) μ) :
    (H [×j]→L[ℝ] ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := momF μ j
      map_add' := momF_add hμ
      map_smul' := fun c m => by simpa using momF_smul c m }
    (∫ a, ‖a‖ ^ j ∂μ) (fun m => by
      have := abs_momF_le hμ m
      rw [Real.norm_eq_abs]; show |momF μ j m| ≤ _; linarith)

lemma momCLM_apply (μ : Measure H) {j : ℕ} (hμ : Integrable (fun a : H => ‖a‖ ^ j) μ)
    (m : H [×j]→L[ℝ] ℝ) : momCLM μ hμ m = momF μ j m := rfl

lemma norm_momCLM_le (μ : Measure H) {j : ℕ} (hμ : Integrable (fun a : H => ‖a‖ ^ j) μ) :
    ‖momCLM μ hμ‖ ≤ ∫ a, ‖a‖ ^ j ∂μ :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg fun a => by positivity) _

end Moments

section IterNorm

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma norm_iteratedFDeriv_iteratedFDeriv (f : H → ℝ) (x : H) :
    ∀ (i k : ℕ), ‖iteratedFDeriv ℝ i (iteratedFDeriv ℝ k f) x‖ = ‖iteratedFDeriv ℝ (i + k) f x‖ := by
  intro i
  induction i generalizing x with
  | zero => intro k; rw [zero_add]; simp
  | succ i ih =>
    intro k
    have h1 : ‖iteratedFDeriv ℝ (i + 1) (iteratedFDeriv ℝ k f) x‖ =
        ‖iteratedFDeriv ℝ i (fderiv ℝ (iteratedFDeriv ℝ k f)) x‖ :=
      (norm_iteratedFDeriv_fderiv).symm
    have h2 : fderiv ℝ (iteratedFDeriv ℝ k f) =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => H) ℝ) ∘
          iteratedFDeriv ℝ (k + 1) f := by
      funext y
      rw [iteratedFDeriv_succ_eq_comp_left]
      simp
    rw [h1, h2, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, ih x (k + 1)]
    rw [show i + (k + 1) = i + 1 + k by omega]

lemma contDiff_clm_iteratedFDeriv {k n : ℕ} (Λ : (H [×k]→L[ℝ] ℝ) →L[ℝ] ℝ) {f : H → ℝ}
    (hf : ContDiff ℝ (n + k) f) : ContDiff ℝ n (fun z => Λ (iteratedFDeriv ℝ k f z)) := by
  have h1 : ContDiff ℝ n (iteratedFDeriv ℝ k f) := hf.iteratedFDeriv_right' (m := n) (i := k)
    |> fun h => by simpa using h
  exact Λ.contDiff.comp h1

lemma norm_iteratedFDeriv_clm_iteratedFDeriv {k n : ℕ} (Λ : (H [×k]→L[ℝ] ℝ) →L[ℝ] ℝ) {f : H → ℝ}
    (hf : ContDiff ℝ (n + k) f) {i : ℕ} (hi : i ≤ n) (x : H) :
    ‖iteratedFDeriv ℝ i (fun z => Λ (iteratedFDeriv ℝ k f z)) x‖ ≤
      ‖Λ‖ * ‖iteratedFDeriv ℝ (i + k) f x‖ := by
  have h1 : ContDiff ℝ n (iteratedFDeriv ℝ k f) := hf.iteratedFDeriv_right' (m := n) (i := k)
    |> fun h => by simpa using h
  have := Λ.norm_iteratedFDeriv_comp_left (f := iteratedFDeriv ℝ k f) (x := x) (N := n)
    h1.contDiffAt (by exact_mod_cast hi) 
  rw [norm_iteratedFDeriv_iteratedFDeriv] at this
  exact this

end IterNorm


section SecondMoment

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma integrable_inner_mul_inner {μ : Measure H} (hμ : Integrable (fun a : H => ‖a‖ ^ 2) μ)
    (x y : H) : Integrable (fun a => inner ℝ x a * inner ℝ y a) μ := by
  refine Integrable.mono' (hμ.const_mul (‖x‖ * ‖y‖)) ?_ ?_
  · exact (by fun_prop : Continuous fun a : H => inner ℝ x a * inner ℝ y a).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun a => ?_
    rw [norm_mul]
    calc ‖inner ℝ x a‖ * ‖inner ℝ y a‖ ≤ (‖x‖ * ‖a‖) * (‖y‖ * ‖a‖) := by
          gcongr <;> exact norm_inner_le_norm _ _
      _ = ‖x‖ * ‖y‖ * ‖a‖ ^ 2 := by ring

/-- For a finite-dimensional subspace, the second moment form of the projected variable. -/
lemma integral_projected_bilinear {μ : Measure H} (hμ : Integrable (fun a : H => ‖a‖ ^ 2) μ)
    (K : Submodule ℝ H) [FiniteDimensional ℝ K] (B : H →L[ℝ] H →L[ℝ] ℝ) :
    ∫ a, B (K.starProjection a) (K.starProjection a) ∂μ =
      ∑ i, ∑ j, B (stdOrthonormalBasis ℝ K i : H) (stdOrthonormalBasis ℝ K j : H) *
        ∫ a, inner ℝ (stdOrthonormalBasis ℝ K i : H) a * inner ℝ (stdOrthonormalBasis ℝ K j : H) a ∂μ := by
  set b := stdOrthonormalBasis ℝ K
  have hP : ∀ a, K.starProjection a = ∑ i, inner ℝ (b i : H) a • (b i : H) := fun a => by
    rw [Submodule.starProjection_apply, b.orthogonalProjectionOnto_apply_eq_sum]
    push_cast
    rfl
  have hexp : ∀ a, B (K.starProjection a) (K.starProjection a) =
      ∑ i, ∑ j, B (b i : H) (b j : H) * (inner ℝ (b i : H) a * inner ℝ (b j : H) a) := by
    intro a
    rw [hP a]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
    · exact fun j _ => (integrable_inner_mul_inner hμ _ _).const_mul _
  · exact fun i _ => integrable_finsetSum _ fun j _ => (integrable_inner_mul_inner hμ _ _).const_mul _

/-- Two measures with the same second-moment form (and finite second moments) integrate every
continuous bilinear form on the diagonal equally. -/
lemma integral_diag_bilinear_eq {μ ν : Measure H}
    (hμ : Integrable (fun a : H => ‖a‖ ^ 2) μ) (hν : Integrable (fun a : H => ‖a‖ ^ 2) ν)
    (hcov : ∀ x y, ∫ a, inner ℝ x a * inner ℝ y a ∂μ = ∫ a, inner ℝ x a * inner ℝ y a ∂ν)
    (B : H →L[ℝ] H →L[ℝ] ℝ) : ∫ a, B a a ∂μ = ∫ a, B a a ∂ν := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq H
  let K : ℕ → Submodule ℝ H := fun n => Submodule.span ℝ (d '' Set.Iic n)
  have hfin : ∀ n, FiniteDimensional ℝ (K n) := fun n =>
    FiniteDimensional.span_of_finite ℝ ((Set.finite_Iic n).image d)
  have hconv : ∀ a, Tendsto (fun n => (K n).starProjection a) atTop (𝓝 a) := by
    intro a
    rw [tendsto_iff_dist_tendsto_zero]
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨m, hm⟩ := hd.exists_dist_lt a hε
    refine ⟨m, fun n hn => ?_⟩
    have h1 : ‖a - (K n).starProjection a‖ ≤ ‖a - d m‖ := by
      rw [Submodule.starProjection_minimal]
      have hmem : d m ∈ K n := Submodule.subset_span ⟨m, Set.mem_Iic.2 hn, rfl⟩
      exact ciInf_le_of_le ⟨0, by rintro _ ⟨x, rfl⟩; positivity⟩ ⟨d m, hmem⟩ le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, dist_eq_norm, norm_sub_rev]
    calc ‖a - (K n).starProjection a‖ ≤ ‖a - d m‖ := h1
      _ = dist a (d m) := (dist_eq_norm _ _).symm
      _ < ε := hm
  have hlim : ∀ ρ : Measure H, Integrable (fun a : H => ‖a‖ ^ 2) ρ →
      Tendsto (fun n => ∫ a, B ((K n).starProjection a) ((K n).starProjection a) ∂ρ) atTop
        (𝓝 (∫ a, B a a ∂ρ)) := by
    intro ρ hρ
    refine tendsto_integral_of_dominated_convergence (fun a => ‖B‖ * ‖a‖ ^ 2) ?_ (hρ.const_mul _) ?_ ?_
    · intro n
      exact (by fun_prop : Continuous fun a : H => B ((K n).starProjection a) ((K n).starProjection a)).aestronglyMeasurable
    · intro n
      refine Filter.Eventually.of_forall fun a => ?_
      calc ‖B ((K n).starProjection a) ((K n).starProjection a)‖
          ≤ ‖B‖ * ‖(K n).starProjection a‖ * ‖(K n).starProjection a‖ := B.le_opNorm₂ _ _
        _ ≤ ‖B‖ * ‖a‖ * ‖a‖ := by
            gcongr <;> exact (K n).norm_starProjection_apply_le a
        _ = ‖B‖ * ‖a‖ ^ 2 := by ring
    · refine Filter.Eventually.of_forall fun a => ?_
      have h := hconv a
      have hc : Continuous (fun p : H × H => B p.1 p.2) := by fun_prop
      have h2 : Tendsto (fun n => ((K n).starProjection a, (K n).starProjection a)) atTop
          (𝓝 (a, a)) := h.prodMk_nhds h
      have h3 := (hc.tendsto (a, a)).comp h2
      exact h3
  have heq : ∀ n, ∫ a, B ((K n).starProjection a) ((K n).starProjection a) ∂μ =
      ∫ a, B ((K n).starProjection a) ((K n).starProjection a) ∂ν := by
    intro n
    rw [integral_projected_bilinear hμ (K n), integral_projected_bilinear hν (K n)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hcov]
  have h1 := hlim μ hμ
  have h2 := hlim ν hν
  simp_rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

end SecondMoment

section GaussianFacts

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {γ : Measure H} [IsProbabilityMeasure γ]

lemma gaussian_integrable_pow (hγ : IsCenteredGaussian γ) (j : ℕ) :
    Integrable (fun b : H => ‖b‖ ^ j) γ := by
  haveI := hγ.1
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · have := (IsGaussian.memLp_id γ (j : ℝ≥0∞) (by simp)).integrable_norm_pow (by simpa using hj.ne')
    simpa using this

lemma gaussian_map_neg (hγ : IsCenteredGaussian γ) : γ.map (fun b : H => -b) = γ := by
  have h := gaussian_comb_map hγ (a := -1) (s := 0) le_rfl (by norm_num)
  have e : (fun q : H × H => (-1 : ℝ) • q.1 + (0 : ℝ) • q.2) = (fun b : H => -b) ∘ Prod.fst := by
    ext q <;> simp
  rw [e, ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod] at h
  simpa using h

lemma integral_odd_eq_zero (hγ : IsCenteredGaussian γ) {f : H → ℝ} (hf : Continuous f)
    (hodd : ∀ b, f (-b) = - f b) : ∫ b, f b ∂γ = 0 := by
  have h1 : ∫ b, f (-b) ∂γ = ∫ b, f b ∂γ := by
    have := integral_map (μ := γ) (by fun_prop : AEMeasurable (fun b : H => -b) γ) hf.aestronglyMeasurable
    rw [gaussian_map_neg hγ] at this
    exact this.symm
  simp_rw [hodd, integral_neg] at h1
  linarith

lemma momF_gaussian_odd (hγ : IsCenteredGaussian γ) {j : ℕ} (hj : Odd j) (m : H [×j]→L[ℝ] ℝ) :
    momF γ j m = 0 := by
  refine integral_odd_eq_zero hγ (continuous_apply_diag m) fun b => ?_
  have : (fun _ : Fin j => -b) = fun _ : Fin j => (-1 : ℝ) • b := by
    ext; simp
  rw [this, m.map_smul_univ]
  simp [hj.neg_one_pow]

lemma integral_snd_prod' {g : H → ℝ} (hg : Integrable g γ) :
    ∫ q : H × H, g q.2 ∂(γ.prod γ) = ∫ w, g w ∂γ := by
  rw [integral_prod _ (hg.comp_snd γ)]
  simp

/-- Fourth moments of a centered Gaussian are at most three times the squared second moment. -/
lemma gaussian_fourth_le (hγ : IsCenteredGaussian γ) :
    ∫ b, ‖b‖ ^ 4 ∂γ ≤ 3 * (∫ b, ‖b‖ ^ 2 ∂γ) ^ 2 := by
  have hi4 := gaussian_integrable_pow hγ 4
  have hi2 := gaussian_integrable_pow hγ 2
  set Γ := γ.prod γ with hΓ
  set m4 := ∫ b, ‖b‖ ^ 4 ∂γ with hm4
  set m2 := ∫ b, ‖b‖ ^ 2 ∂γ with hm2
  -- pieces
  let gp : H × H → ℝ := fun q => ‖q.1 + q.2‖ ^ 4
  let gm : H × H → ℝ := fun q => ‖q.1 - q.2‖ ^ 4
  let rhs : H × H → ℝ := fun q =>
    2 * ‖q.1‖ ^ 4 + 2 * ‖q.2‖ ^ 4 + 12 * (‖q.1‖ ^ 2 * ‖q.2‖ ^ 2)
  have hrhs_int : Integrable rhs Γ := by
    refine Integrable.add (Integrable.add ?_ ?_) ?_
    · exact (hi4.comp_fst γ).const_mul 2
    · exact (hi4.comp_snd γ).const_mul 2
    · exact (Integrable.mul_prod hi2 hi2).const_mul 12
  have hrhs_val : ∫ q, rhs q ∂Γ = 4 * m4 + 12 * m2 ^ 2 := by
    have e1 : Integrable (fun q : H × H => 2 * ‖q.1‖ ^ 4) Γ := (hi4.comp_fst γ).const_mul 2
    have e2 : Integrable (fun q : H × H => 2 * ‖q.2‖ ^ 4) Γ := (hi4.comp_snd γ).const_mul 2
    have e3 : Integrable (fun q : H × H => 12 * (‖q.1‖ ^ 2 * ‖q.2‖ ^ 2)) Γ :=
      (Integrable.mul_prod hi2 hi2).const_mul 12
    show ∫ q, (2 * ‖q.1‖ ^ 4 + 2 * ‖q.2‖ ^ 4 + 12 * (‖q.1‖ ^ 2 * ‖q.2‖ ^ 2)) ∂Γ = _
    have e12 : Integrable (fun q : H × H => 2 * ‖q.1‖ ^ 4 + 2 * ‖q.2‖ ^ 4) Γ := e1.add e2
    rw [integral_add e12 e3, integral_add e1 e2, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_fst_prod hi4, integral_snd_prod' hi4,
      integral_prod_mul (fun b : H => ‖b‖ ^ 2) (fun b : H => ‖b‖ ^ 2)]
    ring
  have hpt : ∀ q : H × H, gp q + gm q ≤ rhs q := by
    intro q
    obtain ⟨u, v⟩ := q
    simp only [gp, gm, rhs]
    have h1 : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 + 2 * inner ℝ u v := by
      rw [norm_add_sq_real]; ring
    have h2 : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * inner ℝ u v := by
      rw [norm_sub_sq_real]; ring
    have h3 : (inner ℝ u v) ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
      have := abs_real_inner_le_norm u v
      have h0 := abs_nonneg (inner ℝ u v)
      calc (inner ℝ u v) ^ 2 = |inner ℝ u v| ^ 2 := (sq_abs _).symm
        _ ≤ (‖u‖ * ‖v‖) ^ 2 := by gcongr
        _ = _ := by ring
    have e : ‖u + v‖ ^ 4 + ‖u - v‖ ^ 4 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) ^ 2 + 8 * (inner ℝ u v) ^ 2 := by
      have : ‖u + v‖ ^ 4 = (‖u + v‖ ^ 2) ^ 2 := by ring
      have : ‖u - v‖ ^ 4 = (‖u - v‖ ^ 2) ^ 2 := by ring
      rw [‹‖u + v‖ ^ 4 = _›, ‹‖u - v‖ ^ 4 = _›, h1, h2]; ring
    rw [e]
    nlinarith [h3]
  have hgp_int : Integrable gp Γ := by
    refine Integrable.mono' hrhs_int (by fun_prop : Continuous gp).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun q => ?_
    have := hpt q
    have h0 : 0 ≤ gm q := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hgm_int : Integrable gm Γ := by
    refine Integrable.mono' hrhs_int (by fun_prop : Continuous gm).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun q => ?_
    have := hpt q
    have h0 : 0 ≤ gp q := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  -- rotation
  have hrot : m4 = (1 / 4) * ∫ q, gp q ∂Γ := by
    have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hs : ((Real.sqrt 2)⁻¹) ^ 2 + ((Real.sqrt 2)⁻¹) ^ 2 = 1 := by
      rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
    have hmap := gaussian_comb_map hγ (a := (Real.sqrt 2)⁻¹) (s := (Real.sqrt 2)⁻¹)
      (inv_nonneg.2 h2.le) hs
    have := integral_map (μ := Γ) (by fun_prop : AEMeasurable
      (fun q : H × H => (Real.sqrt 2)⁻¹ • q.1 + (Real.sqrt 2)⁻¹ • q.2) Γ)
      (f := fun z : H => ‖z‖ ^ 4) (by fun_prop : Continuous fun z : H => ‖z‖ ^ 4).aestronglyMeasurable
    rw [hmap] at this
    rw [hm4, this, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [gp]
    rw [← smul_add, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 h2), mul_pow, inv_pow]
    rw [show (Real.sqrt 2) ^ 4 = 4 by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by norm_num)]; norm_num]
    ring
  -- flip
  have hflip : ∫ q, gm q ∂Γ = ∫ q, gp q ∂Γ := by
    have hmap : Γ.map (Prod.map (id : H → H) (fun b : H => -b)) = Γ := by
      rw [hΓ, ← Measure.map_prod_map _ _ measurable_id (by fun_prop : Measurable fun b : H => -b)]
      rw [gaussian_map_neg hγ, Measure.map_id]
    have := integral_map (μ := Γ)
      (by fun_prop : AEMeasurable (Prod.map (id : H → H) (fun b : H => -b)) Γ)
      (f := gp) (by fun_prop : Continuous gp).aestronglyMeasurable
    rw [hmap] at this
    rw [this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp [gp, gm, sub_eq_add_neg]
  have hsum : ∫ q, gp q ∂Γ + ∫ q, gm q ∂Γ ≤ ∫ q, rhs q ∂Γ := by
    rw [← integral_add hgp_int hgm_int]
    exact integral_mono (hgp_int.add hgm_int) hrhs_int hpt
  rw [hflip, hrhs_val] at hsum
  have hm2nn : 0 ≤ m2 := integral_nonneg fun b => by positivity
  nlinarith [hrot, hsum]

/-- Stability of a centered Gaussian law under normalized i.i.d. sums. -/
lemma gaussian_stable (hγ : IsCenteredGaussian γ) :
    ∀ n : ℕ, (Measure.pi (fun _ : Fin (n + 1) => γ)).map
      (fun z : Fin (n + 1) → H => (Real.sqrt ((n : ℝ) + 1))⁻¹ • ∑ i, z i) = γ := by
  intro n
  induction n with
  | zero =>
    have h := (measurePreserving_eval (fun _ : Fin 1 => γ) 0).map_eq
    simpa using h
  | succ n ih =>
    have hpos : (0:ℝ) < (n : ℝ) + 1 := by positivity
    have hpos2 : (0:ℝ) < ((n + 1 : ℕ) : ℝ) + 1 := by positivity
    set a : ℝ := (Real.sqrt (((n + 1 : ℕ) : ℝ) + 1))⁻¹ with ha
    set s : ℝ := Real.sqrt ((n : ℝ) + 1) * (Real.sqrt (((n + 1 : ℕ) : ℝ) + 1))⁻¹ with hs
    have has : a ^ 2 + s ^ 2 = 1 := by
      rw [ha, hs, mul_pow, inv_pow, Real.sq_sqrt hpos2.le, Real.sq_sqrt hpos.le]
      push_cast
      field_simp
      ring
    have hs0 : 0 ≤ s := by positivity
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 2) => γ) 0
    set T : (Fin (n + 1) → H) → H := fun w => (Real.sqrt ((n : ℝ) + 1))⁻¹ • ∑ i, w i with hT
    have hTm : Measurable T := by fun_prop
    have hfun : (fun z : Fin (n + 2) → H => a • ∑ i, z i) =
        (fun q : H × H => a • q.1 + s • q.2) ∘ (Prod.map id T) ∘
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => H) 0) := by
      funext z
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, hT,
        MeasurableEquiv.piFinSuccAbove_apply]
      rw [Fin.sum_univ_succ, smul_add, smul_smul]
      have h1 : ((Fin.insertNthEquiv (fun _ => H) 0).symm z).1 = z 0 := rfl
      have h2 : ∀ i, ((Fin.insertNthEquiv (fun _ => H) 0).symm z).2 i = z i.succ := fun i => by
        show z (Fin.succAbove 0 i) = _
        rw [Fin.succAbove_zero]
      simp_rw [h1, h2]
      have : Real.sqrt ((n : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
      have e : s * (Real.sqrt ((n : ℝ) + 1))⁻¹ = a := by
        rw [hs, mul_assoc, mul_comm ((Real.sqrt (((n + 1 : ℕ) : ℝ) + 1))⁻¹), ← mul_assoc,
          mul_inv_cancel₀ this, one_mul]
      rw [e]
    have hcomb := gaussian_comb_map hγ hs0 has
    have hmeq := hmp.map_eq
    have hg : Measurable fun q : H × H => a • q.1 + s • q.2 := by fun_prop
    rw [hfun, ← Measure.map_map hg (by fun_prop), ← Measure.map_map (by fun_prop) (by fun_prop),
      hmeq, ← Measure.map_prod_map _ _ measurable_id hTm, ih, Measure.map_id, hcomb]

end GaussianFacts

section Swap

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H]

lemma iteratedFDeriv_smul_diag {k : ℕ} (m : H [×k]→L[ℝ] ℝ) (c : ℝ) (a : H) :
    m (fun _ => c • a) = c ^ k * m (fun _ => a) := by
  have := m.map_smul_univ (fun _ : Fin k => c) (fun _ => a)
  simpa [Finset.prod_const] using this

lemma integral_taylor_poly {ρ : Measure H} {n : ℕ} (hρ : ∀ j ≤ n, Integrable (fun a : H => ‖a‖ ^ j) ρ)
    (f : H → ℝ) (r : H) (c : ℝ) :
    ∫ a, ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹) * iteratedFDeriv ℝ k f r (fun _ => c • a) ∂ρ =
      ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹) * c ^ k * momF ρ k (iteratedFDeriv ℝ k f r) := by
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    simp_rw [iteratedFDeriv_smul_diag]
    rw [integral_const_mul, integral_const_mul, momF]
    ring
  · intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    simp_rw [iteratedFDeriv_smul_diag]
    exact ((integrable_apply_diag (hρ k hk') _).const_mul _).const_mul _

/-- Expansion of `∫ f(r + c a) dρ` into moment terms plus a remainder. -/
lemma integral_expand {ρ : Measure H} {n : ℕ} {f : H → ℝ} (hf : ContDiff ℝ (n + 1) f) {L : ℝ}
    (hL : ∀ x, ‖iteratedFDeriv ℝ (n + 1) f x‖ ≤ L) (hρ : ∀ j ≤ n + 1, Integrable (fun a : H => ‖a‖ ^ j) ρ)
    (r : H) {c : ℝ} (hc : 0 ≤ c) :
    ∃ E : ℝ, ∫ a, f (r + c • a) ∂ρ =
        ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹) * c ^ k * momF ρ k (iteratedFDeriv ℝ k f r) + E ∧
      |E| ≤ L * c ^ (n + 1) * (∫ a, ‖a‖ ^ (n + 1) ∂ρ) / ((n + 1)! : ℝ) := by
  set poly : H → ℝ := fun a => ∑ k ∈ Finset.range (n + 1),
    ((k ! : ℝ)⁻¹) * iteratedFDeriv ℝ k f r (fun _ => c • a) with hpoly
  set rem : H → ℝ := fun a => f (r + c • a) - poly a with hrem
  have hfc : Continuous f := hf.continuous
  have hpoly_cont : Continuous poly := by
    refine continuous_finset_sum _ fun k _ => continuous_const.mul ?_
    exact (iteratedFDeriv ℝ k f r).cont.comp (continuous_pi fun _ => continuous_const.smul continuous_id)
  have hrem_bd : ∀ a, |rem a| ≤ L * c ^ (n + 1) * ‖a‖ ^ (n + 1) / ((n + 1)! : ℝ) := by
    intro a
    have := taylor_bound hf hL r (c • a)
    simp only [hrem, hpoly]
    refine this.trans_eq ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_pow]
    ring
  have hrem_int : Integrable rem ρ := by
    refine Integrable.mono' (((hρ (n + 1) le_rfl).const_mul (L * c ^ (n + 1))).div_const ((n + 1)! : ℝ))
      ((hfc.comp (by fun_prop : Continuous fun a : H => r + c • a)).sub hpoly_cont).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs]; exact hrem_bd a
  have hpoly_int : Integrable poly ρ := by
    refine integrable_finsetSum _ fun k hk => ?_
    have hk' : k ≤ n + 1 := by have := Finset.mem_range.1 hk; omega
    simp_rw [iteratedFDeriv_smul_diag]
    exact ((integrable_apply_diag (hρ k hk') _).const_mul _).const_mul _
  refine ⟨∫ a, rem a ∂ρ, ?_, ?_⟩
  · have : ∫ a, f (r + c • a) ∂ρ = ∫ a, (poly a + rem a) ∂ρ := by
      congr 1; ext a; simp [hrem]
    rw [this, integral_add hpoly_int hrem_int, hpoly,
      integral_taylor_poly (fun j hj => hρ j (by omega))]
  · rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ a, ‖rem a‖ ∂ρ ≤ ∫ a, L * c ^ (n + 1) * ‖a‖ ^ (n + 1) / ((n + 1)! : ℝ) ∂ρ :=
          integral_mono hrem_int.norm
            (((hρ (n + 1) le_rfl).const_mul (L * c ^ (n + 1))).div_const _)
            (fun a => by rw [Real.norm_eq_abs]; exact hrem_bd a)
      _ = _ := by
          rw [integral_div, integral_const_mul]

lemma swap_pointwise {μ γ : Measure H} {n : ℕ} {f : H → ℝ} (hf : ContDiff ℝ (n + 1) f) {L : ℝ}
    (hL : ∀ x, ‖iteratedFDeriv ℝ (n + 1) f x‖ ≤ L)
    (hμ : ∀ j ≤ n + 1, Integrable (fun a : H => ‖a‖ ^ j) μ)
    (hγ : ∀ j ≤ n + 1, Integrable (fun a : H => ‖a‖ ^ j) γ)
    (hmatch : ∀ k < n, ∀ m : H [×k]→L[ℝ] ℝ, momF μ k m = momF γ k m) (r : H) {c : ℝ} (hc : 0 ≤ c) :
    |∫ a, f (r + c • a) ∂μ - ∫ a, f (r + c • a) ∂γ -
        ((n ! : ℝ)⁻¹ * c ^ n * (momF μ n (iteratedFDeriv ℝ n f r) - momF γ n (iteratedFDeriv ℝ n f r)))|
      ≤ L * c ^ (n + 1) * ((∫ a, ‖a‖ ^ (n + 1) ∂μ) + ∫ a, ‖a‖ ^ (n + 1) ∂γ) / ((n + 1)! : ℝ) := by
  obtain ⟨E₁, hE₁, hb₁⟩ := integral_expand hf hL hμ r hc
  obtain ⟨E₂, hE₂, hb₂⟩ := integral_expand hf hL hγ r hc
  have hsum : ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹) * c ^ k * momF μ k (iteratedFDeriv ℝ k f r) -
      ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹) * c ^ k * momF γ k (iteratedFDeriv ℝ k f r) =
      (n ! : ℝ)⁻¹ * c ^ n * (momF μ n (iteratedFDeriv ℝ n f r) - momF γ n (iteratedFDeriv ℝ n f r)) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_range_succ]
    have : ∑ k ∈ Finset.range n, (((k ! : ℝ)⁻¹) * c ^ k * momF μ k (iteratedFDeriv ℝ k f r) -
        ((k ! : ℝ)⁻¹) * c ^ k * momF γ k (iteratedFDeriv ℝ k f r)) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [hmatch k (Finset.mem_range.1 hk)]; ring
    rw [this, zero_add]; ring
  rw [hE₁, hE₂]
  have : ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹) * c ^ k * momF μ k (iteratedFDeriv ℝ k f r) + E₁ -
      (∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹) * c ^ k * momF γ k (iteratedFDeriv ℝ k f r) + E₂) -
      ((n ! : ℝ)⁻¹ * c ^ n * (momF μ n (iteratedFDeriv ℝ n f r) - momF γ n (iteratedFDeriv ℝ n f r)))
      = E₁ - E₂ := by rw [← hsum]; ring
  rw [this]
  calc |E₁ - E₂| ≤ |E₁| + |E₂| := abs_sub _ _
    _ ≤ _ := by
      have := add_le_add hb₁ hb₂
      refine this.trans_eq ?_
      ring

end Swap

section IndepExpect

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma integral_indep_add {R U : Ω → H} (hR : Measurable R) (hU : Measurable U)
    (hind : IndepFun R U P) {f : H → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) (c : ℝ) :
    ∫ ω, f (R ω + c • U ω) ∂P = ∫ r, ∫ a, f (r + c • a) ∂(P.map U) ∂(P.map R) ∧
      Integrable (fun r => ∫ a, f (r + c • a) ∂(P.map U)) (P.map R) := by
  have : IsProbabilityMeasure (P.map R) := (Measure.isProbabilityMeasure_map_iff hR.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (P.map U) := (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
  have hprod := hind.map_prod_eq_prod_map_map hR.aemeasurable hU.aemeasurable
  have hg : Continuous fun q : H × H => f (q.1 + c • q.2) := hf.comp (by fun_prop)
  have hint : Integrable (fun q : H × H => f (q.1 + c • q.2)) ((P.map R).prod (P.map U)) :=
    Integrable.of_bound hg.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hM _)
  have h1 : ∫ ω, f (R ω + c • U ω) ∂P =
      ∫ q, f (q.1 + c • q.2) ∂(P.map fun ω => (R ω, U ω)) := by
    rw [integral_map (hR.prodMk hU).aemeasurable hg.aestronglyMeasurable]
  refine ⟨?_, hint.integral_prod_left⟩
  rw [h1, hprod, integral_prod _ hint]

lemma step_bound {R U W : Ω → H} (hR : Measurable R) (hU : Measurable U) (hW : Measurable W)
    (hRU : IndepFun R U P) (hRW : IndepFun R W P) {μ γ : Measure H}
    (hUμ : P.map U = μ) (hWγ : P.map W = γ) {n : ℕ} {f : H → ℝ} (hf : ContDiff ℝ (n + 1) f)
    {L : ℝ} (hL : ∀ x, ‖iteratedFDeriv ℝ (n + 1) f x‖ ≤ L) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    {K : ℝ} (hK : ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ K)
    (hμ : ∀ j ≤ n + 1, Integrable (fun a : H => ‖a‖ ^ j) μ)
    (hγ : ∀ j ≤ n + 1, Integrable (fun a : H => ‖a‖ ^ j) γ)
    (hmatch : ∀ k < n, ∀ m : H [×k]→L[ℝ] ℝ, momF μ k m = momF γ k m) {c : ℝ} (hc : 0 ≤ c) :
    |∫ ω, f (R ω + c • U ω) ∂P - ∫ ω, f (R ω + c • W ω) ∂P -
        (n ! : ℝ)⁻¹ * c ^ n * ∫ ω, (momF μ n (iteratedFDeriv ℝ n f (R ω)) -
          momF γ n (iteratedFDeriv ℝ n f (R ω))) ∂P|
      ≤ L * c ^ (n + 1) * ((∫ a, ‖a‖ ^ (n + 1) ∂μ) + ∫ a, ‖a‖ ^ (n + 1) ∂γ) / ((n + 1)! : ℝ) := by
  have : IsProbabilityMeasure (P.map R) := (Measure.isProbabilityMeasure_map_iff hR.aemeasurable).2 inferInstance
  obtain ⟨h1, i1⟩ := integral_indep_add hR hU hRU hf.continuous hM c
  obtain ⟨h2, i2⟩ := integral_indep_add hR hW hRW hf.continuous hM c
  rw [hUμ] at h1 i1
  rw [hWγ] at h2 i2
  set T : H → ℝ := fun r => momF μ n (iteratedFDeriv ℝ n f r) - momF γ n (iteratedFDeriv ℝ n f r)
    with hT
  have hDn_cont : Continuous (iteratedFDeriv ℝ n f) :=
    hf.continuous_iteratedFDeriv (by exact_mod_cast Nat.le_succ n)
  have hTcont : Continuous T := by
    have e1 : Continuous fun r => momF μ n (iteratedFDeriv ℝ n f r) :=
      (momCLM μ (hμ n (Nat.le_succ n))).continuous.comp hDn_cont
    have e2 : Continuous fun r => momF γ n (iteratedFDeriv ℝ n f r) :=
      (momCLM γ (hγ n (Nat.le_succ n))).continuous.comp hDn_cont
    exact e1.sub e2
  have hTb : ∀ r, |T r| ≤ K * (∫ a, ‖a‖ ^ n ∂μ) + K * ∫ a, ‖a‖ ^ n ∂γ := by
    intro r
    have a1 := abs_momF_le (hμ n (Nat.le_succ n)) (iteratedFDeriv ℝ n f r)
    have a2 := abs_momF_le (hγ n (Nat.le_succ n)) (iteratedFDeriv ℝ n f r)
    have n1 : 0 ≤ ∫ a, ‖a‖ ^ n ∂μ := integral_nonneg fun a => by positivity
    have n2 : 0 ≤ ∫ a, ‖a‖ ^ n ∂γ := integral_nonneg fun a => by positivity
    calc |T r| ≤ |momF μ n (iteratedFDeriv ℝ n f r)| + |momF γ n (iteratedFDeriv ℝ n f r)| :=
          abs_sub _ _
      _ ≤ _ := by
          have := hK r
          nlinarith [mul_le_mul_of_nonneg_right this n1, mul_le_mul_of_nonneg_right this n2]
  have hTint : Integrable T (P.map R) :=
    Integrable.of_bound hTcont.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun r => by rw [Real.norm_eq_abs]; exact hTb r)
  have h3 : ∫ ω, (momF μ n (iteratedFDeriv ℝ n f (R ω)) - momF γ n (iteratedFDeriv ℝ n f (R ω))) ∂P
      = ∫ r, T r ∂(P.map R) := by
    rw [integral_map hR.aemeasurable hTcont.aestronglyMeasurable]
  have i12 : Integrable (fun r => ∫ a, f (r + c • a) ∂μ - ∫ a, f (r + c • a) ∂γ) (P.map R) :=
    i1.sub i2
  rw [h1, h2, h3, ← integral_sub i1 i2, ← integral_const_mul,
    ← integral_sub i12 (hTint.const_mul _)]
  have hpt : ∀ r, ‖(∫ a, f (r + c • a) ∂μ - ∫ a, f (r + c • a) ∂γ) - (n ! : ℝ)⁻¹ * c ^ n * T r‖ ≤
      L * c ^ (n + 1) * ((∫ a, ‖a‖ ^ (n + 1) ∂μ) + ∫ a, ‖a‖ ^ (n + 1) ∂γ) / ((n + 1)! : ℝ) := by
    intro r
    rw [Real.norm_eq_abs]
    have := swap_pointwise hf hL hμ hγ hmatch r hc
    simpa [hT, mul_assoc] using this
  have := norm_integral_le_of_norm_le_const (μ := P.map R) (C := L * c ^ (n + 1) *
    ((∫ a, ‖a‖ ^ (n + 1) ∂μ) + ∫ a, ‖a‖ ^ (n + 1) ∂γ) / ((n + 1)! : ℝ))
    (f := fun r => (∫ a, f (r + c • a) ∂μ - ∫ a, f (r + c • a) ∂γ) - (n ! : ℝ)⁻¹ * c ^ n * T r)
    (Filter.Eventually.of_forall hpt)
  simpa using this

end IndepExpect

section Hybrid

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H]
variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

/-- Hybrid sum: indices in `A` use `Y`, the remaining indices of `I` use `Z`. -/
def hyb (Y Z : Fin N → Ω → H) (c : ℝ) (A I : Finset (Fin N)) (ω : Ω) : H :=
  c • ∑ i ∈ I, (if i ∈ A then Y i ω else Z i ω)

lemma hyb_Y (Y Z : Fin N → Ω → H) (c : ℝ) {A I : Finset (Fin N)} {i : Fin N} (hiA : i ∈ A)
    (hiI : i ∈ I) (ω : Ω) :
    hyb Y Z c A I ω = hyb Y Z c (A.erase i) (I.erase i) ω + c • Y i ω := by
  unfold hyb
  rw [← Finset.add_sum_erase I _ hiI, smul_add, if_pos hiA, add_comm]
  congr 2
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  simp [Finset.mem_erase, hji]

lemma hyb_Z (Y Z : Fin N → Ω → H) (c : ℝ) {A I : Finset (Fin N)} {i : Fin N}
    (hiI : i ∈ I) (ω : Ω) :
    hyb Y Z c (A.erase i) I ω = hyb Y Z c (A.erase i) (I.erase i) ω + c • Z i ω := by
  unfold hyb
  rw [← Finset.add_sum_erase I _ hiI, smul_add, if_neg (by simp), add_comm]

lemma measurable_hyb {Y Z : Fin N → Ω → H} (hY : ∀ i, Measurable (Y i))
    (hZ : ∀ i, Measurable (Z i)) (c : ℝ) (A I : Finset (Fin N)) : Measurable (hyb Y Z c A I) := by
  unfold hyb
  refine Measurable.const_smul (Finset.measurable_sum _ fun i _ => ?_) c
  by_cases h : i ∈ A
  · simpa [h] using hY i
  · simpa [h] using hZ i

lemma indep_hyb {P : Measure Ω} [IsProbabilityMeasure P] {Y Z : Fin N → Ω → H}
    (hY : ∀ i, Measurable (Y i)) (hZ : ∀ i, Measurable (Z i))
    (hind : iIndepFun (fun j : Fin N ⊕ Fin N => Sum.elim Y Z j) P) (c : ℝ)
    (A I : Finset (Fin N)) {i : Fin N} (hi : i ∉ I) :
    IndepFun (hyb Y Z c A I) (Y i) P ∧ IndepFun (hyb Y Z c A I) (Z i) P := by
  classical
  let idx : Fin N → Fin N ⊕ Fin N := fun j => if j ∈ A then Sum.inl j else Sum.inr j
  have hidx : Function.Injective idx := by
    intro a b hab
    by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> simp [idx, ha, hb] at hab <;> exact hab
  let S : Finset (Fin N ⊕ Fin N) := I.image idx
  have hmeas : ∀ k : Fin N ⊕ Fin N, Measurable (Sum.elim Y Z k) := by
    rintro (k | k)
    · exact hY k
    · exact hZ k
  have hsum : hyb Y Z c A I = (fun x : H => c • x) ∘ (∑ k ∈ S, Sum.elim Y Z k) := by
    funext ω
    unfold hyb
    simp only [Function.comp_apply]
    congr 1
    rw [Finset.sum_apply, Finset.sum_image (fun a _ b _ h => hidx h)]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ A <;> simp [idx, hj]
  have hcomp : Measurable fun x : H => c • x := measurable_const_smul c
  constructor
  · have hnot : Sum.inl i ∉ S := by
      simp only [S, Finset.mem_image, not_exists, not_and]
      intro j hj hji
      have : j = i := by
        by_cases hjA : j ∈ A <;> simp [idx, hjA] at hji; exact hji
      exact hi (this ▸ hj)
    have := (hind.indepFun_finsetSum_of_notMem hmeas hnot).comp hcomp measurable_id
    rw [hsum]; exact this
  · have hnot : Sum.inr i ∉ S := by
      simp only [S, Finset.mem_image, not_exists, not_and]
      intro j hj hji
      have : j = i := by
        by_cases hjA : j ∈ A <;> simp [idx, hjA] at hji; exact hji
      exact hi (this ▸ hj)
    have := (hind.indepFun_finsetSum_of_notMem hmeas hnot).comp hcomp measurable_id
    rw [hsum]; exact this

/-- Data for the Lindeberg argument. -/
structure Setup {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ} (Y Z : Fin N → Ω → H)
    (μ γ : Measure H) : Prop where
  measY : ∀ i, Measurable (Y i)
  measZ : ∀ i, Measurable (Z i)
  indep : iIndepFun (fun j : Fin N ⊕ Fin N => Sum.elim Y Z j) P
  lawY : ∀ i, P.map (Y i) = μ
  lawZ : ∀ i, P.map (Z i) = γ

/-- Moment matching between `μ` and `γ`. -/
structure Matching (μ γ : Measure H) : Prop where
  intμ : ∀ j ≤ 4, Integrable (fun a : H => ‖a‖ ^ j) μ
  intγ : ∀ j ≤ 4, Integrable (fun a : H => ‖a‖ ^ j) γ
  eq0 : ∀ m : H [×0]→L[ℝ] ℝ, momF μ 0 m = momF γ 0 m
  eq1 : ∀ m : H [×1]→L[ℝ] ℝ, momF μ 1 m = momF γ 1 m
  eq2 : ∀ m : H [×2]→L[ℝ] ℝ, momF μ 2 m = momF γ 2 m
  odd3 : ∀ m : H [×3]→L[ℝ] ℝ, momF γ 3 m = 0
  eqB : ∀ B : H →L[ℝ] H →L[ℝ] ℝ, ∫ a, B a a ∂μ = ∫ a, B a a ∂γ
  cenμ : ∫ a, a ∂μ = 0
  cenγ : ∫ a, a ∂γ = 0

lemma Setup.measurable_hyb' {P : Measure Ω} {Y Z : Fin N → Ω → H} {μ γ : Measure H} (S : Setup P Y Z μ γ) (c : ℝ) (A I : Finset (Fin N)) :
    Measurable (hyb Y Z c A I) := measurable_hyb S.measY S.measZ c A I

lemma Matching.eq_le {μ γ : Measure H} (M : Matching μ γ) {k : ℕ} (hk : k ≤ 2)
    (m : H [×k]→L[ℝ] ℝ) : momF μ k m = momF γ k m := by
  interval_cases k
  · exact M.eq0 m
  · exact M.eq1 m
  · exact M.eq2 m

variable {P : Measure Ω} [IsProbabilityMeasure P] {Y Z : Fin N → Ω → H} {μ γ : Measure H}

/-- Third-order Lindeberg: replacing `Y`'s by `Z`'s costs at most `L c³ (m₃ + m₃')/6` each. -/
lemma ind3 (S : Setup P Y Z μ γ) (M : Matching μ γ) {f : H → ℝ} (hf : ContDiff ℝ (2 + 1) f)
    {L : ℝ} (hL : ∀ x, ‖iteratedFDeriv ℝ (2 + 1) f x‖ ≤ L) {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    {K : ℝ} (hK : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ K) {c : ℝ} (hc : 0 ≤ c)
    (A I : Finset (Fin N)) (hAI : A ⊆ I) :
    |∫ ω, f (hyb Y Z c A I ω) ∂P - ∫ ω, f (hyb Y Z c ∅ I ω) ∂P| ≤
      A.card * (L * c ^ (2 + 1) * ((∫ a, ‖a‖ ^ (2 + 1) ∂μ) + ∫ a, ‖a‖ ^ (2 + 1) ∂γ) /
        ((2 + 1)! : ℝ)) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert i A hiA ih =>
    have hAI' : A ⊆ I := (Finset.subset_insert i A).trans hAI
    have hiI : i ∈ I := hAI (Finset.mem_insert_self i A)
    have hiR : i ∉ I.erase i := by simp
    obtain ⟨hindY, hindZ⟩ := indep_hyb S.measY S.measZ S.indep c A (I.erase i) hiR
    have hstep := step_bound (P := P) (S.measurable_hyb' c A (I.erase i)) (S.measY i) (S.measZ i)
      hindY hindZ (S.lawY i) (S.lawZ i) (n := 2) hf hL hB hK
      (fun j hj => M.intμ j (by omega)) (fun j hj => M.intγ j (by omega))
      (fun k hk m => M.eq_le (by omega) m) hc
    have hzero : ∫ ω, (momF μ 2 (iteratedFDeriv ℝ 2 f (hyb Y Z c A (I.erase i) ω)) -
        momF γ 2 (iteratedFDeriv ℝ 2 f (hyb Y Z c A (I.erase i) ω))) ∂P = 0 := by
      simp_rw [M.eq2, sub_self]; simp
    rw [hzero, mul_zero, sub_zero] at hstep
    have e1 : ∀ ω, hyb Y Z c (insert i A) I ω = hyb Y Z c A (I.erase i) ω + c • Y i ω := by
      intro ω
      rw [hyb_Y Y Z c (Finset.mem_insert_self i A) hiI, Finset.erase_insert hiA]
    have e2 : ∀ ω, hyb Y Z c A I ω = hyb Y Z c A (I.erase i) ω + c • Z i ω := by
      intro ω
      have := hyb_Z Y Z c (A := insert i A) hiI ω
      rwa [Finset.erase_insert hiA] at this
    have ih' := ih hAI'
    simp_rw [e2] at ih'
    simp_rw [e1]
    rw [Finset.card_insert_of_notMem hiA]
    push_cast
    have := abs_sub_le (∫ ω, f (hyb Y Z c A (I.erase i) ω + c • Y i ω) ∂P)
      (∫ ω, f (hyb Y Z c A (I.erase i) ω + c • Z i ω) ∂P) (∫ ω, f (hyb Y Z c ∅ I ω) ∂P)
    nlinarith [this, hstep, ih']


/-- The prefix `{j | j < k}`. -/
def pref (N k : ℕ) : Finset (Fin N) := Finset.univ.filter fun j : Fin N => (j : ℕ) < k

lemma pref_zero (N : ℕ) : pref N 0 = ∅ := by
  ext j; simp [pref]

lemma pref_succ {N k : ℕ} (hk : k < N) :
    pref N (k + 1) = insert ⟨k, hk⟩ (pref N k) ∧ (⟨k, hk⟩ : Fin N) ∉ pref N k := by
  constructor
  · ext j
    simp only [pref, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases hj : (j : ℕ) < k
      · exact Or.inr hj
      · left; ext; simp; omega
    · rintro (rfl | h)
      · simp
      · omega
  · simp [pref]

lemma pref_self (N : ℕ) : pref N N = Finset.univ := by
  ext j; simp [pref]

/-- Fourth-order Lindeberg telescoping. -/
lemma ind4 (S : Setup P Y Z μ γ) (M : Matching μ γ) {f : H → ℝ} (hf : ContDiff ℝ (3 + 1) f)
    {L : ℝ} (hL : ∀ x, ‖iteratedFDeriv ℝ (3 + 1) f x‖ ≤ L) {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    {K : ℝ} (hK : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ K) {c : ℝ} (hc : 0 ≤ c) :
    ∀ k : ℕ, k ≤ N →
    |∫ ω, f (hyb Y Z c (pref N k) Finset.univ ω) ∂P - ∫ ω, f (hyb Y Z c ∅ Finset.univ ω) ∂P -
        (3 ! : ℝ)⁻¹ * c ^ 3 * ∑ j ∈ pref N k,
          ∫ ω, momF μ 3 (iteratedFDeriv ℝ 3 f (hyb Y Z c (pref N j) (Finset.univ.erase j) ω)) ∂P|
      ≤ k * (L * c ^ (3 + 1) * ((∫ a, ‖a‖ ^ (3 + 1) ∂μ) + ∫ a, ‖a‖ ^ (3 + 1) ∂γ) /
        ((3 + 1)! : ℝ)) := by
  intro k
  induction k with
  | zero => intro _; simp [pref_zero]
  | succ k ih =>
    intro hk
    have hkN : k < N := hk
    obtain ⟨hins, hnot⟩ := pref_succ hkN
    set j0 : Fin N := ⟨k, hkN⟩ with hj0
    have ih' := ih hkN.le
    have hiR : j0 ∉ Finset.univ.erase j0 := by simp
    obtain ⟨hindY, hindZ⟩ := indep_hyb S.measY S.measZ S.indep c (pref N k) (Finset.univ.erase j0) hiR
    have hstep := step_bound (P := P) (S.measurable_hyb' c (pref N k) (Finset.univ.erase j0))
      (S.measY j0) (S.measZ j0) hindY hindZ (S.lawY j0) (S.lawZ j0) (n := 3) hf hL hB hK
      (fun j hj => M.intμ j (by omega)) (fun j hj => M.intγ j (by omega))
      (fun k' hk' m => M.eq_le (by omega) m) hc
    have hodd : ∀ ω, momF γ 3 (iteratedFDeriv ℝ 3 f (hyb Y Z c (pref N k) (Finset.univ.erase j0) ω)) = 0 :=
      fun ω => M.odd3 _
    simp_rw [hodd, sub_zero] at hstep
    have e1 : ∀ ω, hyb Y Z c (pref N (k + 1)) Finset.univ ω =
        hyb Y Z c (pref N k) (Finset.univ.erase j0) ω + c • Y j0 ω := by
      intro ω
      rw [hins, hyb_Y Y Z c (Finset.mem_insert_self _ _) (Finset.mem_univ _),
        Finset.erase_insert hnot]
    have e2 : ∀ ω, hyb Y Z c (pref N k) Finset.univ ω =
        hyb Y Z c (pref N k) (Finset.univ.erase j0) ω + c • Z j0 ω := by
      intro ω
      have := hyb_Z Y Z c (A := pref N (k + 1)) (I := Finset.univ) (i := j0) (Finset.mem_univ _) ω
      rwa [hins, Finset.erase_insert hnot] at this
    have hsum : ∑ j ∈ pref N (k + 1),
          ∫ ω, momF μ 3 (iteratedFDeriv ℝ 3 f (hyb Y Z c (pref N j) (Finset.univ.erase j) ω)) ∂P =
        (∫ ω, momF μ 3 (iteratedFDeriv ℝ 3 f (hyb Y Z c (pref N k) (Finset.univ.erase j0) ω)) ∂P) +
        ∑ j ∈ pref N k,
          ∫ ω, momF μ 3 (iteratedFDeriv ℝ 3 f (hyb Y Z c (pref N j) (Finset.univ.erase j) ω)) ∂P := by
      rw [hins, Finset.sum_insert hnot]
    rw [hsum]
    simp_rw [e1]
    simp_rw [e2] at ih'
    push_cast
    generalize (∫ ω, f (hyb Y Z c (pref N k) (Finset.univ.erase j0) ω + c • Y j0 ω) ∂P) = a at *
    generalize (∫ ω, f (hyb Y Z c (pref N k) (Finset.univ.erase j0) ω + c • Z j0 ω) ∂P) = b at *
    generalize (∫ ω, f (hyb Y Z c ∅ Finset.univ ω) ∂P) = c0 at *
    generalize (∫ ω, momF μ 3 (iteratedFDeriv ℝ 3 f
      (hyb Y Z c (pref N k) (Finset.univ.erase j0) ω)) ∂P) = T at *
    generalize (∑ j ∈ pref N k, ∫ ω, momF μ 3 (iteratedFDeriv ℝ 3 f
      (hyb Y Z c (pref N j) (Finset.univ.erase j) ω)) ∂P) = Ssum at *
    generalize (L * c ^ (3 + 1) * ((∫ a, ‖a‖ ^ (3 + 1) ∂μ) + ∫ a, ‖a‖ ^ (3 + 1) ∂γ) /
        ((3 + 1)! : ℝ)) = δ at *
    have h := abs_add_le (a - b - (3 ! : ℝ)⁻¹ * c ^ 3 * T) (b - c0 - (3 ! : ℝ)⁻¹ * c ^ 3 * Ssum)
    have e : a - c0 - (3 ! : ℝ)⁻¹ * c ^ 3 * (T + Ssum) =
        (a - b - (3 ! : ℝ)⁻¹ * c ^ 3 * T) + (b - c0 - (3 ! : ℝ)⁻¹ * c ^ 3 * Ssum) := by ring
    rw [e]
    linarith

/-- The product probability space carrying `N` independent copies of `μ` and `N` of `γ`. -/
def prodMeasure (N : ℕ) (μ γ : Measure H) : Measure (Fin N ⊕ Fin N → H) :=
  Measure.pi (fun j : Fin N ⊕ Fin N => (Sum.elim (fun _ : Fin N => μ) (fun _ : Fin N => γ) j : Measure H))

instance prodMeasure.isProb (N : ℕ) (μ γ : Measure H) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure γ] : IsProbabilityMeasure (prodMeasure N μ γ) := by
  unfold prodMeasure
  haveI : ∀ j : Fin N ⊕ Fin N, IsProbabilityMeasure
      (Sum.elim (fun _ : Fin N => μ) (fun _ : Fin N => γ) j : Measure H) := by
    intro j; cases j <;> simpa
  infer_instance

/-- Coordinate maps on the product space. -/
def coordY (N : ℕ) (i : Fin N) (ω : Fin N ⊕ Fin N → H) : H := ω (Sum.inl i)

/-- Coordinate maps on the product space. -/
def coordZ (N : ℕ) (i : Fin N) (ω : Fin N ⊕ Fin N → H) : H := ω (Sum.inr i)

lemma setup_prod (N : ℕ) (μ γ : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ] :
    Setup (prodMeasure N μ γ) (coordY (H := H) N) (coordZ (H := H) N) μ γ := by
  haveI : ∀ j : Fin N ⊕ Fin N, IsProbabilityMeasure
      (Sum.elim (fun _ : Fin N => μ) (fun _ : Fin N => γ) j : Measure H) := by
    intro j; cases j <;> simpa
  refine ⟨fun i => measurable_pi_apply _, fun i => measurable_pi_apply _, ?_, ?_, ?_⟩
  · have := iIndepFun_pi (μ := fun j : Fin N ⊕ Fin N =>
      (Sum.elim (fun _ : Fin N => μ) (fun _ : Fin N => γ) j : Measure H))
      (X := fun _ => (id : H → H)) (fun _ => aemeasurable_id)
    have e : (fun j : Fin N ⊕ Fin N => Sum.elim (coordY (H := H) N) (coordZ (H := H) N) j) =
        fun j ω => id (ω j) := by
      funext j; cases j <;> rfl
    rw [e]; exact this
  · intro i
    exact (measurePreserving_eval (fun j : Fin N ⊕ Fin N =>
      (Sum.elim (fun _ : Fin N => μ) (fun _ : Fin N => γ) j : Measure H)) (Sum.inl i)).map_eq
  · intro i
    exact (measurePreserving_eval (fun j : Fin N ⊕ Fin N =>
      (Sum.elim (fun _ : Fin N => μ) (fun _ : Fin N => γ) j : Measure H)) (Sum.inr i)).map_eq

lemma map_sum_eq_of_iid {W : Fin N → Ω → H} {P : Measure Ω} [IsProbabilityMeasure P]
    (hW : ∀ i, AEMeasurable (W i) P) (hind : iIndepFun W P) {ν : Measure H}
    (hlaw : ∀ i, P.map (W i) = ν) (c : ℝ) :
    P.map (fun ω => c • ∑ i, W i ω) =
      (Measure.pi fun _ : Fin N => ν).map (fun z : Fin N → H => c • ∑ i, z i) := by
  have h1 := (iIndepFun_iff_map_fun_eq_pi_map hW).1 hind
  simp_rw [hlaw] at h1
  have hm : Measurable fun z : Fin N → H => c • ∑ i, z i := by fun_prop
  rw [← h1, AEMeasurable.map_map_of_aemeasurable hm.aemeasurable (aemeasurable_pi_iff.2 hW)]
  rfl

lemma Setup.law_sumY {P : Measure Ω} [IsProbabilityMeasure P] {Y Z : Fin N → Ω → H} {μ γ : Measure H}
    (S : Setup P Y Z μ γ) (c : ℝ) :
    P.map (hyb Y Z c Finset.univ Finset.univ) =
      (Measure.pi fun _ : Fin N => μ).map (fun z : Fin N → H => c • ∑ i, z i) := by
  have hind : iIndepFun Y P :=
    iIndepFun.precomp (g := (Sum.inl : Fin N → Fin N ⊕ Fin N)) Sum.inl_injective S.indep
  have := map_sum_eq_of_iid (fun i => (S.measY i).aemeasurable) hind S.lawY c
  convert this using 2
  funext ω
  simp [hyb]

lemma Setup.law_sumZ {P : Measure Ω} [IsProbabilityMeasure P] {Y Z : Fin N → Ω → H} {μ γ : Measure H}
    (S : Setup P Y Z μ γ) (c : ℝ) :
    P.map (hyb Y Z c ∅ Finset.univ) =
      (Measure.pi fun _ : Fin N => γ).map (fun z : Fin N → H => c • ∑ i, z i) := by
  have hind : iIndepFun Z P :=
    iIndepFun.precomp (g := (Sum.inr : Fin N → Fin N ⊕ Fin N)) Sum.inr_injective S.indep
  have := map_sum_eq_of_iid (fun i => (S.measZ i).aemeasurable) hind S.lawZ c
  convert this using 2
  funext ω
  simp [hyb]

lemma lipschitz_of_fderiv {Q : H → ℝ} (hQ : Differentiable ℝ Q) {L1 : ℝ}
    (hL1 : ∀ x, ‖fderiv ℝ Q x‖ ≤ L1) (x h : H) : |Q (x + h) - Q x| ≤ L1 * ‖h‖ := by
  have := (convex_univ (𝕜 := ℝ) (E := H)).norm_image_sub_le_of_norm_fderiv_le
    (f := Q) (fun x _ => hQ x) (fun x _ => hL1 x) (Set.mem_univ x) (Set.mem_univ (x + h))
  simpa [Real.norm_eq_abs] using this

/-- Estimate for the expectation of the smooth third-moment functional along a hybrid sum. -/
lemma Q_estimate (S : Setup P Y Z μ γ) (M : Matching μ γ) {Q : H → ℝ} (hQ : ContDiff ℝ (2 + 1) Q)
    {L3 : ℝ} (hL3 : ∀ x, ‖iteratedFDeriv ℝ (2 + 1) Q x‖ ≤ L3) {B : ℝ} (hB : ∀ x, |Q x| ≤ B)
    {K2 : ℝ} (hK2 : ∀ x, ‖iteratedFDeriv ℝ 2 Q x‖ ≤ K2) {L1 : ℝ} (hL1 : ∀ x, ‖fderiv ℝ Q x‖ ≤ L1)
    {c : ℝ} (hc : 0 ≤ c) (hlaw : P.map (hyb Y Z c ∅ Finset.univ) = γ) (j : Fin N) :
    |∫ ω, Q (hyb Y Z c (pref N j) (Finset.univ.erase j) ω) ∂P - ∫ z, Q z ∂γ| ≤
      N * (L3 * c ^ (2 + 1) * ((∫ a, ‖a‖ ^ (2 + 1) ∂μ) + ∫ a, ‖a‖ ^ (2 + 1) ∂γ) / ((2 + 1)! : ℝ))
        + L1 * c * ∫ b, ‖b‖ ∂γ := by
  have hsub : pref N j ⊆ Finset.univ.erase j := by
    intro i hi
    simp only [pref, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h; subst h; omega
  have h3 := ind3 S M hQ hL3 hB hK2 hc (pref N j) (Finset.univ.erase j) hsub
  have hL3nn : 0 ≤ L3 := (norm_nonneg _).trans (hL3 0)
  have hδ : 0 ≤ L3 * c ^ (2 + 1) * ((∫ a, ‖a‖ ^ (2 + 1) ∂μ) + ∫ a, ‖a‖ ^ (2 + 1) ∂γ) / ((2 + 1)! : ℝ) := by
    have n1 : 0 ≤ ∫ a, ‖a‖ ^ (2 + 1) ∂μ := integral_nonneg fun a => by positivity
    have n2 : 0 ≤ ∫ a, ‖a‖ ^ (2 + 1) ∂γ := integral_nonneg fun a => by positivity
    positivity
  have hcard : ((pref N j).card : ℝ) ≤ N := by
    have : (pref N j).card ≤ N := by
      calc (pref N j).card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
        _ = N := by simp
    exact_mod_cast this
  have h3' := h3.trans (mul_le_mul_of_nonneg_right hcard hδ)
  -- compare `hyb ∅ (univ.erase j)` with `hyb ∅ univ`
  have hdiff : ∀ ω, hyb Y Z c ∅ Finset.univ ω =
      hyb Y Z c ∅ (Finset.univ.erase j) ω + c • Z j ω := by
    intro ω
    have := hyb_Z Y Z c (A := ∅) (I := Finset.univ) (i := j) (Finset.mem_univ _) ω
    simpa using this
  have hQd : Differentiable ℝ Q := hQ.differentiable (by norm_num)
  have hQc : Continuous Q := hQ.continuous
  have hmeasE := S.measurable_hyb' c ∅ (Finset.univ.erase j)
  have hint1 : Integrable (fun ω => Q (hyb Y Z c ∅ (Finset.univ.erase j) ω)) P :=
    Integrable.of_bound (hQc.measurable.comp hmeasE).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB _)
  have hint2 : Integrable (fun ω => Q (hyb Y Z c ∅ Finset.univ ω)) P :=
    Integrable.of_bound (hQc.measurable.comp (S.measurable_hyb' c ∅ Finset.univ)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB _)
  have hZint : Integrable (fun ω => ‖Z j ω‖) P := by
    have : Integrable (fun b : H => ‖b‖) γ := by
      simpa using M.intγ 1 (by norm_num)
    have h' : Integrable (fun b : H => ‖b‖) (P.map (Z j)) := by rw [S.lawZ j]; exact this
    exact (integrable_map_measure h'.aestronglyMeasurable (S.measZ j).aemeasurable).1 h'
  have hlip : |∫ ω, Q (hyb Y Z c ∅ Finset.univ ω) ∂P - ∫ ω, Q (hyb Y Z c ∅ (Finset.univ.erase j) ω) ∂P|
      ≤ L1 * c * ∫ b, ‖b‖ ∂γ := by
    rw [← integral_sub hint2 hint1]
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hI : ∫ ω, ‖Z j ω‖ ∂P = ∫ b, ‖b‖ ∂γ := by
      rw [← S.lawZ j, integral_map (S.measZ j).aemeasurable (by fun_prop : Continuous fun b : H => ‖b‖).aestronglyMeasurable]
    calc ∫ ω, ‖Q (hyb Y Z c ∅ Finset.univ ω) - Q (hyb Y Z c ∅ (Finset.univ.erase j) ω)‖ ∂P
        ≤ ∫ ω, L1 * c * ‖Z j ω‖ ∂P := by
          refine integral_mono (hint2.sub hint1).norm (hZint.const_mul _) fun ω => ?_
          rw [hdiff ω, Real.norm_eq_abs]
          have := lipschitz_of_fderiv hQd hL1 (hyb Y Z c ∅ (Finset.univ.erase j) ω) (c • Z j ω)
          simp only [add_sub_cancel_left] at this ⊢
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc] at this
          simpa [mul_assoc] using this
      _ = L1 * c * ∫ b, ‖b‖ ∂γ := by rw [integral_const_mul, hI]
  have hEγ : ∫ ω, Q (hyb Y Z c ∅ Finset.univ ω) ∂P = ∫ z, Q z ∂γ := by
    rw [← hlaw, integral_map (S.measurable_hyb' c ∅ Finset.univ).aemeasurable hQc.aestronglyMeasurable]
  rw [← hEγ]
  have := abs_add_le (∫ ω, Q (hyb Y Z c (pref N j) (Finset.univ.erase j) ω) ∂P -
      ∫ ω, Q (hyb Y Z c ∅ (Finset.univ.erase j) ω) ∂P)
    (∫ ω, Q (hyb Y Z c ∅ (Finset.univ.erase j) ω) ∂P - ∫ ω, Q (hyb Y Z c ∅ Finset.univ ω) ∂P)
  have e : ∫ ω, Q (hyb Y Z c (pref N j) (Finset.univ.erase j) ω) ∂P -
      ∫ ω, Q (hyb Y Z c ∅ Finset.univ ω) ∂P =
      (∫ ω, Q (hyb Y Z c (pref N j) (Finset.univ.erase j) ω) ∂P -
        ∫ ω, Q (hyb Y Z c ∅ (Finset.univ.erase j) ω) ∂P) +
      (∫ ω, Q (hyb Y Z c ∅ (Finset.univ.erase j) ω) ∂P - ∫ ω, Q (hyb Y Z c ∅ Finset.univ ω) ∂P) := by
    ring
  rw [e]
  rw [abs_sub_comm] at hlip
  linarith

/-- The smooth third-moment functional `z ↦ ⟨D³F(z), E[a^{⊗3}]⟩`. -/
def Qf (μ : Measure H) (F : H → ℝ) (z : H) : ℝ := momF μ 3 (iteratedFDeriv ℝ 3 F z)

/-- Core Lindeberg estimate. -/
lemma core (S : Setup P Y Z μ γ) (M : Matching μ γ) {c : ℝ} (hc : 0 < c) (hN : 0 < N)
    (hcN : c ^ 2 * N = 1) (hlaw : P.map (hyb Y Z c ∅ Finset.univ) = γ) {F : H → ℝ}
    (hF : ContDiff ℝ 6 F) (hFb : ∀ j ≤ 6, ∀ x, ‖iteratedFDeriv ℝ j F x‖ ≤ 1) :
    |∫ ω, F (hyb Y Z c Finset.univ Finset.univ ω) ∂P - ∫ z, F z ∂γ -
        (1 / 6) * c * ∫ z, Qf μ F z ∂γ| ≤
      (((∫ a, ‖a‖ ^ 4 ∂μ) + ∫ a, ‖a‖ ^ 4 ∂γ) / 24 +
        ((∫ a, ‖a‖ ^ 3 ∂μ) * ((∫ a, ‖a‖ ^ 3 ∂μ) + ∫ a, ‖a‖ ^ 3 ∂γ) / 6 +
          (∫ a, ‖a‖ ^ 3 ∂μ) * ∫ b, ‖b‖ ∂γ) / 6) / N := by
  have hint3 := M.intμ 3 (by norm_num)
  set Λ := momCLM μ hint3 with hΛ
  set m3 : ℝ := ∫ a, ‖a‖ ^ 3 ∂μ with hm3
  have hm3nn : 0 ≤ m3 := integral_nonneg fun a => by positivity
  have hΛn : ‖Λ‖ ≤ m3 := norm_momCLM_le μ hint3
  have hQdef : Qf μ F = fun z => Λ (iteratedFDeriv ℝ 3 F z) := rfl
  have hF' : ContDiff ℝ (3 + 3) F := by norm_num; exact hF
  have hQ : ContDiff ℝ (2 + 1) (Qf μ F) := by
    rw [hQdef]
    have := contDiff_clm_iteratedFDeriv Λ (n := 3) hF'
    norm_num; exact this
  have hQb : ∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i (Qf μ F) x‖ ≤ m3 := by
    intro i hi x
    rw [hQdef]
    refine (norm_iteratedFDeriv_clm_iteratedFDeriv Λ (n := 3) hF' hi x).trans ?_
    calc ‖Λ‖ * ‖iteratedFDeriv ℝ (i + 3) F x‖ ≤ m3 * 1 :=
          mul_le_mul hΛn (hFb _ (by omega) x) (norm_nonneg _) hm3nn
      _ = m3 := mul_one _
  have hF4 : ContDiff ℝ (3 + 1) F := by norm_num; exact hF.of_le (by norm_num)
  have h4 := ind4 S M hF4 (L := 1) (fun x => by simpa using hFb 4 (by norm_num) x) (B := 1)
    (fun x => by simpa using hFb 0 (by norm_num) x) (K := 1) (fun x => hFb 3 (by norm_num) x)
    hc.le N le_rfl
  rw [pref_self] at h4
  set m3γ : ℝ := ∫ a, ‖a‖ ^ 3 ∂γ with hm3γ
  set m4μ : ℝ := ∫ a, ‖a‖ ^ 4 ∂μ with hm4μ
  set m4γ : ℝ := ∫ a, ‖a‖ ^ 4 ∂γ with hm4γ
  set m1γ : ℝ := ∫ b, ‖b‖ ∂γ with hm1γ
  set I : ℝ := ∫ z, Qf μ F z ∂γ with hI
  have hj : ∀ j : Fin N, |∫ ω, Qf μ F (hyb Y Z c (pref N j) (Finset.univ.erase j) ω) ∂P - I| ≤
      N * (m3 * c ^ (2 + 1) * (m3 + m3γ) / ((2 + 1)! : ℝ)) + m3 * c * m1γ := by
    intro j
    exact Q_estimate S M hQ (hQb 3 le_rfl) (fun x => by simpa using hQb 0 (by norm_num) x)
      (hQb 2 (by norm_num)) (fun x => by simpa using hQb 1 (by norm_num) x) hc.le hlaw j
  have hEγ : ∫ ω, F (hyb Y Z c ∅ Finset.univ ω) ∂P = ∫ z, F z ∂γ := by
    rw [← hlaw, integral_map (S.measurable_hyb' c ∅ Finset.univ).aemeasurable
      hF.continuous.aestronglyMeasurable]
  rw [hEγ] at h4
  set X1 := ∫ ω, F (hyb Y Z c Finset.univ Finset.univ ω) ∂P with hX1
  set X0 := ∫ z, F z ∂γ with hX0
  set Tj : Fin N → ℝ := fun j =>
    ∫ ω, Qf μ F (hyb Y Z c (pref N j) (Finset.univ.erase j) ω) ∂P with hTj
  have hsumT : |∑ j : Fin N, Tj j - N * I| ≤ N * (N * (m3 * c ^ (2 + 1) * (m3 + m3γ) / ((2 + 1)! : ℝ)) +
      m3 * c * m1γ) := by
    have : ∑ j : Fin N, Tj j - N * I = ∑ j : Fin N, (Tj j - I) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j : Fin N, |Tj j - I| ≤ ∑ _j : Fin N, (N * (m3 * c ^ (2 + 1) * (m3 + m3γ) / ((2 + 1)! : ℝ)) +
          m3 * c * m1γ) := Finset.sum_le_sum fun j _ => hj j
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hc2 : c ^ 2 = 1 / (N : ℝ) := by
    have : (N : ℝ) ≠ 0 := by positivity
    field_simp; linarith
  have hq : (3 ! : ℝ)⁻¹ * c ^ 3 * (N * I) = (1 / 6) * c * I := by
    have : c ^ 3 * N = c := by
      have : c ^ 3 * N = c * (c ^ 2 * N) := by ring
      rw [this, hcN, mul_one]
    simp only [Nat.factorial]; push_cast
    linear_combination (1 / 6 * I) * this
  have h5 : |(3 ! : ℝ)⁻¹ * c ^ 3 * ∑ j : Fin N, Tj j - (1 / 6) * c * I| ≤
      (3 ! : ℝ)⁻¹ * c ^ 3 * (N * (N * (m3 * c ^ (2 + 1) * (m3 + m3γ) / ((2 + 1)! : ℝ)) +
      m3 * c * m1γ)) := by
    rw [← hq, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (3 ! : ℝ)⁻¹ * c ^ 3)]
    exact mul_le_mul_of_nonneg_left hsumT (by positivity)
  have h6 := abs_add_le (X1 - X0 - (3 ! : ℝ)⁻¹ * c ^ 3 * ∑ j : Fin N, Tj j)
    ((3 ! : ℝ)⁻¹ * c ^ 3 * ∑ j : Fin N, Tj j - (1 / 6) * c * I)
  have e : X1 - X0 - (1 / 6) * c * I = (X1 - X0 - (3 ! : ℝ)⁻¹ * c ^ 3 * ∑ j : Fin N, Tj j) +
      ((3 ! : ℝ)⁻¹ * c ^ 3 * ∑ j : Fin N, Tj j - (1 / 6) * c * I) := by ring
  rw [e]
  refine h6.trans ?_
  -- numeric identity
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hc4 : c ^ 4 = (1 / (N:ℝ)) ^ 2 := by rw [← hc2]; ring
  have hc6 : c ^ 6 = (1 / (N:ℝ)) ^ 3 := by rw [← hc2]; ring
  have hnum : (N:ℝ) * (1 * c ^ (3 + 1) * (m4μ + m4γ) / ((3 + 1)! : ℝ)) +
      (3 ! : ℝ)⁻¹ * c ^ 3 * (N * (N * (m3 * c ^ (2 + 1) * (m3 + m3γ) / ((2 + 1)! : ℝ)) +
      m3 * c * m1γ)) =
      ((m4μ + m4γ) / 24 + (m3 * (m3 + m3γ) / 6 + m3 * m1γ) / 6) / N := by
    have e1 : c ^ (3 + 1) = c ^ 4 := rfl
    have e2 : c ^ (2 + 1) = c ^ 3 := rfl
    have hlhs : (N:ℝ) * (1 * c ^ (3 + 1) * (m4μ + m4γ) / ((3 + 1)! : ℝ)) +
        (3 ! : ℝ)⁻¹ * c ^ 3 * (N * (N * (m3 * c ^ (2 + 1) * (m3 + m3γ) / ((2 + 1)! : ℝ)) +
        m3 * c * m1γ)) = (N * c ^ 4 * (m4μ + m4γ)) / 24 +
          (N ^ 2 * c ^ 6 * m3 * (m3 + m3γ)) / 36 + (N * c ^ 4 * m3 * m1γ) / 6 := by
      simp only [e1, e2, Nat.factorial]; push_cast; ring
    rw [hlhs, hc4, hc6]
    field_simp
    ring
  refine (add_le_add h4 h5).trans (le_of_eq ?_)
  rw [← hnum]

end Hybrid

section Glue

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma momF_zero_eq (μ : Measure H) [IsProbabilityMeasure μ] (m : H [×0]→L[ℝ] ℝ) :
    momF μ 0 m = m 0 := by
  have : ∀ a : H, m (fun _ => a) = m 0 := fun a => by congr 1; ext i; exact i.elim0
  simp [momF, this]

lemma momF_one_eq_zero (μ : Measure H) (hint : Integrable (fun a : H => ‖a‖) μ)
    (h0 : ∫ a, a ∂μ = 0) (m : H [×1]→L[ℝ] ℝ) : momF μ 1 m = 0 := by
  have hid : Integrable (fun a : H => a) μ := by
    refine ⟨aestronglyMeasurable_id, ?_⟩
    simpa [HasFiniteIntegral] using hint.2
  have e : ∀ a : H, m (fun _ => a) = (continuousMultilinearCurryFin1 ℝ H ℝ m) a := fun a => by
    rw [continuousMultilinearCurryFin1_apply]; congr 1
  simp_rw [momF, e]
  rw [ContinuousLinearMap.integral_comp_comm _ hid, h0, map_zero]

/-- The diagonal of a continuous bilinear form associated with a 2-linear map. -/
def biOf (m : H [×2]→L[ℝ] ℝ) : H →L[ℝ] H →L[ℝ] ℝ :=
  (continuousMultilinearCurryFin1 ℝ H ℝ : (H [×1]→L[ℝ] ℝ) →L[ℝ] (H →L[ℝ] ℝ)).comp
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => H) ℝ m)

lemma biOf_apply (m : H [×2]→L[ℝ] ℝ) (a : H) : biOf m a a = m (fun _ => a) := by
  simp [biOf, continuousMultilinearCurryFin1_apply]
  congr 1
  ext i; fin_cases i <;> rfl

lemma integrable_pow_le_four {μ : Measure H} [IsFiniteMeasure μ]
    (h4 : Integrable (fun a : H => ‖a‖ ^ 4) μ) {j : ℕ} (hj : j ≤ 4) :
    Integrable (fun a : H => ‖a‖ ^ j) μ := by
  refine Integrable.mono' ((integrable_const (1:ℝ)).add h4)
    (by fun_prop : Continuous fun a : H => ‖a‖ ^ j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h0 : 0 ≤ ‖a‖ := norm_nonneg a
  by_cases h1 : ‖a‖ ≤ 1
  · have : ‖a‖ ^ j ≤ 1 := pow_le_one₀ h0 h1
    have : 0 ≤ ‖a‖ ^ 4 := by positivity
    simp only [Pi.add_apply]; linarith
  · push_neg at h1
    have : ‖a‖ ^ j ≤ ‖a‖ ^ 4 := pow_le_pow_right₀ h1.le hj
    simp only [Pi.add_apply]; linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma prob_map {X : Ω → H} (hX : AEMeasurable X P) : IsProbabilityMeasure (P.map X) :=
  (Measure.isProbabilityMeasure_map_iff hX).2 inferInstance

lemma integrable_map_pow {X : Ω → H} (hX : AEMeasurable X P)
    (h4 : Integrable (fun ω => ‖X ω‖ ^ 4) P) : Integrable (fun a : H => ‖a‖ ^ 4) (P.map X) := by
  have := prob_map hX
  refine (integrable_map_measure (by fun_prop : Continuous fun a : H => ‖a‖ ^ 4).aestronglyMeasurable hX).2 ?_
  exact h4

lemma cov_form_eq {X G : Ω → H} (hX : AEMeasurable X P) (hcent : ∫ ω, X ω ∂P = 0)
    (h4 : Integrable (fun ω => ‖X ω‖ ^ 4) P) (hG : IsCenteredGaussianRV P G
      (fun x y => ProbabilityTheory.covarianceBilin (law P X) x y)) (x y : H) :
    ∫ a, inner ℝ x a * inner ℝ y a ∂(P.map X) = ∫ b, inner ℝ x b * inner ℝ y b ∂(P.map G) := by
  haveI := prob_map hX
  haveI := prob_map hG.1
  haveI := hG.2.1.1
  have hint4 := integrable_map_pow hX h4
  have hint2 : Integrable (fun a : H => ‖a‖ ^ 2) (P.map X) := integrable_pow_le_four hint4 (by norm_num)
  have hmean : ∫ a, a ∂(P.map X) = 0 := by
    have h : ∫ a, id a ∂(P.map X) = ∫ ω, id (X ω) ∂P := integral_map hX aestronglyMeasurable_id
    simpa using h.trans hcent
  have hmem1 : MemLp id 2 (P.map X) :=
    (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).2 hint2
  have hmem2 : MemLp id 2 (P.map G) := ProbabilityTheory.IsGaussian.memLp_two_id
  have hmean2 : ∫ a, a ∂(P.map G) = 0 := by
    simpa using gaussian_integral_id_eq_zero hG.2.1
  have h1 := ProbabilityTheory.covarianceBilin_apply hmem1 x y
  have h2 := ProbabilityTheory.covarianceBilin_apply hmem2 x y
  have h3 := hG.2.2 x y
  simp only [id_eq, hmean, hmean2, sub_zero] at h1 h2
  rw [← h1, ← h2, h3]

/-- The data of Lemma 7.1 yields the moment matching. -/
lemma matching_of_data {X G : Ω → H} (hX : AEMeasurable X P) (hcent : ∫ ω, X ω ∂P = 0)
    (h4 : Integrable (fun ω => ‖X ω‖ ^ 4) P) (hG : IsCenteredGaussianRV P G
      (fun x y => ProbabilityTheory.covarianceBilin (law P X) x y)) :
    Matching (P.map X) (P.map G) := by
  haveI := prob_map hX
  haveI := prob_map hG.1
  have hint4 := integrable_map_pow hX h4
  have hmean : ∫ a, a ∂(P.map X) = 0 := by
    have h : ∫ a, id a ∂(P.map X) = ∫ ω, id (X ω) ∂P := integral_map hX aestronglyMeasurable_id
    simpa using h.trans hcent
  have hmean2 : ∫ a, a ∂(P.map G) = 0 := by
    simpa using gaussian_integral_id_eq_zero hG.2.1
  have hintγ : ∀ j, Integrable (fun a : H => ‖a‖ ^ j) (P.map G) := gaussian_integrable_pow hG.2.1
  have hint1 : Integrable (fun a : H => ‖a‖) (P.map X) := by
    simpa using integrable_pow_le_four hint4 (j := 1) (by norm_num)
  refine ⟨fun j hj => integrable_pow_le_four hint4 hj, fun j _ => hintγ j, ?_, ?_, ?_, ?_, ?_, hmean, hmean2⟩
  · intro m; rw [momF_zero_eq, momF_zero_eq]
  · intro m
    rw [momF_one_eq_zero _ hint1 hmean, momF_one_eq_zero _ (by simpa using hintγ 1) hmean2]
  · intro m
    have hcov := cov_form_eq hX hcent h4 hG
    have := integral_diag_bilinear_eq (integrable_pow_le_four hint4 (j := 2) (by norm_num))
      (hintγ 2) hcov (biOf m)
    simpa [momF, biOf_apply] using this
  · intro m
    exact momF_gaussian_odd hG.2.1 (by decide) m
  · intro B
    exact integral_diag_bilinear_eq (integrable_pow_le_four hint4 (j := 2) (by norm_num))
      (hintγ 2) (cov_form_eq hX hcent h4 hG) B

lemma second_moment_eq {X G : Ω → H} (hX : AEMeasurable X P) (hcent : ∫ ω, X ω ∂P = 0)
    (h4 : Integrable (fun ω => ‖X ω‖ ^ 4) P) (hG : IsCenteredGaussianRV P G
      (fun x y => ProbabilityTheory.covarianceBilin (law P X) x y)) :
    ∫ b, ‖b‖ ^ 2 ∂(P.map G) = ∫ a, ‖a‖ ^ 2 ∂(P.map X) := by
  haveI := prob_map hX
  haveI := prob_map hG.1
  have hint4 := integrable_map_pow hX h4
  have hcov := cov_form_eq hX hcent h4 hG
  have := integral_diag_bilinear_eq (integrable_pow_le_four hint4 (j := 2) (by norm_num))
    (gaussian_integrable_pow hG.2.1 2) hcov (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ)
  have e : ∀ a : H, (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ) a a = ‖a‖ ^ 2 := fun a => by
    simp [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  simp_rw [e] at this
  exact this.symm

lemma pairing_eq {F : H → ℝ} (hF : ContDiff ℝ 3 F) {K : ℝ} (hK : ∀ x, ‖iteratedFDeriv ℝ 3 F x‖ ≤ K)
    {X G : Ω → H} (hX : AEMeasurable X P) (hG : AEMeasurable G P)
    (h3 : Integrable (fun ω => ‖X ω‖ ^ 3) P) :
    thirdMomentPairing P F G X = ∫ z, Qf (P.map X) F z ∂(P.map G) := by
  haveI := prob_map hX
  haveI := prob_map hG
  have hD : Continuous (iteratedFDeriv ℝ 3 F) := hF.continuous_iteratedFDeriv le_rfl
  have hΦ : Continuous fun q : H × H => iteratedFDeriv ℝ 3 F q.1 (fun _ => q.2) := by
    have : Continuous fun p : (H [×3]→L[ℝ] ℝ) × H => p.1 (fun _ => p.2) := by fun_prop
    exact this.comp (hD.comp continuous_fst |>.prodMk continuous_snd)
  have hvec : ∀ x : H, (![x, x, x] : Fin 3 → H) = fun _ => x := by
    intro x; ext i; fin_cases i <;> rfl
  have hint : Integrable (fun p : Ω × Ω => iteratedFDeriv ℝ 3 F (G p.1) (fun _ => X p.2)) (P.prod P) := by
    have hm : AEMeasurable (fun p : Ω × Ω => (G p.1, X p.2)) (P.prod P) :=
      (hG.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk
        (hX.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    refine Integrable.mono' ((h3.comp_snd P).const_mul K)
      (hΦ.measurable.comp_aemeasurable hm).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    exact (norm_apply_diag_le _ _).trans (mul_le_mul_of_nonneg_right (hK _) (by positivity))
  unfold thirdMomentPairing
  simp_rw [hvec]
  rw [integral_prod _ hint]
  have h1 : ∀ x : Ω, ∫ y, iteratedFDeriv ℝ 3 F (G x) (fun _ => X y) ∂P =
      Qf (P.map X) F (G x) := by
    intro x
    unfold Qf momF
    rw [integral_map hX (by exact (continuous_apply_diag _).aestronglyMeasurable)]
  simp_rw [h1]
  rw [integral_map hG (by
    have hint3 : Integrable (fun a : H => ‖a‖ ^ 3) (P.map X) :=
      (integrable_map_measure (by fun_prop : Continuous fun a : H => ‖a‖ ^ 3).aestronglyMeasurable hX).2 h3
    have : Continuous (Qf (P.map X) F) := (momCLM (P.map X) hint3).continuous.comp hD
    exact this.aestronglyMeasurable)]

lemma unit_ball_bound {k : ℕ} {F : H → ℝ} (hF : F ∈ CbUnitBall H k) :
    ContDiff ℝ k F ∧ ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j F x‖ ≤ 1 := by
  obtain ⟨hd, hb, hn⟩ := hF
  refine ⟨hd, fun j hj x => ?_⟩
  have hnn : ∀ i ∈ Finset.range (k + 1), 0 ≤ ⨆ z : H, ‖iteratedFDeriv ℝ i F z‖ :=
    fun i _ => Real.iSup_nonneg fun z => norm_nonneg _
  have h1 : (⨆ z : H, ‖iteratedFDeriv ℝ j F z‖) ≤ ∑ i ∈ Finset.range (k + 1), ⨆ z : H, ‖iteratedFDeriv ℝ i F z‖ :=
    Finset.single_le_sum hnn (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  have h2 : ‖iteratedFDeriv ℝ j F x‖ ≤ ⨆ z : H, ‖iteratedFDeriv ℝ j F z‖ :=
    le_ciSup (hb j hj) x
  exact h2.trans (h1.trans hn)

lemma integrable_norm_pow_le_four {X : Ω → H} (hX : AEMeasurable X P)
    (h4 : Integrable (fun ω => ‖X ω‖ ^ 4) P) {j : ℕ} (hj : j ≤ 4) :
    Integrable (fun ω => ‖X ω‖ ^ j) P := by
  refine Integrable.mono' ((integrable_const (1:ℝ)).add h4)
    ((hX.norm.pow_const j).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h0 : 0 ≤ ‖X ω‖ := norm_nonneg _
  by_cases h1 : ‖X ω‖ ≤ 1
  · have : ‖X ω‖ ^ j ≤ 1 := pow_le_one₀ h0 h1
    have : 0 ≤ ‖X ω‖ ^ 4 := by positivity
    simp only [Pi.add_apply]; linarith
  · push_neg at h1
    have : ‖X ω‖ ^ j ≤ ‖X ω‖ ^ 4 := pow_le_pow_right₀ h1.le hj
    simp only [Pi.add_apply]; linarith

/-- The explicit constant of the `C_b^6` form. -/
def c6const (a b c : ℝ) : ℝ :=
  (c + 3 * a ^ 2) / 24 + (b * (b + (a + 3 * a ^ 2) / 2) / 6 + b * (1 + a) / 2) / 6

set_option maxHeartbeats 1600000 in
lemma c6_core {N : ℕ} (hN : 1 ≤ N) {X₀ : Ω → H} (hmeas₀ : AEMeasurable X₀ P)
    (hcent : ∫ ω, X₀ ω ∂P = 0) (h4 : Integrable (fun ω => ‖X₀ ω‖ ^ 4) P)
    {X : Fin N → Ω → H} (hind : iIndepFun X P) (hmeas : ∀ i, AEMeasurable (X i) P)
    (hlaw : ∀ i, P.map (X i) = P.map X₀) {G : Ω → H}
    (hG : IsCenteredGaussianRV P G (fun x y => ProbabilityTheory.covarianceBilin (law P X₀) x y))
    {F : H → ℝ} (hF : F ∈ CbUnitBall H 6) :
    |∫ ω, F ((Real.sqrt N)⁻¹ • ∑ i, X i ω) ∂P - ∫ ω, F (G ω) ∂P -
        (1 / (6 * Real.sqrt N)) * thirdMomentPairing P F G X₀| ≤
      c6const (∫ ω, ‖X₀ ω‖ ^ 2 ∂P) (∫ ω, ‖X₀ ω‖ ^ 3 ∂P) (∫ ω, ‖X₀ ω‖ ^ 4 ∂P) / N := by
  obtain ⟨hF6, hFb⟩ := unit_ball_bound hF
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  set μ := P.map X₀ with hμ
  set γ := P.map G with hγ
  haveI := prob_map hmeas₀
  haveI := prob_map hG.1
  have M := matching_of_data hmeas₀ hcent h4 hG
  set c : ℝ := (Real.sqrt N)⁻¹ with hc
  have hsq : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hcpos : 0 < c := inv_pos.2 hsq
  have hcN : c ^ 2 * N = 1 := by
    rw [hc, inv_pow, Real.sq_sqrt hNpos.le]; field_simp
  have S := setup_prod N μ γ
  -- the Gaussian endpoint
  have hlawZ : (prodMeasure N μ γ).map (hyb (coordY (H := H) N)
      (coordZ (H := H) N) c ∅ Finset.univ) = γ := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [S.law_sumZ c]
    have := gaussian_stable hG.2.1 n
    simpa [hc] using this
  have hcore := core S M hcpos (by omega) hcN hlawZ hF6 hFb
  -- transfer the main term to `P`
  have hX1 : ∫ ω, F (c • ∑ i, X i ω) ∂P =
      ∫ ω, F (hyb (coordY (H := H) N)
      (coordZ (H := H) N) c Finset.univ Finset.univ ω)
        ∂(prodMeasure N μ γ) := by
    have h1 := map_sum_eq_of_iid hmeas hind hlaw c
    have h2 := S.law_sumY c
    have hm : Measurable fun z : Fin N → H => c • ∑ i, z i := by fun_prop
    have e1 : ∫ ω, F (c • ∑ i, X i ω) ∂P = ∫ z, F z ∂(P.map fun ω => c • ∑ i, X i ω) := by
      rw [integral_map (aemeasurable_pi_iff.2 hmeas |> fun h => by
        exact (hm.comp_aemeasurable h)) hF6.continuous.aestronglyMeasurable]
    have e2 : ∫ ω, F (hyb (coordY (H := H) N)
      (coordZ (H := H) N) c Finset.univ Finset.univ ω)
        ∂(prodMeasure N μ γ) =
        ∫ z, F z ∂((prodMeasure N μ γ).map (hyb (coordY (H := H) N)
      (coordZ (H := H) N) c Finset.univ Finset.univ)) := by
      rw [integral_map (S.measurable_hyb' c _ _).aemeasurable hF6.continuous.aestronglyMeasurable]
    rw [e1, e2, h1, h2]
  have hEG : ∫ ω, F (G ω) ∂P = ∫ z, F z ∂γ := by
    rw [hγ, integral_map hG.1 hF6.continuous.aestronglyMeasurable]
  have h3 : Integrable (fun ω => ‖X₀ ω‖ ^ 3) P := integrable_norm_pow_le_four hmeas₀ h4 (by norm_num)
  have hF3 : ContDiff ℝ 3 F := hF6.of_le (by norm_num)
  have hpair := pairing_eq (P := P) hF3 (K := 1)
    (fun x => hFb 3 (by norm_num) x) hmeas₀ hG.1 h3
  -- moments
  have hmom : ∀ j : ℕ, ∫ a, ‖a‖ ^ j ∂μ = ∫ ω, ‖X₀ ω‖ ^ j ∂P := fun j => by
    rw [hμ, integral_map hmeas₀ (by fun_prop : Continuous fun a : H => ‖a‖ ^ j).aestronglyMeasurable]
  have hm2 : ∫ b, ‖b‖ ^ 2 ∂γ = ∫ ω, ‖X₀ ω‖ ^ 2 ∂P := by
    rw [hγ, second_moment_eq hmeas₀ hcent h4 hG, ← hmom 2]
  have hm4 : ∫ b, ‖b‖ ^ 4 ∂γ ≤ 3 * (∫ ω, ‖X₀ ω‖ ^ 2 ∂P) ^ 2 := by
    rw [← hm2]; exact gaussian_fourth_le hG.2.1
  have hm3 : ∫ b, ‖b‖ ^ 3 ∂γ ≤ ((∫ ω, ‖X₀ ω‖ ^ 2 ∂P) + 3 * (∫ ω, ‖X₀ ω‖ ^ 2 ∂P) ^ 2) / 2 := by
    have hle : ∫ b, ‖b‖ ^ 3 ∂γ ≤ ∫ b, ((‖b‖ ^ 2 + ‖b‖ ^ 4) / 2) ∂γ := by
      refine integral_mono (gaussian_integrable_pow hG.2.1 3)
        (((gaussian_integrable_pow hG.2.1 2).add (gaussian_integrable_pow hG.2.1 4)).div_const 2) ?_
      intro b
      simp only
      nlinarith [sq_nonneg (‖b‖ * (1 - ‖b‖)), norm_nonneg b]
    rw [integral_div, integral_add (gaussian_integrable_pow hG.2.1 2) (gaussian_integrable_pow hG.2.1 4), hm2] at hle
    linarith
  have hm1 : ∫ b, ‖b‖ ∂γ ≤ (1 + ∫ ω, ‖X₀ ω‖ ^ 2 ∂P) / 2 := by
    have hle : ∫ b, ‖b‖ ∂γ ≤ ∫ b, ((1 + ‖b‖ ^ 2) / 2) ∂γ := by
      refine integral_mono (by simpa using gaussian_integrable_pow hG.2.1 1)
        (((integrable_const (1:ℝ)).add (gaussian_integrable_pow hG.2.1 2)).div_const 2) ?_
      intro b
      simp only
      nlinarith [sq_nonneg (‖b‖ - 1)]
    rw [integral_div, integral_add (integrable_const _) (gaussian_integrable_pow hG.2.1 2), hm2] at hle
    simpa using hle
  have hm3nn : 0 ≤ ∫ a, ‖a‖ ^ 3 ∂μ := integral_nonneg fun a => by positivity
  -- assemble
  have hcc : 1 / (6 * Real.sqrt N) = (1 / 6) * c := by rw [hc]; field_simp
  rw [hX1, hEG, hpair, hcc]
  refine hcore.trans ?_
  rw [hmom 4, hmom 3] at *
  refine div_le_div_of_nonneg_right ?_ hNpos.le
  unfold c6const
  have hm3' := hm3nn
  nlinarith [mul_le_mul_of_nonneg_left hm3 hm3', mul_le_mul_of_nonneg_left hm1 hm3', hm4]

end Glue

end EdgeAux

end HRS
