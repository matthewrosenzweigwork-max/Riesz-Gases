import HRS.Prob.HilbertCLT

/-!
# U10a core: the centered Gaussian measure with covariance `2q ∫ ∑_j k_j ⊗ k_j dμ`

Abstract Hilbert-space core of `limit_field_rd_gaussian` (S.B.7(ii)).  For a finite measure `μ`
on a measurable space `α`, a finite family of measurable, a.e. bounded maps `k_j : α → H` into a
separable real Hilbert space and `q ≥ 0`, the form
`Q(u,v) = 2q ∫ ∑_j ⟨k_j,u⟩⟨k_j,v⟩ dμ` is a trace-class covariance, and the centered Gaussian measure `ν`
with covariance `Q` has `E‖G‖² = 2q ∫ ∑_j ‖k_j‖² dμ`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HRS.MS.U10

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {α : Type*} [MeasurableSpace α] {J : Type*} [Fintype J]

/-- The integrand `∑_j ⟨k_j(a),u⟩⟨k_j(a),v⟩`. -/
def u10_S (k : α → J → H) (u v : H) (a : α) : ℝ :=
  ∑ j, inner ℝ (k a j) u * inner ℝ (k a j) v

structure U10Data (μ : Measure α) (k : α → J → H) (B : ℝ) : Prop where
  meas : ∀ j, Measurable fun a => k a j
  bound : ∀ᵐ a ∂μ, ∀ j, ‖k a j‖ ≤ B

lemma u10_S_add_left (k : α → J → H) (u u' v : H) (a : α) :
    u10_S k (u + u') v a = u10_S k u v a + u10_S k u' v a := by
  simp only [u10_S, inner_add_right, add_mul, Finset.sum_add_distrib]

lemma u10_S_smul_left (k : α → J → H) (c : ℝ) (u v : H) (a : α) :
    u10_S k (c • u) v a = c * u10_S k u v a := by
  simp only [u10_S, inner_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

lemma u10_S_comm (k : α → J → H) (u v : H) (a : α) : u10_S k u v a = u10_S k v u a := by
  simp only [u10_S]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma u10_S_self_nonneg (k : α → J → H) (u : H) (a : α) : 0 ≤ u10_S k u u a :=
  Finset.sum_nonneg fun j _ => mul_self_nonneg _

lemma u10_S_measurable {μ : Measure α} {k : α → J → H} {B : ℝ} (hk : U10Data μ k B) (u v : H) :
    Measurable (u10_S k u v) := by
  unfold u10_S
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((hk.meas j).inner measurable_const).mul ((hk.meas j).inner measurable_const)

lemma u10_S_bound_pt {k : α → J → H} {B : ℝ} {a : α} (ha : ∀ j, ‖k a j‖ ≤ B) (u v : H) :
    ‖u10_S k u v a‖ ≤ Fintype.card J * (B ^ 2 * ‖u‖ * ‖v‖) := by
  unfold u10_S
  refine (norm_sum_le _ _).trans ?_
  have : ∀ j, ‖inner ℝ (k a j) u * inner ℝ (k a j) v‖ ≤ B ^ 2 * ‖u‖ * ‖v‖ := by
    intro j
    rw [norm_mul]
    have h1 : ‖inner ℝ (k a j) u‖ ≤ B * ‖u‖ :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (ha j) (norm_nonneg _))
    have h2 : ‖inner ℝ (k a j) v‖ ≤ B * ‖v‖ :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (ha j) (norm_nonneg _))
    calc ‖inner ℝ (k a j) u‖ * ‖inner ℝ (k a j) v‖ ≤ (B * ‖u‖) * (B * ‖v‖) :=
          mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = B ^ 2 * ‖u‖ * ‖v‖ := by ring
  calc ∑ j, ‖inner ℝ (k a j) u * inner ℝ (k a j) v‖ ≤ ∑ _j : J, B ^ 2 * ‖u‖ * ‖v‖ :=
        Finset.sum_le_sum fun j _ => this j
    _ = Fintype.card J * (B ^ 2 * ‖u‖ * ‖v‖) := by simp

lemma u10_S_bound {μ : Measure α} {k : α → J → H} {B : ℝ} (hk : U10Data μ k B) (u v : H) :
    ∀ᵐ a ∂μ, ‖u10_S k u v a‖ ≤ Fintype.card J * (B ^ 2 * ‖u‖ * ‖v‖) := by
  filter_upwards [hk.bound] with a ha using u10_S_bound_pt ha u v

lemma u10_S_integrable {μ : Measure α} [IsFiniteMeasure μ] {k : α → J → H} {B : ℝ}
    (hk : U10Data μ k B) (u v : H) : Integrable (u10_S k u v) μ :=
  Integrable.of_bound (u10_S_measurable hk u v).aestronglyMeasurable _ (u10_S_bound hk u v)

/-- The covariance form `Q(u,v) = 2q ∫ ∑_j ⟨k_j,u⟩⟨k_j,v⟩ dμ` as a continuous bilinear form. -/
def u10_Q (μ : Measure α) [IsFiniteMeasure μ] (k : α → J → H) (B q : ℝ) (hk : U10Data μ k B) :
    H →L[ℝ] H →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun u v => 2 * q * ∫ a, u10_S k u v a ∂μ)
      (fun u u' v => by
        simp only [u10_S_add_left]
        rw [integral_add (u10_S_integrable hk u v) (u10_S_integrable hk u' v)]; ring)
      (fun c u v => by
        simp only [u10_S_smul_left]
        rw [integral_const_mul]; simp only [smul_eq_mul]; ring)
      (fun u v v' => by
        simp only [u10_S_comm k u]
        simp only [u10_S_add_left]
        rw [integral_add (u10_S_integrable hk v u) (u10_S_integrable hk v' u)]; ring)
      (fun c u v => by
        simp only [u10_S_comm k u]
        simp only [u10_S_smul_left]
        rw [integral_const_mul]; simp only [smul_eq_mul]; ring))
    (|2 * q| * (Fintype.card J * B ^ 2) * μ.real Set.univ)
    (fun u v => by
      simp only [LinearMap.mk₂_apply]
      rw [norm_mul, Real.norm_eq_abs]
      have h := norm_integral_le_of_norm_le_const (μ := μ) (u10_S_bound hk u v)
      calc |2 * q| * ‖∫ a, u10_S k u v a ∂μ‖
          ≤ |2 * q| * (Fintype.card J * (B ^ 2 * ‖u‖ * ‖v‖) * μ.real Set.univ) :=
            mul_le_mul_of_nonneg_left h (abs_nonneg _)
        _ = |2 * q| * (Fintype.card J * B ^ 2) * μ.real Set.univ * ‖u‖ * ‖v‖ := by ring)

lemma u10_Q_apply (μ : Measure α) [IsFiniteMeasure μ] (k : α → J → H) (B q : ℝ)
    (hk : U10Data μ k B) (u v : H) :
    u10_Q μ k B q hk u v = 2 * q * ∫ a, u10_S k u v a ∂μ := by
  simp [u10_Q]

/-- Parseval, integrated: `∑_i ∫ ∑_j ⟨k_j,b_i⟩² = ∫ ∑_j ‖k_j‖²`. -/
lemma u10_hasSum_trace {μ : Measure α} [IsFiniteMeasure μ] {k : α → J → H} {B : ℝ}
    (hk : U10Data μ k B) {ι : Type} [Countable ι] (b : HilbertBasis ι ℝ H) :
    HasSum (fun i => ∫ a, u10_S k (b i) (b i) a ∂μ) (∫ a, ∑ j, ‖k a j‖ ^ 2 ∂μ) := by
  have hint : ∀ i, Integrable (u10_S k (b i) (b i)) μ := fun i => u10_S_integrable hk _ _
  have hnn : ∀ i a, 0 ≤ u10_S k (b i) (b i) a := fun i a => u10_S_self_nonneg k _ a
  have hTint : Integrable (fun a => ∑ j, ‖k a j‖ ^ 2) μ := by
    refine Integrable.of_bound
      (Finset.measurable_sum _ fun j _ => ((hk.meas j).norm.pow_const 2)).aestronglyMeasurable
      (Fintype.card J * B ^ 2) ?_
    filter_upwards [hk.bound] with a ha
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    calc ∑ j, ‖k a j‖ ^ 2 ≤ ∑ _j : J, B ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (ha j) 2
      _ = Fintype.card J * B ^ 2 := by simp
  -- pointwise Parseval
  have hpar : ∀ a, HasSum (fun i => u10_S k (b i) (b i) a) (∑ j, ‖k a j‖ ^ 2) := by
    intro a
    unfold u10_S
    refine hasSum_sum (s := Finset.univ)
      (f := fun j i => inner ℝ (k a j) (b i) * inner ℝ (k a j) (b i))
      (a := fun j => ‖k a j‖ ^ 2) (fun j _ => ?_)
    have h := b.hasSum_inner_mul_inner (k a j) (k a j)
    rw [real_inner_self_eq_norm_sq] at h
    simpa only [real_inner_comm (k a j)] using h
  have hsum : Summable (fun i => ∫ a, u10_S k (b i) (b i) a ∂μ) := by
    refine summable_of_sum_le (c := ∫ a, ∑ j, ‖k a j‖ ^ 2 ∂μ)
      (fun i => integral_nonneg (hnn i)) fun s => ?_
    rw [← integral_finset_sum _ (fun i _ => hint i)]
    refine integral_mono (integrable_finset_sum _ fun i _ => hint i) hTint ?_
    intro a
    simp only [u10_S]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun j _ => ?_
    have := (b.orthonormal).sum_inner_products_le (k a j) (s := s)
    simpa [Real.norm_eq_abs, sq_abs, real_inner_comm, sq] using this
  have hnorm : (fun i => ∫ a, ‖u10_S k (b i) (b i) a‖ ∂μ) =
      fun i => ∫ a, u10_S k (b i) (b i) a ∂μ := by
    funext i
    exact integral_congr_ae (ae_of_all _ fun a => Real.norm_of_nonneg (hnn i a))
  have h2 := hasSum_integral_of_summable_integral_norm hint (by rw [hnorm]; exact hsum)
  have e : (fun a => ∑' i, u10_S k (b i) (b i) a) = fun a => ∑ j, ‖k a j‖ ^ 2 :=
    funext fun a => (hpar a).tsum_eq
  rw [e] at h2
  exact h2

/-- The core: the centered Gaussian measure with covariance `2q ∫ ∑_j k_j ⊗ k_j dμ`. -/
theorem u10_core (μ : Measure α) [IsFiniteMeasure μ] (k : α → J → H) (B : ℝ)
    (hk : U10Data μ k B) (q : ℝ) (hq : 0 ≤ q) :
    ∃ ν : Measure H, IsProbabilityMeasure ν ∧ HRS.IsCenteredGaussian ν ∧
      ∫⁻ x, ‖x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (2 * q * ∫ a, ∑ j, ‖k a j‖ ^ 2 ∂μ) ∧
      ∀ u v : H, ∫ x, inner ℝ u x * inner ℝ v x ∂ν = 2 * q * ∫ a, u10_S k u v a ∂μ := by
  obtain ⟨ι, hc, b, -⟩ := HRS.HilbertCLTAux.exists_hilbertBasis_type (H := H)
  have hTC : HRS.IsTraceClassCov (u10_Q μ k B q hk) := by
    refine ⟨?_, ?_, ⟨ι, b, ?_⟩⟩
    · intro x y
      rw [u10_Q_apply, u10_Q_apply, show u10_S k x y = u10_S k y x from funext (u10_S_comm k x y)]
    · intro x
      rw [u10_Q_apply]
      exact mul_nonneg (by linarith) (integral_nonneg fun a => u10_S_self_nonneg k x a)
    · have := ((u10_hasSum_trace hk b).mul_left (2 * q)).summable
      simpa only [u10_Q_apply] using this
  obtain ⟨ν, hν, hcg, hcov⟩ := HRS.exists_centeredGaussian_of_traceClass _ hTC
  have hg := hcg.1
  have hmean := HRS.HilbertCLTAux.gaussian_mean_zero hcg
  have h1 := HRS.HilbertCLTAux.hasSum_cov_basis ν id IsGaussian.memLp_two_id hmean b
  have e : HRS.law ν id = ν := Measure.map_id
  rw [e] at h1
  simp_rw [hcov, u10_Q_apply] at h1
  have h3 := (u10_hasSum_trace hk b).mul_left (2 * q)
  have h4 : ∫ x, ‖x‖ ^ 2 ∂ν = 2 * q * ∫ a, ∑ j, ‖k a j‖ ^ 2 ∂μ := h1.unique h3
  refine ⟨ν, hν, hcg, ?_, ?_⟩
  · have hint : Integrable (fun x : H => ‖x‖ ^ 2) ν :=
      (IsGaussian.memLp_two_id).integrable_norm_pow (p := 2) (by norm_num)
    rw [← h4]
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => sq_nonneg _)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  · intro u v
    rw [← u10_Q_apply μ k B q hk u v, ← hcov u v,
      covarianceBilin_apply IsGaussian.memLp_two_id u v, hmean]
    simp

end HRS.MS.U10
