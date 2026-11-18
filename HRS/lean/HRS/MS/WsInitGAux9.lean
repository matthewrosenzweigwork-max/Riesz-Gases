import HRS.MS.WsInitGAux8
import HRS.MS.QsfAux3

/-!
# S21 packet G, part 9: the covariance of a centred Gaussian `γ` on `ℓ²` on infinite combinations

`s21g_cov`: let `γ` be a centred Gaussian on `SeqL2 = ℓ²` with `E[z_i z_j] = HRS.Whole.susceptibilityCov (φ_i, φ_j)` for a summable `C_b^J` family `φ`.
If `a, a' ∈ ℓ²` and `ψ = ∑_j a_j φ_j`, `ψ' = ∑_j a'_j φ_j` pointwise (both in `L²(ν)`), then
`E[⟨a,z⟩⟨a',z⟩] = HRS.Whole.susceptibilityCov (ψ, ψ')`.  Proof: the covariance form of `γ` and `⟪T a, R T a'⟫` (`S45.s45_C`) are bounded bilinear forms agreeing on the
standard basis; `T a = P_ν ψ` by `L²` convergence of the partial sums.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S21

open HRS HRS.Whole

variable {d : ℕ} {ν : Measure (Euc d)} [IsProbabilityMeasure ν]

/-- Partial sums `∑_{i<n} a_i φ_i`. -/
def s21gP (a : ℕ → ℝ) (φ : ℕ → Euc d → ℝ) (n : ℕ) : Euc d → ℝ := fun x => ∑ i ∈ Finset.range n, a i * φ i x

theorem s21g_pair_P_succ (a : ℕ → ℝ) (φ : ℕ → Euc d → ℝ) (hφ : ∀ i, MemLp (φ i) 2 ν) (n : ℕ) :
    HRS.Whole.pair ν (s21gP a φ (n + 1)) = HRS.Whole.pair ν (s21gP a φ n) + a n * HRS.Whole.pair ν (φ n) := by
  have hint : ∀ i, Integrable (φ i) ν := fun i => (hφ i).integrable one_le_two
  have e : s21gP a φ (n + 1) = fun x => s21gP a φ n x + a n * φ n x := by
    funext x; simp [s21gP, Finset.sum_range_succ]
  unfold HRS.Whole.pair
  have hP : Integrable (s21gP a φ n) ν := integrable_finsetSum _ fun i _ => (hint i).const_mul (a i)
  rw [e]
  rw [integral_add (f := s21gP a φ n) (g := fun x => a n * φ n x) hP ((hint n).const_mul _),
    integral_const_mul]

theorem s21g_partial_U (a : ℕ → ℝ) (φ : ℕ → Euc d → ℝ) (hφ : ∀ i, MemLp (φ i) 2 ν) (n : ℕ) :
    (↑↑(∑ i ∈ Finset.range n, a i • S45.s45_U (φ i) (hφ i)) : Euc d → ℝ) =ᵐ[ν]
      HRS.Whole.projMean ν (s21gP a φ n) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℝ 2 ν] with x hx
    simp [hx, HRS.Whole.projMean, s21gP, HRS.Whole.pair]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 := Lp.coeFn_add (∑ i ∈ Finset.range n, a i • S45.s45_U (φ i) (hφ i)) (a n • S45.s45_U (φ n) (hφ n))
    have h2 := Lp.coeFn_smul (a n) (S45.s45_U (φ n) (hφ n))
    have h3 := S45.s45_U_ae (hφ n)
    filter_upwards [h1, h2, h3, ih] with x hx1 hx2 hx3 hx4
    rw [hx1]
    simp only [Pi.add_apply]
    rw [hx4, hx2]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hx3]
    simp only [HRS.Whole.projMean]
    rw [s21g_pair_P_succ a φ hφ n]
    have hP : s21gP a φ (n + 1) x = s21gP a φ n x + a n * φ n x := by
      simp [s21gP, Finset.sum_range_succ]
    rw [hP]
    ring

theorem s21g_T_eq {φ : ℕ → Euc d → ℝ} (hφ : ∀ i, MemLp (φ i) 2 ν) {w : ℕ → ℝ} (hw : Summable w)
    (hφw : ∀ i x, |φ i x| ≤ w i) (hU : Summable fun j => ‖S45.s45_U (φ j) (hφ j)‖) (a : SeqL2)
    {ψ : Euc d → ℝ} (hψ : MemLp ψ 2 ν)
    (hs : ∀ x, HasSum (fun j => SeqL2.coord a j * φ j x) (ψ x)) :
    S45.s45_T S45.s45_seqBasis hU a = S45.s45_U ψ hψ := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (abs_nonneg _).trans (hφw i 0)
  have haj : ∀ j, |SeqL2.coord a j| ≤ ‖a‖ := fun j => by
    have := lp.norm_apply_le_norm (by simp : (2 : ℝ≥0∞) ≠ 0) (show lp (fun _ : ℕ => ℝ) 2 from a) j
    rwa [Real.norm_eq_abs] at this
  set A : ℕ → ℝ := fun i => |SeqL2.coord a i| * w i with hA
  have hAs : Summable A := Summable.of_nonneg_of_le (fun i => mul_nonneg (abs_nonneg _) (hw0 i))
    (fun i => mul_le_mul_of_nonneg_right (haj i) (hw0 i)) (hw.mul_left ‖a‖)
  set tail : ℕ → ℝ := fun n => ∑' i, A (i + n) with htail
  have htail0 : Tendsto tail atTop (𝓝 0) := tendsto_sum_nat_add A
  -- partial sums of the series in L²
  set Sn : ℕ → Lp ℝ 2 ν := fun n => ∑ i ∈ Finset.range n, SeqL2.coord a i • S45.s45_U (φ i) (hφ i) with hSn
  have hT : Tendsto Sn atTop (𝓝 (S45.s45_T S45.s45_seqBasis hU a)) := by
    have := (S45.s45_summable_T S45.s45_seqBasis hU a).hasSum.tendsto_sum_nat
    simpa [hSn, S45.s45_T_apply, S45.s45_inner_seqBasis] using this
  have hpoint : ∀ n x, |ψ x - s21gP (fun i => SeqL2.coord a i) φ n x| ≤ tail n := by
    intro n x
    have h1 := (hs x).summable.sum_add_tsum_nat_add n
    rw [(hs x).tsum_eq] at h1
    have e : ψ x - s21gP (fun i => SeqL2.coord a i) φ n x = ∑' i, SeqL2.coord a (i + n) * φ (i + n) x := by
      simp only [s21gP]; linarith
    rw [e]
    have := tsum_of_norm_bounded (f := fun i => SeqL2.coord a (i + n) * φ (i + n) x) (g := fun i => A (i + n))
      ((summable_nat_add_iff n).2 hAs).hasSum (fun i => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hφw _ x) (abs_nonneg _))
    rwa [Real.norm_eq_abs] at this
  have hbound : ∀ n, ‖S45.s45_U ψ hψ - Sn n‖ ≤ 2 * tail n := by
    intro n
    have htn : 0 ≤ tail n := (abs_nonneg _).trans (hpoint n 0)
    have h := Lp.norm_le_of_ae_bound (μ := ν) (f := S45.s45_U ψ hψ - Sn n) (C := 2 * tail n) (by linarith)
      (by
        have h1 := Lp.coeFn_sub (S45.s45_U ψ hψ) (Sn n)
        have h2 := S45.s45_U_ae hψ
        have h3 := s21g_partial_U (fun i => SeqL2.coord a i) φ hφ n
        filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
        rw [hx1]
        simp only [Pi.sub_apply]
        rw [hx2]
        have hx3' : (↑↑(Sn n) : Euc d → ℝ) x = HRS.Whole.projMean ν (s21gP (fun i => SeqL2.coord a i) φ n) x := hx3
        rw [hx3']
        simp only [HRS.Whole.projMean, Real.norm_eq_abs]
        have hdiff : |HRS.Whole.pair ν ψ - HRS.Whole.pair ν (s21gP (fun i => SeqL2.coord a i) φ n)| ≤ tail n := by
          have hpsi : Integrable ψ ν := hψ.integrable one_le_two
          have hP : Integrable (s21gP (fun i => SeqL2.coord a i) φ n) ν :=
            integrable_finsetSum _ fun i _ => ((hφ i).integrable one_le_two).const_mul _
          unfold HRS.Whole.pair
          rw [← integral_sub hpsi hP]
          have := norm_integral_le_of_norm_le_const (μ := ν)
            (f := fun x => ψ x - s21gP (fun i => SeqL2.coord a i) φ n x) (C := tail n)
            (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hpoint n x)
          rw [Real.norm_eq_abs] at this
          simpa using this
        have := hpoint n x
        calc |ψ x - HRS.Whole.pair ν ψ - (s21gP (fun i => SeqL2.coord a i) φ n x -
              HRS.Whole.pair ν (s21gP (fun i => SeqL2.coord a i) φ n))|
            = |(ψ x - s21gP (fun i => SeqL2.coord a i) φ n x) -
              (HRS.Whole.pair ν ψ - HRS.Whole.pair ν (s21gP (fun i => SeqL2.coord a i) φ n))| := by ring_nf
          _ ≤ |ψ x - s21gP (fun i => SeqL2.coord a i) φ n x| +
              |HRS.Whole.pair ν ψ - HRS.Whole.pair ν (s21gP (fun i => SeqL2.coord a i) φ n)| := abs_sub _ _
          _ ≤ 2 * tail n := by linarith)
    simpa [measureUnivNNReal] using h
  have hT2 : Tendsto Sn atTop (𝓝 (S45.s45_U ψ hψ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using htail0.const_mul 2)
    rw [norm_sub_rev]; exact hbound n
  exact tendsto_nhds_unique hT hT2

theorem s21g_dense_basis : Dense (↑(Submodule.span ℝ (Set.range (S45.s45_seqBasis))) : Set SeqL2) :=
  Submodule.dense_iff_topologicalClosure_eq_top.2 S45.s45_seqBasis.dense_span

theorem s21g_clm_ext {f g : SeqL2 →L[ℝ] SeqL2 →L[ℝ] ℝ}
    (h : ∀ i j, f (S45.s45_seqBasis i) (S45.s45_seqBasis j) = g (S45.s45_seqBasis i) (S45.s45_seqBasis j)) :
    f = g := by
  refine ContinuousLinearMap.ext_on s21g_dense_basis ?_
  rintro _ ⟨i, rfl⟩
  refine ContinuousLinearMap.ext_on s21g_dense_basis ?_
  rintro _ ⟨j, rfl⟩
  exact h i j

theorem s21g_cov {g : Euc d → ℝ} {K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν} (hK : S45.IsKData ν g K) {β : ℝ} (hβ : 0 < β)
    {J : ℕ} {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily J φ) {γ : Measure SeqL2}
    (hγ : IsCenteredGaussianSeq γ (fun i j => HRS.Whole.susceptibilityCov g ν β (φ i) (φ j)))
    (a a' : SeqL2) {ψ ψ' : Euc d → ℝ} (hψ : MemLp ψ 2 ν) (hψ' : MemLp ψ' 2 ν)
    (hs : ∀ x, HasSum (fun j => SeqL2.coord a j * φ j x) (ψ x))
    (hs' : ∀ x, HasSum (fun j => SeqL2.coord a' j * φ j x) (ψ' x)) :
    Integrable (fun z : SeqL2 => inner ℝ a z * inner ℝ a' z) γ ∧
      ∫ z, inner ℝ a z * inner ℝ a' z ∂γ = HRS.Whole.susceptibilityCov g ν β ψ ψ' := by
  have hφm : ∀ i, MemLp (φ i) 2 ν := fun i => HRS.MS.Tc5.tc5_memLp_of_cb (hφ.1 i)
  have hU : Summable fun j => ‖S45.s45_U (φ j) (hφm j)‖ := by
    refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) (hφ.2.mul_left 2)
    exact S45.s45_U_norm_le (hφm i) fun x => HRS.MS.Tc5.tc5_cb_sup_le (hφ.1 i) x
  have hφw : ∀ i x, |φ i x| ≤ cbNorm J (φ i) := fun i x => s11p_abs_le_cbNorm (hφ.1 i) x
  obtain ⟨hg, hcovs⟩ := hγ
  haveI : IsGaussian γ := hg.1
  have hmem : MemLp id 2 γ := IsGaussian.memLp_two_id
  have hmean : ∫ z, id z ∂γ = 0 := HRS.HilbertCLTAux.gaussian_mean_zero hg
  -- the covariance form agrees with `s45_C` on the basis
  have hB : covarianceBilin γ = S45.s45_C hK hβ.le S45.s45_seqBasis hU := by
    refine s21g_clm_ext fun i j => ?_
    rw [covarianceBilin_apply hmem, hmean, S45.s45_C_basis]
    simp only [id, sub_zero, S45.s45_inner_seqBasis]
    rw [(hcovs i j).2]
    exact S45.s45_susceptibilityCov_eq hK hβ (hφm i) (hφm j)
  have hint : Integrable (fun z : SeqL2 => inner ℝ a z * inner ℝ a' z) γ := by
    have hn : Integrable (fun z : SeqL2 => ‖z‖ ^ 2) γ := by
      have := hmem.integrable_norm_pow (p := 2) (by norm_num)
      simpa using this
    refine (hn.const_mul (‖a‖ * ‖a'‖)).mono' ?_ (Filter.Eventually.of_forall fun F => ?_)
    · exact ((continuous_const.inner continuous_id).mul (continuous_const.inner continuous_id)).aestronglyMeasurable
    · rw [norm_mul]
      calc ‖inner ℝ a F‖ * ‖inner ℝ a' F‖ ≤ (‖a‖ * ‖F‖) * (‖a'‖ * ‖F‖) :=
            mul_le_mul (norm_inner_le_norm _ _) (norm_inner_le_norm _ _) (norm_nonneg _) (by positivity)
        _ = ‖a‖ * ‖a'‖ * ‖F‖ ^ 2 := by ring
  refine ⟨hint, ?_⟩
  have h1 : ∫ z, inner ℝ a z * inner ℝ a' z ∂γ = covarianceBilin γ a a' := by
    rw [covarianceBilin_apply hmem, hmean]; simp
  rw [h1, hB, S45.s45_C_apply, S45.s45_susceptibilityCov_eq hK hβ hψ hψ',
    s21g_T_eq hφm hφ.2 hφw hU a hψ hs, s21g_T_eq hφm hφ.2 hφw hU a' hψ' hs']

end HRS.MS.S21
