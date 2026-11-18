import HRS.Prob.HilbertCLT
import HRS.Prob.YurinskiiLindeberg
import HRS.MP.KolmChentsov
import HRS.Whole.Orbits

/-!
# S11.1 terminal wave, G01 part 1: Gaussian series with one common iid sequence

For a common iid standard Gaussian sequence `g` and square-summable vectors `ℓ_k` of a Hilbert space `H` we study the `L²`
limit `Y = Σ_k g_k ℓ_k` (`S111tIsGSL`), the exact law of a finite family of continuous linear functionals of such limits
(centered Gaussian with covariance `Σ_k φ_j(ℓ^j_k) φ_l(ℓ^l_k)`, **for several limits driven by the same `g`**), and the fourth moment
bound in `ℓ²`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111T

section Real

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ}

/-- An `L²` limit of the real Gaussian series `Σ_l b_l g_l` is centered Gaussian with variance `Σ b_l²`. -/
theorem s111t_real_series_law (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (hind : iIndepFun g P)
    (b : ℕ → ℝ) (hb : Summable fun l => b l ^ 2) (S : Ω → ℝ) (hS : MemLp S 2 P)
    (hlim : Tendsto (fun K : ℕ => ∫ ω, (∑ l ∈ Finset.range K, b l * g l ω - S ω) ^ 2 ∂P) atTop (𝓝 0)) :
    P.map S = gaussianReal 0 (Real.toNNReal (∑' l, b l ^ 2)) := by
  set Gk : ℕ → Ω → ℝ := fun K ω => ∑ l ∈ Finset.range K, b l * g l ω with hGk
  have hGm : ∀ K, AEMeasurable (Gk K) P := fun K =>
    (HilbertCLTAux.gauss_sum_hasLaw hg hind b K).aemeasurable
  have hGL : ∀ K, MemLp (Gk K) 2 P := fun K =>
    memLp_finsetSum _ (fun j _ => (HilbertCLTAux.gauss_memLp hg j).const_mul (b j))
  set σ2 := ∑' l, b l ^ 2 with hσ2
  have hσ : 0 ≤ σ2 := tsum_nonneg fun _ => sq_nonneg _
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hu : ∀ K, charFun (P.map (Gk K)) t =
      Complex.exp (t * 0 * Complex.I - ((∑ j ∈ Finset.range K, (b j) ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    intro K
    have hlaw := HilbertCLTAux.gauss_sum_hasLaw hg hind b K
    rw [hlaw.map_eq, charFun_gaussianReal]
    congr 2
    push_cast
    simp
  have hv : Tendsto (fun K => ∑ j ∈ Finset.range K, (b j) ^ 2) atTop (𝓝 σ2) :=
    hb.hasSum.tendsto_sum_nat
  let f : ℝ → ℂ := fun v => Complex.exp (t * 0 * Complex.I - (v : ℂ) * (t : ℂ) ^ 2 / 2)
  have hf : Continuous f := by fun_prop
  have hlim1 : Tendsto (fun K => charFun (P.map (Gk K)) t) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal σ2)) t)) := by
    simp_rw [hu]
    rw [charFun_gaussianReal, Real.coe_toNNReal _ hσ]
    exact (hf.tendsto σ2).comp hv
  have hlim2 : Tendsto (fun K => charFun (P.map (Gk K)) t) atTop (𝓝 (charFun (P.map S) t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb' : Tendsto (fun K => |t| * Real.sqrt (∫ ω, (Gk K ω - S ω) ^ 2 ∂P)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hlim
      rw [Real.sqrt_zero] at this
      simpa using this.const_mul |t|
    refine squeeze_zero (fun K => norm_nonneg _) (fun K => ?_) hb'
    have hint : Integrable (fun ω => Gk K ω - S ω) P := ((hGL K).sub hS).integrable one_le_two
    refine (HilbertCLTAux.norm_charFun_sub_le (hGm K) hS.aemeasurable hint t).trans ?_
    gcongr
    have hL2 : MemLp (fun ω => |Gk K ω - S ω|) 2 P := ((hGL K).sub hS).abs
    calc ∫ ω, |Gk K ω - S ω| ∂P ≤ Real.sqrt (∫ ω, |Gk K ω - S ω| ^ 2 ∂P) := HRS.integral_le_sqrt P hL2
      _ = Real.sqrt (∫ ω, (Gk K ω - S ω) ^ 2 ∂P) := by simp_rw [sq_abs]
  exact tendsto_nhds_unique hlim2 hlim1

end Real

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ}

/-- The partial sums `Σ_{j<K} g_j ℓ_j`. -/
def s111t_gsum (g : ℕ → Ω → ℝ) (ℓ : ℕ → H) (K : ℕ) (ω : Ω) : H :=
  ∑ j ∈ Finset.range K, g j ω • ℓ j

/-- `Y` is the `L²(P;H)` limit of the Gaussian series `Σ g_j ℓ_j`. -/
structure S111tIsGSL (P : Measure Ω) (g : ℕ → Ω → ℝ) (ℓ : ℕ → H) (Y : Ω → H) : Prop where
  memLp : MemLp Y 2 P
  tendsto : Tendsto (fun K : ℕ => ∫ ω, ‖s111t_gsum g ℓ K ω - Y ω‖ ^ 2 ∂P) atTop (𝓝 0)

theorem s111t_gsum_memLp (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (ℓ : ℕ → H) (K : ℕ) :
    MemLp (s111t_gsum g ℓ K) 2 P :=
  memLp_finsetSum _ fun j _ =>
    (ContinuousLinearMap.toSpanSingleton ℝ (ℓ j)).comp_memLp' (HilbertCLTAux.gauss_memLp hg j)

/-- Existence of the `L²` limit of a square-summable Gaussian series with a common sequence `g`. -/
theorem s111t_gsl_exists (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (hind : iIndepFun g P)
    (ℓ : ℕ → H) (hs : Summable fun j => ‖ℓ j‖ ^ 2) : ∃ Y : Ω → H, S111tIsGSL P g ℓ Y := by
  have hGk := s111t_gsum_memLp (P := P) hg ℓ
  have hdiff : ∀ n m, n ≤ m → ∫ ω, ‖s111t_gsum g ℓ m ω - s111t_gsum g ℓ n ω‖ ^ 2 ∂P =
      ∑ j ∈ Finset.range m, ‖ℓ j‖ ^ 2 - ∑ j ∈ Finset.range n, ‖ℓ j‖ ^ 2 := by
    intro n m hnm
    have : ∀ ω, s111t_gsum g ℓ m ω - s111t_gsum g ℓ n ω = ∑ j ∈ Finset.Ico n m, g j ω • ℓ j := fun ω => by
      simp only [s111t_gsum]; rw [Finset.sum_Ico_eq_sub _ hnm]
    simp_rw [this]
    rw [HilbertCLTAux.gauss_sum_sq_integral hg hind ℓ, Finset.sum_Ico_eq_sub _ hnm]
  have hcau : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ∫ ω, ‖s111t_gsum g ℓ m ω - s111t_gsum g ℓ n ω‖ ^ 2 ∂P < ε := by
    intro ε hε
    have hc := hs.hasSum.tendsto_sum_nat.cauchySeq
    rw [Metric.cauchySeq_iff] at hc
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rcases le_total n m with h | h
    · rw [hdiff n m h]
      have := hN m hm n hn
      rwa [Real.dist_eq, abs_of_nonneg (by
        have := hdiff n m h
        have h0 : 0 ≤ ∫ ω, ‖s111t_gsum g ℓ m ω - s111t_gsum g ℓ n ω‖ ^ 2 ∂P :=
          integral_nonneg fun _ => by positivity
        linarith)] at this
    · have e : ∫ ω, ‖s111t_gsum g ℓ m ω - s111t_gsum g ℓ n ω‖ ^ 2 ∂P =
          ∫ ω, ‖s111t_gsum g ℓ n ω - s111t_gsum g ℓ m ω‖ ^ 2 ∂P := by
        congr 1; ext ω; rw [norm_sub_rev]
      rw [e, hdiff m n h]
      have := hN n hn m hm
      have h0 : 0 ≤ ∫ ω, ‖s111t_gsum g ℓ n ω - s111t_gsum g ℓ m ω‖ ^ 2 ∂P :=
        integral_nonneg fun _ => by positivity
      have h1 := hdiff m n h
      rwa [Real.dist_eq, abs_of_nonneg (by linarith)] at this
  obtain ⟨F, hF, hlim⟩ := HilbertCLTAux.exists_L2_limit hGk hcau
  exact ⟨F, hF, hlim⟩

/-- Differences of limits driven by the same sequence are the limit of the difference series. -/
theorem S111tIsGSL.sub {ℓ ℓ' : ℕ → H} {Y Y' : Ω → H} (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P)
    (h1 : S111tIsGSL P g ℓ Y) (h2 : S111tIsGSL P g ℓ' Y') :
    S111tIsGSL P g (fun j => ℓ j - ℓ' j) (fun ω => Y ω - Y' ω) := by
  refine ⟨h1.memLp.sub h2.memLp, ?_⟩
  have e : ∀ K ω, s111t_gsum g (fun j => ℓ j - ℓ' j) K ω = s111t_gsum g ℓ K ω - s111t_gsum g ℓ' K ω := by
    intro K ω
    simp only [s111t_gsum, smul_sub, Finset.sum_sub_distrib]
  have hA : ∀ K, MemLp (fun ω => s111t_gsum g ℓ K ω - Y ω) 2 P :=
    fun K => (s111t_gsum_memLp hg ℓ K).sub h1.memLp
  have hB : ∀ K, MemLp (fun ω => s111t_gsum g ℓ' K ω - Y' ω) 2 P :=
    fun K => (s111t_gsum_memLp hg ℓ' K).sub h2.memLp
  have hup : Tendsto (fun K : ℕ => 2 * ∫ ω, ‖s111t_gsum g ℓ K ω - Y ω‖ ^ 2 ∂P +
      2 * ∫ ω, ‖s111t_gsum g ℓ' K ω - Y' ω‖ ^ 2 ∂P) atTop (𝓝 0) := by
    have := (h1.tendsto.const_mul 2).add (h2.tendsto.const_mul 2)
    simpa using this
  refine squeeze_zero (fun K => integral_nonneg fun _ => by positivity) (fun K => ?_) hup
  have iA := (hA K).norm.integrable_sq
  have iB := (hB K).norm.integrable_sq
  calc ∫ ω, ‖s111t_gsum g (fun j => ℓ j - ℓ' j) K ω - (Y ω - Y' ω)‖ ^ 2 ∂P
      ≤ ∫ ω, (2 * ‖s111t_gsum g ℓ K ω - Y ω‖ ^ 2 + 2 * ‖s111t_gsum g ℓ' K ω - Y' ω‖ ^ 2) ∂P := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => by positivity)
          ((iA.const_mul 2).add (iB.const_mul 2)) (ae_of_all _ fun ω => ?_)
        beta_reduce
        rw [e]
        have : s111t_gsum g ℓ K ω - s111t_gsum g ℓ' K ω - (Y ω - Y' ω) =
            (s111t_gsum g ℓ K ω - Y ω) - (s111t_gsum g ℓ' K ω - Y' ω) := by abel
        rw [this]
        have h := norm_sub_le (s111t_gsum g ℓ K ω - Y ω) (s111t_gsum g ℓ' K ω - Y' ω)
        nlinarith [norm_nonneg (s111t_gsum g ℓ K ω - Y ω), norm_nonneg (s111t_gsum g ℓ' K ω - Y' ω),
          norm_nonneg ((s111t_gsum g ℓ K ω - Y ω) - (s111t_gsum g ℓ' K ω - Y' ω)),
          sq_nonneg (‖s111t_gsum g ℓ K ω - Y ω‖ - ‖s111t_gsum g ℓ' K ω - Y' ω‖)]
    _ = 2 * ∫ ω, ‖s111t_gsum g ℓ K ω - Y ω‖ ^ 2 ∂P + 2 * ∫ ω, ‖s111t_gsum g ℓ' K ω - Y' ω‖ ^ 2 ∂P := by
        rw [integral_add (iA.const_mul 2) (iB.const_mul 2), integral_const_mul, integral_const_mul]

end Hilbert

section Vector

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem s111t_memell2 {κ : Type*} (a : κ → ℝ) (ha : Summable fun k => a k ^ 2) :
    Memℓp a 2 := by
  rw [memℓp_gen_iff (by simp)]
  simpa [Real.norm_eq_abs, sq_abs] using ha

/-- The matrix `Σ_k a_{jk} a_{lk}` of square-summable sequences is positive semidefinite. -/
theorem s111t_gram_psd (a : ι → ℕ → ℝ) (ha : ∀ j, Summable fun k => a j k ^ 2) :
    (Matrix.of fun j l => ∑' k, a j k * a l k : Matrix ι ι ℝ).PosSemidef := by
  let v : ι → lp (fun _ : ℕ => ℝ) 2 := fun j => ⟨a j, s111t_memell2 (a j) (ha j)⟩
  have h := Matrix.posSemidef_gram ℝ v
  convert h using 1
  ext j l
  simp only [Matrix.of_apply, Matrix.gram_apply, lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  simp [v, mul_comm]

theorem s111t_summable_mul (a b : ℕ → ℝ) (ha : Summable fun k => a k ^ 2) (hb : Summable fun k => b k ^ 2) :
    Summable fun k => a k * b k := by
  refine Summable.of_norm_bounded ((ha.add hb).mul_left (1 / 2)) (fun k => ?_)
  rw [Real.norm_eq_abs]
  have := sq_nonneg (|a k| - |b k|)
  have h2 : |a k * b k| = |a k| * |b k| := abs_mul _ _
  have h3 : |a k| ^ 2 = a k ^ 2 := sq_abs _
  have h4 : |b k| ^ 2 = b k ^ 2 := sq_abs _
  rw [h2]
  nlinarith

theorem s111t_summable_clm (φ : H →L[ℝ] ℝ) (ℓ : ℕ → H) (hs : Summable fun k => ‖ℓ k‖ ^ 2) :
    Summable fun k => (φ (ℓ k)) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) (hs.mul_left (‖φ‖ ^ 2))
  calc (φ (ℓ k)) ^ 2 = |φ (ℓ k)| ^ 2 := (sq_abs _).symm
    _ ≤ (‖φ‖ * ‖ℓ k‖) ^ 2 := by
        gcongr; exact φ.le_opNorm (ℓ k)
    _ = _ := by ring

/-- **Law of finitely many linear functionals of Gaussian series driven by one common sequence.** -/
theorem s111t_vector_law (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (hind : iIndepFun g P)
    (Y : ι → Ω → H) (ℓ : ι → ℕ → H) (hY : ∀ j, S111tIsGSL P g (ℓ j) (Y j))
    (hsum : ∀ j, Summable fun k => ‖ℓ j k‖ ^ 2) (φ : ι → H →L[ℝ] ℝ) :
    P.map (fun ω => (WithLp.toLp 2 fun j => φ j (Y j ω) : EuclideanSpace ℝ ι)) =
      multivariateGaussian 0 (Matrix.of fun j l => ∑' k, φ j (ℓ j k) * φ l (ℓ l k)) := by
  set a : ι → ℕ → ℝ := fun j k => φ j (ℓ j k) with ha_def
  have ha : ∀ j, Summable fun k => a j k ^ 2 := fun j => s111t_summable_clm (φ j) (ℓ j) (hsum j)
  have hQ := s111t_gram_psd a ha
  have hYm : ∀ j, AEMeasurable (fun ω => φ j (Y j ω)) P := fun j =>
    ((φ j).continuous.comp_aestronglyMeasurable (hY j).memLp.aestronglyMeasurable).aemeasurable
  have hVm : AEMeasurable (fun ω => (WithLp.toLp 2 fun j => φ j (Y j ω) : EuclideanSpace ℝ ι)) P := by
    have : Measurable (fun x : ι → ℝ => (WithLp.toLp 2 x : EuclideanSpace ℝ ι)) := by fun_prop
    exact this.comp_aemeasurable (aemeasurable_pi_iff.2 hYm)
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_multivariateGaussian hQ]
  -- the scalar series
  set b : ℕ → ℝ := fun k => ∑ j, t j * a j k with hb_def
  have hbs : Summable fun k => b k ^ 2 := by
    have : ∀ k, b k ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ j, (t j * a j k) ^ 2 := fun k => by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun j => t j * a j k)
      simpa using this
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) this ?_
    refine Summable.mul_left _ (summable_sum fun j _ => ?_)
    simp_rw [mul_pow]
    exact (ha j).mul_left _
  set St : Ω → ℝ := fun ω => ∑ j, t j * φ j (Y j ω) with hSt
  have hStL : MemLp St 2 P := memLp_finsetSum _ fun j _ =>
    ((φ j).comp_memLp' (hY j).memLp).const_mul (t j)
  have hlim : Tendsto (fun K : ℕ => ∫ ω, (∑ l ∈ Finset.range K, b l * g l ω - St ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have hG : ∀ K ω, ∑ l ∈ Finset.range K, b l * g l ω =
        ∑ j, t j * φ j (s111t_gsum g (ℓ j) K ω) := by
      intro K ω
      simp only [hb_def, ha_def, s111t_gsum, map_sum, map_smul, smul_eq_mul, Finset.sum_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    set z : ι → ℕ → Ω → ℝ := fun j K ω => φ j (s111t_gsum g (ℓ j) K ω - Y j ω) with hz
    have hzL : ∀ j K, MemLp (z j K) 2 P := fun j K =>
      (φ j).comp_memLp' ((s111t_gsum_memLp hg (ℓ j) K).sub (hY j).memLp)
    have hdiff : ∀ K ω, ∑ l ∈ Finset.range K, b l * g l ω - St ω = ∑ j, t j * z j K ω := by
      intro K ω
      rw [hG, hSt]
      simp only [hz, map_sub, mul_sub, Finset.sum_sub_distrib]
    have hz2 : ∀ j, Tendsto (fun K => ∫ ω, (z j K ω) ^ 2 ∂P) atTop (𝓝 0) := by
      intro j
      have h0 : Tendsto (fun K : ℕ => ‖φ j‖ ^ 2 * ∫ ω, ‖s111t_gsum g (ℓ j) K ω - Y j ω‖ ^ 2 ∂P)
          atTop (𝓝 0) := by simpa using (hY j).tendsto.const_mul (‖φ j‖ ^ 2)
      refine squeeze_zero (fun K => integral_nonneg fun _ => sq_nonneg _) (fun K => ?_) h0
      have hn := ((s111t_gsum_memLp hg (ℓ j) K).sub (hY j).memLp).norm.integrable_sq
      calc ∫ ω, (z j K ω) ^ 2 ∂P
          ≤ ∫ ω, ‖φ j‖ ^ 2 * ‖s111t_gsum g (ℓ j) K ω - Y j ω‖ ^ 2 ∂P := by
            refine integral_mono (hzL j K).integrable_sq (hn.const_mul _) (fun ω => ?_)
            have := (φ j).le_opNorm (s111t_gsum g (ℓ j) K ω - Y j ω)
            have h' : |z j K ω| ≤ ‖φ j‖ * ‖s111t_gsum g (ℓ j) K ω - Y j ω‖ := by
              simpa [hz, Real.norm_eq_abs] using this
            calc (z j K ω) ^ 2 = |z j K ω| ^ 2 := (sq_abs _).symm
              _ ≤ (‖φ j‖ * ‖s111t_gsum g (ℓ j) K ω - Y j ω‖) ^ 2 := by gcongr
              _ = _ := by ring
        _ = _ := integral_const_mul _ _
    have hbound : ∀ K, ∫ ω, (∑ l ∈ Finset.range K, b l * g l ω - St ω) ^ 2 ∂P ≤
        (Fintype.card ι : ℝ) * ∑ j, (t j) ^ 2 * ∫ ω, (z j K ω) ^ 2 ∂P := by
      intro K
      have hi : ∀ j, Integrable (fun ω => (t j) ^ 2 * (z j K ω) ^ 2) P :=
        fun j => (hzL j K).integrable_sq.const_mul _
      have hsq : Integrable (fun ω => (∑ l ∈ Finset.range K, b l * g l ω - St ω) ^ 2) P := by
        have : MemLp (fun ω => ∑ l ∈ Finset.range K, b l * g l ω - St ω) 2 P := by
          simp_rw [hdiff]
          exact memLp_finsetSum _ fun j _ => (hzL j K).const_mul (t j)
        exact this.integrable_sq
      calc ∫ ω, (∑ l ∈ Finset.range K, b l * g l ω - St ω) ^ 2 ∂P
          ≤ ∫ ω, (Fintype.card ι : ℝ) * ∑ j, (t j) ^ 2 * (z j K ω) ^ 2 ∂P := by
            refine integral_mono hsq ((integrable_finset_sum _ fun j _ => hi j).const_mul _) (fun ω => ?_)
            simp only [hdiff]
            have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun j => t j * z j K ω)
            simpa [mul_pow] using this
        _ = _ := by
            rw [integral_const_mul, integral_finset_sum _ fun j _ => hi j]
            simp_rw [integral_const_mul]
    have hup : Tendsto (fun K : ℕ => (Fintype.card ι : ℝ) * ∑ j, (t j) ^ 2 * ∫ ω, (z j K ω) ^ 2 ∂P)
        atTop (𝓝 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset ι) (fun j _ => (hz2 j).const_mul ((t j) ^ 2))
      simpa using this.const_mul (Fintype.card ι : ℝ)
    exact squeeze_zero (fun K => integral_nonneg fun _ => sq_nonneg _) hbound hup
  have hlaw := s111t_real_series_law hg hind b hbs St hStL hlim
  have h1 : charFun (P.map (fun ω => (WithLp.toLp 2 fun j => φ j (Y j ω) : EuclideanSpace ℝ ι))) t =
      charFun (P.map St) 1 := by
    rw [charFun_apply, integral_map hVm (by fun_prop), HilbertCLTAux.charFun_map_real_eq hStL.aemeasurable]
    congr 1; ext ω; congr 1
    simp [hSt, PiLp.inner_apply, mul_comm]
  rw [h1, hlaw, charFun_gaussianReal]
  have hσ : ∑' k, b k ^ 2 =
      dotProduct t.ofLp ((Matrix.of fun j l => ∑' k, a j k * a l k).mulVec t.ofLp) := by
    have hsq : ∀ k, b k ^ 2 = ∑ j, ∑ l, t j * t l * (a j k * a l k) := by
      intro k
      simp only [hb_def, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have hsm : ∀ j l, Summable fun k => t j * t l * (a j k * a l k) := fun j l =>
      (s111t_summable_mul (a j) (a l) (ha j) (ha l)).mul_left _
    simp_rw [hsq]
    rw [Summable.tsum_finsetSum (fun j _ => summable_sum fun l _ => hsm j l)]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Summable.tsum_finsetSum (fun l _ => hsm j l)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [tsum_mul_left]
    simp only [WithLp.ofLp]
    ring
  have hσ0 : 0 ≤ ∑' k, b k ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  rw [Real.coe_toNNReal _ hσ0, hσ]
  simp

end Vector

end HRS.MS.S111T
