/-
# HRS.Prob.HilbertCLT — the i.i.d. central limit theorem in `W₂` on a separable Hilbert space

Work package CLT-H (wave 2). This file states, with `sorry` proofs, the probabilistic inputs
that the static field limits (Proposition 4.21, `M:O:prop:negative`, source lines 5513-5557)
and the i.i.d. initial-data lemmas (Lemmas A.36 and A.38, `M:B:lem:iid-init`,
`M:B:lem:iid-init-field`) use, in exactly the form their proofs need:

* existence of a centered Gaussian measure with a prescribed trace-class covariance on a
  separable real Hilbert space (Mathlib at the pin has `IsGaussian` and `covarianceBilin`
  but no such existence theorem in infinite dimension);
* the i.i.d. central limit theorem in `W₂`: for i.i.d. centered `H`-valued summands with a
  finite second moment (possibly degenerate covariance) the normalised sums converge in
  `W₂` to the centered Gaussian with the same covariance (source lines 5521-5557: finite-
  dimensional CLT, uniformly small tails, and "weak convergence together with convergence of
  second moments implies `W₂` convergence in a separable Hilbert space");
* the uniform (triangular-array) version over families with uniformly small Hilbert tails
  and uniformly bounded second moments, which the proof of Proposition 4.21 uses to get
  uniformity in the reference density `μ`;
* the fourth-moment bound `O:eq:fourth-sum` (source line 5540 region).

Conventions. All statements are in `ℝ≥0∞` (`wassersteinE`, `lintegral`) or carry explicit
`MemLp` hypotheses, so no junk value of a real `iSup`/`tsum`/Bochner integral can make a
statement vacuous.
-/
import HRS.Prob.Gaussian

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

set_option linter.unusedSectionVars false

namespace HRS

section HilbertCLT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The normalised partial sum `N^{-1/2} ∑_{i<N} X_i`. -/
def normalizedSum {Ω : Type*} (X : ℕ → Ω → H) (N : ℕ) (ω : Ω) : H :=
  (Real.sqrt N)⁻¹ • ∑ i ∈ Finset.range N, X i ω

/-- A trace-class covariance form on `H`: a bounded bilinear form which is symmetric,
positive semidefinite, and has finite trace along some Hilbert basis. (The trace of a
nonnegative operator does not depend on the basis; one basis suffices.) -/
structure IsTraceClassCov (C : H →L[ℝ] H →L[ℝ] ℝ) : Prop where
  symm : ∀ x y, C x y = C y x
  nonneg : ∀ x, 0 ≤ C x x
  trace : ∃ (ι : Type) (b : HilbertBasis ι ℝ H), Summable fun i => C (b i) (b i)

namespace HilbertCLTAux
open ProbabilityTheory

section TraceClass
variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace H] [BorelSpace H] in
lemma countable_of_orthonormal {ι : Type*} {v : ι → H} (hon : Orthonormal ℝ v) : Countable ι := by
  have := Set.PairwiseDisjoint.countable_of_isOpen (a := (Set.univ : Set ι))
    (s := fun i : ι => Metric.ball (v i) (1 / 2))
    (fun i _ j _ hij => ?_) (fun i _ => Metric.isOpen_ball)
    (fun i _ => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)
  · exact Set.countable_univ_iff.mp this
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  have h1 : dist (v i) (v j) ≤ dist (v i) x + dist x (v j) := dist_triangle _ _ _
  rw [Metric.mem_ball] at hx hx'
  have hd : dist (v i) (v j) ^ 2 = 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, hon.inner_eq_zero hij, hon.norm_eq_one, hon.norm_eq_one]
    norm_num
  have : dist (v i) (v j) < 1 := by linarith [dist_comm x (v i)]
  nlinarith [dist_nonneg (x := v i) (y := v j)]

omit [MeasurableSpace H] [BorelSpace H] in
lemma exists_hilbertBasis_type : ∃ (ι : Type) (_ : Countable ι) (_ : HilbertBasis ι ℝ H), True := by
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis ℝ H
  have hon : Orthonormal ℝ ((↑) : w → H) := hb ▸ b.orthonormal
  have hcount : Countable w := countable_of_orthonormal hon
  obtain ⟨e, he⟩ := Countable.exists_injective_nat w
  let ι := Set.range e
  let eq : w ≃ ι := Equiv.ofInjective e he
  have hv : Orthonormal ℝ (fun j : ι => ((eq.symm j : w) : H)) :=
    hon.comp _ eq.symm.injective
  have hrange : Set.range (fun j : ι => ((eq.symm j : w) : H)) = Set.range ((↑) : w → H) := by
    ext x; constructor
    · rintro ⟨j, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨eq i, by simp⟩
  refine ⟨ι, inferInstance, HilbertBasis.mkOfOrthogonalEqBot hv ?_, trivial⟩
  rw [hrange, ← hb]
  rw [← Submodule.orthogonal_closure, b.dense_span]
  exact Submodule.top_orthogonal_eq_bot
end TraceClass

section Parseval
variable {Ω : Type*} [MeasurableSpace Ω]

omit [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] in
lemma integrable_sq_norm_of_memLp2 {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → H}
    (hX : MemLp X 2 P) : Integrable (fun ω => ‖X ω‖ ^ 2) P := by
  have := hX.integrable_norm_pow (p := 2) (by norm_num)
  exact this

lemma covarianceBilin_law_self (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → H)
    (hX : MemLp X 2 P) (hmean : ∫ ω, X ω ∂P = 0) (x : H) :
    ProbabilityTheory.covarianceBilin (law P X) x x = ∫ ω, (inner ℝ x (X ω)) ^ 2 ∂P := by
  have hm : AEMeasurable X P := hX.aemeasurable
  have hν : MemLp id 2 (law P X) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hm]; exact hX
  rw [ProbabilityTheory.covarianceBilin_apply hν]
  have h0 : (law P X)[id] = 0 := by
    show ∫ x, x ∂(law P X) = 0
    rw [integral_map hm (f := fun x : H => x) (Continuous.aestronglyMeasurable continuous_id)]
    exact hmean
  rw [h0, integral_map hm]
  · simp [sq]
  · exact (Continuous.aestronglyMeasurable (by fun_prop))

lemma integrable_inner_sq (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → H}
    (hX : MemLp X 2 P) (x : H) : Integrable (fun ω => (inner ℝ x (X ω)) ^ 2) P := by
  refine Integrable.mono' ((integrable_sq_norm_of_memLp2 hX).const_mul (‖x‖ ^ 2))
    ((aestronglyMeasurable_const.inner hX.aestronglyMeasurable).pow 2)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  calc (inner ℝ x (X ω)) ^ 2 = |inner ℝ x (X ω)| ^ 2 := (sq_abs _).symm
    _ ≤ (‖x‖ * ‖X ω‖) ^ 2 := by gcongr; exact abs_real_inner_le_norm x (X ω)
    _ = _ := by ring

theorem hasSum_cov_basis (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → H)
    (hX : MemLp X 2 P) (hmean : ∫ ω, X ω ∂P = 0) {ι : Type*} (b : HilbertBasis ι ℝ H) :
    HasSum (fun i => ProbabilityTheory.covarianceBilin (law P X) (b i) (b i))
      (∫ ω, ‖X ω‖ ^ 2 ∂P) := by
  simp_rw [covarianceBilin_law_self P X hX hmean]
  have hint := fun i => integrable_inner_sq P hX (b i)
  have hsum : Summable (fun i => ∫ ω, (inner ℝ (b i) (X ω)) ^ 2 ∂P) := by
    refine summable_of_sum_le (c := ∫ ω, ‖X ω‖ ^ 2 ∂P) (fun i => integral_nonneg fun ω => sq_nonneg _)
      (fun F => ?_)
    rw [← integral_finsetSum _ (fun i _ => hint i)]
    refine integral_mono (integrable_finsetSum _ fun i _ => hint i) (integrable_sq_norm_of_memLp2 hX)
      (fun ω => ?_)
    have := b.orthonormal.sum_inner_products_le (X ω) (s := F)
    simpa [real_inner_comm] using this
  have habs : Summable (fun i => ∫ ω, ‖(inner ℝ (b i) (X ω)) ^ 2‖ ∂P) := by
    simpa [Real.norm_of_nonneg (sq_nonneg _)] using hsum
  haveI : Countable ι := countable_of_orthonormal b.orthonormal
  have := integral_tsum_of_summable_integral_norm hint habs
  have hpt : ∀ ω, ∑' i, (inner ℝ (b i) (X ω)) ^ 2 = ‖X ω‖ ^ 2 := by
    intro ω
    have := b.tsum_inner_mul_inner (X ω) (X ω)
    simp only [real_inner_self_eq_norm_sq] at this
    rw [← this]
    refine tsum_congr fun i => ?_
    rw [real_inner_comm]; ring
  simp_rw [hpt] at this
  rw [← this]
  exact hsum.hasSum
end Parseval

section Moments
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] in
lemma integrable_norm_pow_of_memLp4 {S : Ω → H} (hS : MemLp S 4 P) (k : ℕ) (hk : k ≤ 4) :
    Integrable (fun ω => ‖S ω‖ ^ k) P := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp
  have h := (hS.mono_exponent (p := (k : ℝ≥0∞)) (by exact_mod_cast hk))
  exact h.integrable_norm_pow (by exact_mod_cast hpos.ne')

lemma integrable_inner_of_memLp4 {S Y : Ω → H} (hS : MemLp S 4 P) (hY : MemLp Y 4 P) :
    Integrable (fun ω => inner ℝ (S ω) (Y ω)) P := by
  have h2S := integrable_norm_pow_of_memLp4 hS 2 (by norm_num)
  have h2Y := integrable_norm_pow_of_memLp4 hY 2 (by norm_num)
  refine Integrable.mono' (h2S.fun_add h2Y) ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (hS.aestronglyMeasurable.inner hY.aestronglyMeasurable)
  · calc ‖inner ℝ (S ω) (Y ω)‖ ≤ ‖S ω‖ * ‖Y ω‖ := norm_inner_le_norm _ _
      _ ≤ ‖S ω‖ ^ 2 + ‖Y ω‖ ^ 2 := by nlinarith [norm_nonneg (S ω), norm_nonneg (Y ω), sq_nonneg (‖S ω‖ - ‖Y ω‖)]

lemma integral_inner_indep {U Y : Ω → H} (hind : IndepFun U Y P) (hU : Integrable U P)
    (hY : Integrable Y P) (h0 : ∫ ω, Y ω ∂P = 0) : ∫ ω, inner ℝ (U ω) (Y ω) ∂P = 0 := by
  have h' : ∫ ω, inner ℝ (U ω) (Y ω) ∂P = innerSL ℝ (∫ ω, U ω ∂P) (∫ ω, Y ω ∂P) :=
    hind.integral_bilin hU hY (innerSL ℝ)
  rw [h', h0]; simp

lemma integral_sq_add {S Y : Ω → H} (hind : IndepFun S Y P) (hS : MemLp S 4 P) (hY : MemLp Y 4 P)
    (hY0 : ∫ ω, Y ω ∂P = 0) :
    ∫ ω, ‖S ω + Y ω‖ ^ 2 ∂P = ∫ ω, ‖S ω‖ ^ 2 ∂P + ∫ ω, ‖Y ω‖ ^ 2 ∂P := by
  have hSi : Integrable S P := hS.integrable (by norm_num)
  have hYi : Integrable Y P := hY.integrable (by norm_num)
  have h2S := integrable_norm_pow_of_memLp4 hS 2 (by norm_num)
  have h2Y := integrable_norm_pow_of_memLp4 hY 2 (by norm_num)
  have hc := integrable_inner_of_memLp4 hS hY
  have : ∀ ω, ‖S ω + Y ω‖ ^ 2 = ‖S ω‖ ^ 2 + ‖Y ω‖ ^ 2 + 2 * inner ℝ (S ω) (Y ω) := by
    intro ω; rw [norm_add_sq_real]; ring
  simp_rw [this]
  rw [integral_add (h2S.fun_add h2Y) (hc.const_mul 2), integral_add h2S h2Y, integral_const_mul,
    integral_inner_indep hind hSi hYi hY0]
  ring

omit [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] in
lemma pow4_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have h1 : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
  have h2 : (x ^ 2 + y ^ 2) ^ 2 ≤ 2 * (x ^ 4 + y ^ 4) := by nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
  calc (x + y) ^ 4 = ((x + y) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (x ^ 2 + y ^ 2)) ^ 2 := by gcongr
    _ = 4 * (x ^ 2 + y ^ 2) ^ 2 := by ring
    _ ≤ 8 * (x ^ 4 + y ^ 4) := by linarith

lemma integral_fourth_add_le {S Y : Ω → H} (hind : IndepFun S Y P) (hS : MemLp S 4 P)
    (hY : MemLp Y 4 P) (hS0 : ∫ ω, S ω ∂P = 0) (hY0 : ∫ ω, Y ω ∂P = 0) :
    ∫ ω, ‖S ω + Y ω‖ ^ 4 ∂P ≤ ∫ ω, ‖S ω‖ ^ 4 ∂P + ∫ ω, ‖Y ω‖ ^ 4 ∂P +
      6 * ((∫ ω, ‖S ω‖ ^ 2 ∂P) * ∫ ω, ‖Y ω‖ ^ 2 ∂P) := by
  have hSi : Integrable S P := hS.integrable (by norm_num)
  have hYi : Integrable Y P := hY.integrable (by norm_num)
  have h4S := integrable_norm_pow_of_memLp4 hS 4 le_rfl
  have h4Y := integrable_norm_pow_of_memLp4 hY 4 le_rfl
  have h3S := integrable_norm_pow_of_memLp4 hS 3 (by norm_num)
  have h3Y := integrable_norm_pow_of_memLp4 hY 3 (by norm_num)
  have h2S := integrable_norm_pow_of_memLp4 hS 2 (by norm_num)
  have h2Y := integrable_norm_pow_of_memLp4 hY 2 (by norm_num)
  have mS := hS.aestronglyMeasurable
  have mY := hY.aestronglyMeasurable
  have hT : Integrable (fun ω => (‖S ω‖ + ‖Y ω‖) ^ 4) P := by
    refine Integrable.mono' ((h4S.fun_add h4Y).const_mul 8) ?_
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((mS.norm.add mY.norm).pow 4)
    · rw [Real.norm_of_nonneg (by positivity)]
      exact pow4_le _ _ (norm_nonneg _) (norm_nonneg _)
  -- bound for the products
  have hab : ∀ ω, ‖S ω‖ ^ 2 * ‖Y ω‖ ^ 2 ≤ (‖S ω‖ + ‖Y ω‖) ^ 4 := by
    intro ω
    have := norm_nonneg (S ω); have := norm_nonneg (Y ω)
    have h : ‖S ω‖ * ‖Y ω‖ ≤ (‖S ω‖ + ‖Y ω‖) ^ 2 := by nlinarith
    calc ‖S ω‖ ^ 2 * ‖Y ω‖ ^ 2 = (‖S ω‖ * ‖Y ω‖) ^ 2 := by ring
      _ ≤ ((‖S ω‖ + ‖Y ω‖) ^ 2) ^ 2 := by gcongr
      _ = _ := by ring
  have hcle : ∀ ω, |inner ℝ (S ω) (Y ω)| ≤ ‖S ω‖ * ‖Y ω‖ := fun ω => by
    simpa using abs_real_inner_le_norm (S ω) (Y ω)
  have hI_ab : Integrable (fun ω => ‖S ω‖ ^ 2 * ‖Y ω‖ ^ 2) P := by
    refine hT.mono' ((mS.norm.pow 2).mul (mY.norm.pow 2)) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]; exact hab ω
  have hI_ca : Integrable (fun ω => ‖S ω‖ ^ 2 * inner ℝ (S ω) (Y ω)) P := by
    refine hT.mono' ((mS.norm.pow 2).mul (mS.inner mY)) (Filter.Eventually.of_forall fun ω => ?_)
    have := norm_nonneg (S ω); have := norm_nonneg (Y ω)
    rw [norm_mul, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
    calc ‖S ω‖ ^ 2 * |inner ℝ (S ω) (Y ω)| ≤ ‖S ω‖ ^ 2 * (‖S ω‖ * ‖Y ω‖) := by
          gcongr; exact hcle ω
      _ ≤ (‖S ω‖ + ‖Y ω‖) ^ 4 := by
          have : ‖S ω‖ ≤ ‖S ω‖ + ‖Y ω‖ := by linarith
          have h2 : ‖Y ω‖ ≤ ‖S ω‖ + ‖Y ω‖ := by linarith
          calc ‖S ω‖ ^ 2 * (‖S ω‖ * ‖Y ω‖) = ‖S ω‖ * ‖S ω‖ * ‖S ω‖ * ‖Y ω‖ := by ring
            _ ≤ (‖S ω‖ + ‖Y ω‖) * (‖S ω‖ + ‖Y ω‖) * (‖S ω‖ + ‖Y ω‖) * (‖S ω‖ + ‖Y ω‖) := by
                gcongr
            _ = _ := by ring
  have hI_cb : Integrable (fun ω => ‖Y ω‖ ^ 2 * inner ℝ (S ω) (Y ω)) P := by
    refine hT.mono' ((mY.norm.pow 2).mul (mS.inner mY)) (Filter.Eventually.of_forall fun ω => ?_)
    have := norm_nonneg (S ω); have := norm_nonneg (Y ω)
    rw [norm_mul, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
    calc ‖Y ω‖ ^ 2 * |inner ℝ (S ω) (Y ω)| ≤ ‖Y ω‖ ^ 2 * (‖S ω‖ * ‖Y ω‖) := by
          gcongr; exact hcle ω
      _ ≤ (‖S ω‖ + ‖Y ω‖) ^ 4 := by
          have : ‖S ω‖ ≤ ‖S ω‖ + ‖Y ω‖ := by linarith
          have h2 : ‖Y ω‖ ≤ ‖S ω‖ + ‖Y ω‖ := by linarith
          calc ‖Y ω‖ ^ 2 * (‖S ω‖ * ‖Y ω‖) = ‖Y ω‖ * ‖Y ω‖ * ‖Y ω‖ * ‖S ω‖ := by ring
            _ ≤ (‖S ω‖ + ‖Y ω‖) * (‖S ω‖ + ‖Y ω‖) * (‖S ω‖ + ‖Y ω‖) * (‖S ω‖ + ‖Y ω‖) := by
                gcongr
            _ = _ := by ring
  -- vanishing cross terms
  have hU : Integrable (fun ω => ‖S ω‖ ^ 2 • S ω) P := by
    refine Integrable.mono' (h2S.fun_add h4S) ((mS.norm.pow 2).smul mS) (Filter.Eventually.of_forall fun ω => ?_)
    have := norm_nonneg (S ω)
    have e : ‖‖S ω‖ ^ 2 • S ω‖ = ‖S ω‖ ^ 3 := by
      rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _)]; ring
    show ‖‖S ω‖ ^ 2 • S ω‖ ≤ ‖S ω‖ ^ 2 + ‖S ω‖ ^ 4
    rw [e]
    nlinarith [sq_nonneg (‖S ω‖ ^ 2 - ‖S ω‖), sq_nonneg (‖S ω‖ - 1), mul_nonneg this (sq_nonneg (‖S ω‖ - 1))]
  have hV : Integrable (fun ω => ‖Y ω‖ ^ 2 • Y ω) P := by
    refine Integrable.mono' (h2Y.fun_add h4Y) ((mY.norm.pow 2).smul mY) (Filter.Eventually.of_forall fun ω => ?_)
    have := norm_nonneg (Y ω)
    have e : ‖‖Y ω‖ ^ 2 • Y ω‖ = ‖Y ω‖ ^ 3 := by
      rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _)]; ring
    show ‖‖Y ω‖ ^ 2 • Y ω‖ ≤ ‖Y ω‖ ^ 2 + ‖Y ω‖ ^ 4
    rw [e]
    nlinarith [sq_nonneg (‖Y ω‖ ^ 2 - ‖Y ω‖), sq_nonneg (‖Y ω‖ - 1), mul_nonneg this (sq_nonneg (‖Y ω‖ - 1))]
  have hmeas : Measurable (fun s : H => ‖s‖ ^ 2 • s) := by fun_prop
  have hca : ∫ ω, ‖S ω‖ ^ 2 * inner ℝ (S ω) (Y ω) ∂P = 0 := by
    have := integral_inner_indep (hind.comp hmeas measurable_id) hU hYi hY0
    simpa [inner_smul_left] using this
  have hcb : ∫ ω, ‖Y ω‖ ^ 2 * inner ℝ (S ω) (Y ω) ∂P = 0 := by
    have := integral_inner_indep (hind.symm.comp hmeas measurable_id) hV hSi hS0
    simpa [inner_smul_left, real_inner_comm] using this
  have hab_int : ∫ ω, ‖S ω‖ ^ 2 * ‖Y ω‖ ^ 2 ∂P = (∫ ω, ‖S ω‖ ^ 2 ∂P) * ∫ ω, ‖Y ω‖ ^ 2 ∂P := by
    have hind' : IndepFun (fun ω => ‖S ω‖ ^ 2) (fun ω => ‖Y ω‖ ^ 2) P :=
      hind.comp (φ := fun s : H => ‖s‖ ^ 2) (ψ := fun s : H => ‖s‖ ^ 2) (by fun_prop) (by fun_prop)
    exact hind'.integral_fun_mul_eq_mul_integral (mS.norm.pow 2) (mY.norm.pow 2)
  -- pointwise bound
  have hpt : ∀ ω, ‖S ω + Y ω‖ ^ 4 ≤ ‖S ω‖ ^ 4 + ‖Y ω‖ ^ 4 + 6 * (‖S ω‖ ^ 2 * ‖Y ω‖ ^ 2) +
      4 * (‖S ω‖ ^ 2 * inner ℝ (S ω) (Y ω)) + 4 * (‖Y ω‖ ^ 2 * inner ℝ (S ω) (Y ω)) := by
    intro ω
    have hc2 : (inner ℝ (S ω) (Y ω)) ^ 2 ≤ ‖S ω‖ ^ 2 * ‖Y ω‖ ^ 2 := by
      have := abs_real_inner_le_norm (S ω) (Y ω)
      calc (inner ℝ (S ω) (Y ω)) ^ 2 = |inner ℝ (S ω) (Y ω)| ^ 2 := (sq_abs _).symm
        _ ≤ (‖S ω‖ * ‖Y ω‖) ^ 2 := by gcongr
        _ = _ := by ring
    have e : ‖S ω + Y ω‖ ^ 4 = (‖S ω‖ ^ 2 + ‖Y ω‖ ^ 2 + 2 * inner ℝ (S ω) (Y ω)) ^ 2 := by
      have := norm_add_sq_real (S ω) (Y ω)
      calc ‖S ω + Y ω‖ ^ 4 = (‖S ω + Y ω‖ ^ 2) ^ 2 := by ring
        _ = _ := by rw [this]; ring
    rw [e]; nlinarith [hc2]
  calc ∫ ω, ‖S ω + Y ω‖ ^ 4 ∂P
      ≤ ∫ ω, (‖S ω‖ ^ 4 + ‖Y ω‖ ^ 4 + 6 * (‖S ω‖ ^ 2 * ‖Y ω‖ ^ 2) +
      4 * (‖S ω‖ ^ 2 * inner ℝ (S ω) (Y ω)) + 4 * (‖Y ω‖ ^ 2 * inner ℝ (S ω) (Y ω))) ∂P := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity) ?_
          (Filter.Eventually.of_forall hpt)
        exact ((((h4S.fun_add h4Y).fun_add (hI_ab.const_mul 6)).fun_add (hI_ca.const_mul 4)).fun_add (hI_cb.const_mul 4))
    _ = _ := by
        rw [integral_add (((h4S.fun_add h4Y).fun_add (hI_ab.const_mul 6)).fun_add (hI_ca.const_mul 4)) (hI_cb.const_mul 4),
          integral_add ((h4S.fun_add h4Y).fun_add (hI_ab.const_mul 6)) (hI_ca.const_mul 4),
          integral_add (h4S.fun_add h4Y) (hI_ab.const_mul 6), integral_add h4S h4Y,
          integral_const_mul, integral_const_mul, integral_const_mul, hca, hcb, hab_int]
        ring
end Moments

section IID
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma identDistrib_of_iid {X : ℕ → Ω → H} (hiid : IsIIDCopies P X) (h0 : AEMeasurable (X 0) P)
    (hm : ∀ i, AEMeasurable (X i) P) (i : ℕ) : IdentDistrib (X i) (X 0) P P :=
  ⟨hm i, h0, hiid.2 i 0⟩

lemma iid_memLp_integral {X : ℕ → Ω → H} (hiid : IsIIDCopies P X) {p : ℝ≥0∞}
    (h0 : MemLp (X 0) p P) (hm : ∀ i, AEMeasurable (X i) P) (i : ℕ) :
    MemLp (X i) p P ∧ ∫ ω, X i ω ∂P = ∫ ω, X 0 ω ∂P ∧
      ∀ k : ℕ, ∫ ω, ‖X i ω‖ ^ k ∂P = ∫ ω, ‖X 0 ω‖ ^ k ∂P := by
  have hid := identDistrib_of_iid hiid h0.aemeasurable hm i
  refine ⟨hid.memLp_iff.2 h0, hid.integral_eq, fun k => ?_⟩
  exact (hid.comp (u := fun x : H => ‖x‖ ^ k) (by fun_prop)).integral_eq

lemma fourth_sum_bound {X : ℕ → Ω → H} (hiid : IsIIDCopies P X) (hL4 : MemLp (X 0) 4 P)
    (hm : ∀ i, AEMeasurable (X i) P)
    (hmean : ∫ ω, X 0 ω ∂P = 0) (n : ℕ) :
    MemLp (fun ω => ∑ i ∈ Finset.range n, X i ω) 4 P ∧
    ∫ ω, ‖∑ i ∈ Finset.range n, X i ω‖ ^ 2 ∂P = n * ∫ ω, ‖X 0 ω‖ ^ 2 ∂P ∧
    ∫ ω, ‖∑ i ∈ Finset.range n, X i ω‖ ^ 4 ∂P ≤
      n * ∫ ω, ‖X 0 ω‖ ^ 4 ∂P + 3 * n * (n - 1) * (∫ ω, ‖X 0 ω‖ ^ 2 ∂P) ^ 2 ∧
    ∫ ω, ∑ i ∈ Finset.range n, X i ω ∂P = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hM, h2, h4, h0⟩ := ih
    obtain ⟨hMn, hIn, hKn⟩ := iid_memLp_integral hiid hL4 hm n
    have hind : IndepFun (fun ω => ∑ i ∈ Finset.range n, X i ω) (X n) P := by
      have := hiid.1.indepFun_finsetSum_of_notMem₀ hm (s := Finset.range n) (i := n) (by simp)
      convert this using 1
      ext ω; simp
    simp only [Finset.sum_range_succ]
    refine ⟨hM.add hMn, ?_, ?_, ?_⟩
    · rw [integral_sq_add hind hM hMn (by rw [hIn, hmean]), h2, hKn 2]; push_cast; ring
    · have := integral_fourth_add_le hind hM hMn h0 (by rw [hIn, hmean])
      rw [h2, hKn 2, hKn 4] at this
      push_cast
      nlinarith [this, h4]
    · rw [integral_add (hM.integrable (by norm_num)) (hMn.integrable (by norm_num)), h0, hIn, hmean]
      simp
end IID

lemma iid_fourth_aux {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → H} (hiid : IsIIDCopies P X) (hL4 : MemLp (X 0) 4 P)
    (hm : ∀ i, AEMeasurable (X i) P)
    (hmean : ∫ ω, X 0 ω ∂P = 0) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, ‖(Real.sqrt N)⁻¹ • ∑ i ∈ Finset.range N, X i ω‖ ^ 4 ∂P ≤
      (N : ℝ)⁻¹ * ∫ ω, ‖X 0 ω‖ ^ 4 ∂P + 3 * (∫ ω, ‖X 0 ω‖ ^ 2 ∂P) ^ 2 := by
  obtain ⟨-, -, h4, -⟩ := fourth_sum_bound hiid hL4 hm hmean N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have e : ∀ ω, ‖(Real.sqrt N)⁻¹ • ∑ i ∈ Finset.range N, X i ω‖ ^ 4 =
      ((N : ℝ)⁻¹) ^ 2 * ‖∑ i ∈ Finset.range N, X i ω‖ ^ 4 := by
    intro ω
    rw [norm_smul, mul_pow, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    congr 1
    rw [inv_pow]
    have : (Real.sqrt N) ^ 4 = (N : ℝ) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hNpos.le]
    rw [this, inv_pow]
  simp_rw [e]
  rw [integral_const_mul]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc ((N : ℝ)⁻¹) ^ 2 * ∫ ω, ‖∑ i ∈ Finset.range N, X i ω‖ ^ 4 ∂P
      ≤ ((N : ℝ)⁻¹) ^ 2 * (N * ∫ ω, ‖X 0 ω‖ ^ 4 ∂P + 3 * N * (N - 1) * (∫ ω, ‖X 0 ω‖ ^ 2 ∂P) ^ 2) := by
        gcongr
    _ ≤ _ := by
        have h2 : 0 ≤ (∫ ω, ‖X 0 ω‖ ^ 2 ∂P) ^ 2 := sq_nonneg _
        have : ((N : ℝ)⁻¹) ^ 2 * (N * ∫ ω, ‖X 0 ω‖ ^ 4 ∂P + 3 * N * (N - 1) * (∫ ω, ‖X 0 ω‖ ^ 2 ∂P) ^ 2)
            = (N : ℝ)⁻¹ * ∫ ω, ‖X 0 ω‖ ^ 4 ∂P + 3 * ((N - 1) / N) * (∫ ω, ‖X 0 ω‖ ^ 2 ∂P) ^ 2 := by
          field_simp
        rw [this]
        have : (N - 1 : ℝ) / N ≤ 1 := by rw [div_le_one hNpos]; linarith
        nlinarith [mul_le_mul_of_nonneg_right this h2]

section Chol

/-- A symmetric positive semidefinite bounded operator. -/
structure IsPSDOp (A : H →L[ℝ] H) : Prop where
  symm : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)
  nonneg : ∀ x, 0 ≤ inner ℝ (A x) x

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma IsPSDOp.cs {A : H →L[ℝ] H} (hA : IsPSDOp A) (u x : H) :
    (inner ℝ (A u) x) ^ 2 ≤ inner ℝ (A u) u * inner ℝ (A x) x := by
  have key : ∀ t : ℝ, 0 ≤ inner ℝ (A u) u * (t * t) + (2 * inner ℝ (A u) x) * t + inner ℝ (A x) x := by
    intro t
    have h := hA.nonneg (x + t • u)
    have e : inner ℝ (A (x + t • u)) (x + t • u) =
        inner ℝ (A u) u * (t * t) + (2 * inner ℝ (A u) x) * t + inner ℝ (A x) x := by
      rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right, inner_smul_left,
        inner_smul_left, inner_smul_right, inner_smul_right, hA.symm x u]
      simp only [conj_trivial, real_inner_comm (A u) x]
      ring
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma IsPSDOp.eq_zero_of_diag {A : H →L[ℝ] H} (hA : IsPSDOp A) {u : H} (h : inner ℝ (A u) u = 0) :
    A u = 0 := by
  have h2 : ∀ x, (inner ℝ (A u) x) ^ 2 ≤ 0 := fun x => by
    have := hA.cs u x; rw [h] at this; simpa using this
  apply ext_inner_right ℝ
  intro x
  have := h2 x
  have h0 : (inner ℝ (A u) x) ^ 2 = 0 := le_antisymm this (sq_nonneg _)
  simpa using h0


/-- One step of the (pivoted) Cholesky elimination. -/
def cholStep (A : H →L[ℝ] H) (u : H) : H →L[ℝ] H :=
  if inner ℝ (A u) u = 0 then A
  else A - (inner ℝ (A u) u)⁻¹ • ((innerSL ℝ (A u)).smulRight (A u))

/-- The vector eliminated by the step. -/
def cholVec (A : H →L[ℝ] H) (u : H) : H :=
  if inner ℝ (A u) u = 0 then 0 else (Real.sqrt (inner ℝ (A u) u))⁻¹ • A u

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma cholStep_inner {A : H →L[ℝ] H} {u : H} (hd : 0 ≤ inner ℝ (A u) u) (x y : H) :
    inner ℝ (cholStep A u x) y =
      inner ℝ (A x) y - inner ℝ (cholVec A u) x * inner ℝ (cholVec A u) y := by
  by_cases h : inner ℝ (A u) u = 0
  · simp [cholStep, cholVec, h]
  · have hpos : 0 < inner ℝ (A u) u := lt_of_le_of_ne hd (Ne.symm h)
    simp only [cholStep, cholVec, h, ite_false, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      inner_sub_left, inner_smul_left, conj_trivial, inner_smul_right]
    have : (Real.sqrt (inner ℝ (A u) u))⁻¹ * (Real.sqrt (inner ℝ (A u) u))⁻¹ =
        (inner ℝ (A u) u)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hd]
    rw [← this]; ring


/-- The Cholesky sequence of operators. -/
def cholSeq (A : H →L[ℝ] H) (u : ℕ → H) : ℕ → (H →L[ℝ] H)
  | 0 => A
  | k + 1 => cholStep (cholSeq A u k) (u k)

/-- The `k`-th eliminated vector. -/
def cholC (A : H →L[ℝ] H) (u : ℕ → H) (k : ℕ) : H := cholVec (cholSeq A u k) (u k)

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma cholVec_sq_le {A : H →L[ℝ] H} (hA : IsPSDOp A) (u x : H) :
    (inner ℝ (cholVec A u) x) ^ 2 ≤ inner ℝ (A x) x := by
  by_cases h : inner ℝ (A u) u = 0
  · simp [cholVec, h, hA.nonneg x]
  · have hpos : 0 < inner ℝ (A u) u := lt_of_le_of_ne (hA.nonneg u) (Ne.symm h)
    simp only [cholVec, h, ite_false, inner_smul_left, conj_trivial]
    have h1 := hA.cs u x
    calc ((Real.sqrt (inner ℝ (A u) u))⁻¹ * inner ℝ (A u) x) ^ 2
        = (inner ℝ (A u) u)⁻¹ * (inner ℝ (A u) x) ^ 2 := by
          rw [mul_pow, inv_pow, Real.sq_sqrt hpos.le]
      _ ≤ (inner ℝ (A u) u)⁻¹ * (inner ℝ (A u) u * inner ℝ (A x) x) := by gcongr
      _ = inner ℝ (A x) x := by field_simp

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma cholStep_psd {A : H →L[ℝ] H} (hA : IsPSDOp A) (u : H) : IsPSDOp (cholStep A u) := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [← real_inner_comm x (cholStep A u y), cholStep_inner (hA.nonneg u) x y,
      cholStep_inner (hA.nonneg u) y x, hA.symm x y, real_inner_comm x (A y)]
    ring
  · rw [cholStep_inner (hA.nonneg u)]
    have := cholVec_sq_le hA u x
    nlinarith

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma cholSeq_psd {A : H →L[ℝ] H} (hA : IsPSDOp A) (u : ℕ → H) : ∀ k, IsPSDOp (cholSeq A u k)
  | 0 => hA
  | k + 1 => cholStep_psd (cholSeq_psd hA u k) _

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma cholSeq_succ_inner {A : H →L[ℝ] H} (hA : IsPSDOp A) (u : ℕ → H) (k : ℕ) (x y : H) :
    inner ℝ (cholSeq A u (k + 1) x) y =
      inner ℝ (cholSeq A u k x) y - inner ℝ (cholC A u k) x * inner ℝ (cholC A u k) y :=
  cholStep_inner ((cholSeq_psd hA u k).nonneg _) x y

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma cholSeq_le {A : H →L[ℝ] H} (hA : IsPSDOp A) (u : ℕ → H) (x : H) :
    ∀ k, inner ℝ (cholSeq A u k x) x ≤ inner ℝ (A x) x
  | 0 => le_rfl
  | k + 1 => by
      rw [cholSeq_succ_inner hA u k]
      nlinarith [cholSeq_le hA u x k, sq_nonneg (inner ℝ (cholC A u k) x)]

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma cholSeq_kill {A : H →L[ℝ] H} (hA : IsPSDOp A) (u : ℕ → H) :
    ∀ k j, j < k → cholSeq A u k (u j) = 0 := by
  intro k
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj
    have hk := cholSeq_psd hA u k
    apply ext_inner_right ℝ
    intro y
    rw [cholSeq_succ_inner hA u k]
    by_cases hjk : j = k
    · subst hjk
      by_cases h : inner ℝ (cholSeq A u j (u j)) (u j) = 0
      · have := hk.eq_zero_of_diag h
        simp [cholC, cholVec, this]
      · have hpos : 0 < inner ℝ (cholSeq A u j (u j)) (u j) := lt_of_le_of_ne (hk.nonneg _) (Ne.symm h)
        simp only [cholC, cholVec, h, ite_false, inner_smul_left, conj_trivial]
        have : (Real.sqrt (inner ℝ (cholSeq A u j (u j)) (u j)))⁻¹ * (Real.sqrt (inner ℝ (cholSeq A u j (u j)) (u j)))⁻¹ =
            (inner ℝ (cholSeq A u j (u j)) (u j))⁻¹ := by
          rw [← mul_inv, Real.mul_self_sqrt hpos.le]
        simp only [inner_zero_left]
        rw [show (Real.sqrt (inner ℝ (cholSeq A u j (u j)) (u j)))⁻¹ * inner ℝ (cholSeq A u j (u j)) (u j) *
            ((Real.sqrt (inner ℝ (cholSeq A u j (u j)) (u j)))⁻¹ * inner ℝ (cholSeq A u j (u j)) y) =
            ((Real.sqrt (inner ℝ (cholSeq A u j (u j)) (u j)))⁻¹ * (Real.sqrt (inner ℝ (cholSeq A u j (u j)) (u j)))⁻¹) *
              inner ℝ (cholSeq A u j (u j)) (u j) * inner ℝ (cholSeq A u j (u j)) y by ring, this]
        field_simp
        ring
    · have hjk' : j < k := by omega
      have h0 := ih j hjk'
      have hc : inner ℝ (cholC A u k) (u j) = 0 := by
        by_cases h : inner ℝ (cholSeq A u k (u k)) (u k) = 0
        · simp [cholC, cholVec, h]
        · simp only [cholC, cholVec, h, ite_false, inner_smul_left, conj_trivial]
          have : inner ℝ (cholSeq A u k (u k)) (u j) = 0 := by
            rw [hk.symm, h0, inner_zero_right]
          rw [this, mul_zero]
      simp [h0, hc]


omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma cholSeq_sum {A : H →L[ℝ] H} (hA : IsPSDOp A) (u : ℕ → H) (x y : H) :
    ∀ m, inner ℝ (A x) y = ∑ j ∈ Finset.range m, inner ℝ (cholC A u j) x * inner ℝ (cholC A u j) y +
      inner ℝ (cholSeq A u m x) y
  | 0 => by simp [cholSeq]
  | m + 1 => by
      rw [Finset.sum_range_succ, cholSeq_succ_inner hA u m, cholSeq_sum hA u x y m]
      ring

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma cholSeq_tendsto_diag {A : H →L[ℝ] H} (hA : IsPSDOp A) (u : ℕ → H)
    (hdense : Dense (Submodule.span ℝ (Set.range u) : Set H)) (x : H) :
    Tendsto (fun m => inner ℝ (cholSeq A u m x) x) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hA0 : 0 ≤ ‖A‖ := norm_nonneg _
  obtain ⟨w, hw, hxw⟩ := hdense.exists_dist_lt x (show 0 < Real.sqrt (ε / (‖A‖ + 1)) by positivity)
  -- w lies in span of finitely many u j
  let V : ℕ → Submodule ℝ H := fun m => Submodule.span ℝ (u '' Set.Iio m)
  have hVmono : Monotone V := fun a b hab => Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hab))
  have hle : Submodule.span ℝ (Set.range u) ≤ ⨆ m, V m := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact Submodule.mem_iSup_of_mem (j + 1) (Submodule.subset_span ⟨j, by simp, rfl⟩)
  obtain ⟨K, hK⟩ := (Submodule.mem_iSup_of_directed V hVmono.directed_le).mp (hle hw)
  refine ⟨K, fun m hm => ?_⟩
  have hker : V m ≤ LinearMap.ker (cholSeq A u m : H →ₗ[ℝ] H) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, hj, rfl⟩
    exact cholSeq_kill hA u m j hj
  have hAw : cholSeq A u m w = 0 := hker (hVmono hm hK)
  have hpsd := cholSeq_psd hA u m
  set z := x - w with hz
  have hdiag : inner ℝ (cholSeq A u m x) x = inner ℝ (cholSeq A u m z) z := by
    have hxz : x = z + w := by rw [hz]; abel
    have e1 : inner ℝ (cholSeq A u m z) w = 0 := by rw [hpsd.symm, hAw, inner_zero_right]
    conv_lhs => rw [hxz]
    rw [map_add, hAw, add_zero, inner_add_right, e1, add_zero]
  have hbound : inner ℝ (cholSeq A u m z) z ≤ ‖A‖ * ‖z‖ ^ 2 := by
    refine (cholSeq_le hA u z m).trans ?_
    calc inner ℝ (A z) z ≤ ‖A z‖ * ‖z‖ := real_inner_le_norm _ _
      _ ≤ ‖A‖ * ‖z‖ * ‖z‖ := by gcongr; exact A.le_opNorm z
      _ = ‖A‖ * ‖z‖ ^ 2 := by ring
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hpsd.nonneg x), hdiag]
  have hz2 : ‖z‖ ^ 2 < ε / (‖A‖ + 1) := by
    have : ‖z‖ < Real.sqrt (ε / (‖A‖ + 1)) := by rw [hz, ← dist_eq_norm]; exact hxw
    calc ‖z‖ ^ 2 < (Real.sqrt (ε / (‖A‖ + 1))) ^ 2 := by gcongr
      _ = _ := Real.sq_sqrt (by positivity)
  calc inner ℝ (cholSeq A u m z) z ≤ ‖A‖ * ‖z‖ ^ 2 := hbound
    _ ≤ ‖A‖ * (ε / (‖A‖ + 1)) := by gcongr
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith


omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma cholC_sq_partial {A : H →L[ℝ] H} (hA : IsPSDOp A) (u : ℕ → H) {ι : Type*}
    (b : HilbertBasis ι ℝ H) (htr : Summable fun i => inner ℝ (A (b i)) (b i)) (m : ℕ) :
    ∑ j ∈ Finset.range m, ‖cholC A u j‖ ^ 2 ≤ ∑' i, inner ℝ (A (b i)) (b i) := by
  have hpar : ∀ c : H, HasSum (fun i => (inner ℝ c (b i)) ^ 2) (‖c‖ ^ 2) := by
    intro c
    have := b.hasSum_inner_mul_inner c c
    simp only [real_inner_self_eq_norm_sq] at this
    convert this using 1
    ext i; rw [real_inner_comm (b i) c]; ring
  have hsum : ∀ j, HasSum (fun i => (inner ℝ (cholC A u j) (b i)) ^ 2) (‖cholC A u j‖ ^ 2) :=
    fun j => hpar _
  have hfin : HasSum (fun i => ∑ j ∈ Finset.range m, (inner ℝ (cholC A u j) (b i)) ^ 2)
      (∑ j ∈ Finset.range m, ‖cholC A u j‖ ^ 2) := hasSum_sum fun j _ => hsum j
  rw [← hfin.tsum_eq]
  refine hfin.summable.tsum_le_tsum (fun i => ?_) htr
  have := cholSeq_sum hA u (b i) (b i) m
  have h2 := (cholSeq_psd hA u m).nonneg (b i)
  have e : ∀ j, (inner ℝ (cholC A u j) (b i)) ^ 2 = inner ℝ (cholC A u j) (b i) * inner ℝ (cholC A u j) (b i) :=
    fun j => sq _
  simp only [e]
  linarith

omit [MeasurableSpace H] [BorelSpace H] in
/-- Rank-one decomposition of a trace-class positive operator. -/
lemma exists_rank_one_decomp {A : H →L[ℝ] H} (hA : IsPSDOp A) {ι : Type*}
    (b : HilbertBasis ι ℝ H) (htr : Summable fun i => inner ℝ (A (b i)) (b i)) :
    ∃ ℓ : ℕ → H, Summable (fun j => ‖ℓ j‖ ^ 2) ∧
      ∀ x y, HasSum (fun j => inner ℝ (ℓ j) x * inner ℝ (ℓ j) y) (inner ℝ (A x) y) := by
  obtain ⟨u, hu⟩ : ∃ u : ℕ → H, Dense (Set.range u) := by
    have : Nonempty H := ⟨0⟩
    exact ⟨TopologicalSpace.denseSeq H, TopologicalSpace.denseRange_denseSeq H⟩
  have hdense : Dense (Submodule.span ℝ (Set.range u) : Set H) :=
    hu.mono Submodule.subset_span
  refine ⟨cholC A u, ?_, ?_⟩
  · refine summable_of_sum_range_le (fun j => sq_nonneg _) (fun m => cholC_sq_partial hA u b htr m)
  · intro x y
    have hsum : Summable (fun j => ‖cholC A u j‖ ^ 2) :=
      summable_of_sum_range_le (fun j => sq_nonneg _) (fun m => cholC_sq_partial hA u b htr m)
    have hs : Summable (fun j => inner ℝ (cholC A u j) x * inner ℝ (cholC A u j) y) := by
      refine Summable.of_norm_bounded (hsum.mul_right (‖x‖ * ‖y‖)) (fun j => ?_)
      rw [norm_mul]
      calc ‖inner ℝ (cholC A u j) x‖ * ‖inner ℝ (cholC A u j) y‖
          ≤ (‖cholC A u j‖ * ‖x‖) * (‖cholC A u j‖ * ‖y‖) := by
            gcongr <;> exact norm_inner_le_norm _ _
        _ = _ := by ring
    refine hs.hasSum_iff_tendsto_nat.mpr ?_
    have hxy : ∀ m, ∑ j ∈ Finset.range m, inner ℝ (cholC A u j) x * inner ℝ (cholC A u j) y =
        inner ℝ (A x) y - inner ℝ (cholSeq A u m x) y := by
      intro m; rw [cholSeq_sum hA u x y m]; ring
    simp_rw [hxy]
    have h0 : Tendsto (fun m => inner ℝ (cholSeq A u m x) y) atTop (𝓝 0) := by
      have hx := cholSeq_tendsto_diag hA u hdense x
      have hy := cholSeq_tendsto_diag hA u hdense y
      have hb : Tendsto (fun m => Real.sqrt (inner ℝ (cholSeq A u m x) x * inner ℝ (cholSeq A u m y) y))
          atTop (𝓝 0) := by
        have := (hx.mul hy)
        rw [zero_mul] at this
        have h2 := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp this
        rw [Real.sqrt_zero] at h2
        exact h2
      refine squeeze_zero_norm (fun m => ?_) hb
      rw [Real.norm_eq_abs]
      exact Real.abs_le_sqrt ((cholSeq_psd hA u m).cs x y)
    simpa using (tendsto_const_nhds (x := inner ℝ (A x) y)).sub h0

end Chol

section L2lim
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma lpNorm_two_sq {f : Ω → H} (hf : MemLp f 2 P) :
    (lpNorm f 2 P) ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂P := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg fun _ => by positivity)]
  norm_num

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- Completeness of `L²`, in the form used for Gaussian series. -/
lemma exists_L2_limit {G : ℕ → Ω → H} (hG : ∀ k, MemLp (G k) 2 P)
    (hcau : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∫ ω, ‖G m ω - G n ω‖ ^ 2 ∂P < ε) :
    ∃ F : Ω → H, MemLp F 2 P ∧ Tendsto (fun k => ∫ ω, ‖G k ω - F ω‖ ^ 2 ∂P) atTop (𝓝 0) := by
  let f : ℕ → Lp H 2 P := fun k => (hG k).toLp (G k)
  have hdist : ∀ m n, dist (f m) (f n) = lpNorm (fun ω => G m ω - G n ω) 2 P := by
    intro m n
    rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
    rfl
  have hcs : CauchySeq f := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcau (ε ^ 2) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [hdist]
    have h1 := hN m hm n hn
    rw [← lpNorm_two_sq (f := fun ω => G m ω - G n ω) ((hG m).sub (hG n))] at h1
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h1
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨F, Lp.memLp F, ?_⟩
  have hd : Tendsto (fun k => dist (f k) F) atTop (𝓝 0) := by
    simpa using (tendsto_iff_dist_tendsto_zero.mp hF)
  have hdist2 : ∀ k, dist (f k) F = lpNorm (fun ω => G k ω - F ω) 2 P := by
    intro k
    rw [dist_eq_norm]
    have hae : (⇑(f k - F)) =ᵐ[P] fun ω => G k ω - F ω := by
      filter_upwards [Lp.coeFn_sub (f k) F, (hG k).coeFn_toLp] with ω h1 h2
      rw [h1]; simp [Pi.sub_apply, h2, f]
    rw [Lp.norm_def, ← toReal_eLpNorm, eLpNorm_congr_ae hae]
  have hsq : ∀ k, ∫ ω, ‖G k ω - F ω‖ ^ 2 ∂P = (dist (f k) F) ^ 2 := by
    intro k
    rw [hdist2, lpNorm_two_sq (f := fun ω => G k ω - F ω) ((hG k).sub (Lp.memLp F))]
  simp_rw [hsq]
  simpa using hd.pow 2
end L2lim

section GaussSeries
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : ℕ → Ω → ℝ}

omit [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] in
lemma gauss_sum_hasLaw (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (hind : iIndepFun g P)
    (a : ℕ → ℝ) (k : ℕ) :
    HasLaw (fun ω => ∑ j ∈ Finset.range k, a j * g j ω)
      (gaussianReal 0 (∑ j ∈ Finset.range k, (NNReal.mk (a j ^ 2) (sq_nonneg _)))) P := by
  have hY : ∀ j, HasLaw (fun ω => a j * g j ω)
      (gaussianReal 0 (NNReal.mk (a j ^ 2) (sq_nonneg _))) P := by
    intro j
    have := gaussianReal_const_mul (hg j) (a j)
    simpa using this
  have hindY : iIndepFun (fun j ω => a j * g j ω) P :=
    hind.comp (fun j x => a j * x) (fun j => by fun_prop)
  induction k with
  | zero =>
    refine ⟨aemeasurable_const, ?_⟩
    simp [gaussianReal_zero_var]
  | succ k ih =>
    have hind2 : IndepFun (fun ω => ∑ j ∈ Finset.range k, a j * g j ω) (fun ω => a k * g k ω) P := by
      have := hindY.indepFun_finsetSum_of_notMem₀ (fun j => (hY j).aemeasurable)
        (s := Finset.range k) (i := k) (by simp)
      convert this using 1
      ext ω; simp
    have := gaussianReal_add_gaussianReal_of_indepFun hind2 ih (hY k)
    simp only [Finset.sum_range_succ]
    refine ⟨ih.aemeasurable.add (hY k).aemeasurable, ?_⟩
    rw [zero_add] at this
    exact this

end GaussSeries

section GaussSeries2
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : ℕ → Ω → ℝ}

omit [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] in
lemma gauss_memLp (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (i : ℕ) : MemLp (g i) 2 P := by
  have := memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp)
  rw [← (hg i).map_eq, memLp_map_measure_iff aestronglyMeasurable_id (hg i).aemeasurable] at this
  exact this

omit [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] in
lemma gauss_integral_mul (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (hind : iIndepFun g P)
    (i j : ℕ) : ∫ ω, g i ω * g j ω ∂P = if i = j then 1 else 0 := by
  have h0 : ∀ i, ∫ ω, g i ω ∂P = 0 := by
    intro i
    have := integral_map (hg i).aemeasurable (f := fun x : ℝ => x) aestronglyMeasurable_id
    rw [(hg i).map_eq, integral_id_gaussianReal] at this
    exact this.symm
  split_ifs with h
  · subst h
    have hm := gauss_memLp hg i
    have := variance_eq_sub hm
    have hv : Var[g i; P] = 1 := by
      have := (hg i).variance_eq
      simpa using this
    rw [hv] at this
    simp only [h0 i] at this
    have h2 : ∫ ω, g i ω * g i ω ∂P = ∫ ω, (g i ^ 2) ω ∂P := by
      congr 1; ext ω; simp [sq]
    rw [h2]; linarith
  · have := (hind.indepFun h).integral_fun_mul_eq_mul_integral (gauss_memLp hg i).aestronglyMeasurable
      (gauss_memLp hg j).aestronglyMeasurable
    rw [this, h0 i]; simp

end GaussSeries2

section GaussSeries3
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : ℕ → Ω → ℝ}

lemma gauss_sum_sq_integral (hg : ∀ i, HasLaw (g i) (gaussianReal 0 1) P) (hind : iIndepFun g P)
    (ℓ : ℕ → H) (F : Finset ℕ) :
    ∫ ω, ‖∑ j ∈ F, g j ω • ℓ j‖ ^ 2 ∂P = ∑ j ∈ F, ‖ℓ j‖ ^ 2 := by
  have e : ∀ ω, ‖∑ j ∈ F, g j ω • ℓ j‖ ^ 2 =
      ∑ i ∈ F, ∑ j ∈ F, (g i ω * g j ω) * inner ℝ (ℓ i) (ℓ j) := by
    intro ω
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  simp_rw [e]
  have hint : ∀ i j, Integrable (fun ω => (g i ω * g j ω) * inner ℝ (ℓ i) (ℓ j)) P :=
    fun i j => ((gauss_memLp hg i).integrable_mul (gauss_memLp hg j)).mul_const _
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  simp_rw [integral_mul_const, gauss_integral_mul hg hind i]
  simp [Finset.sum_ite_eq, hi, real_inner_self_eq_norm_sq]

end GaussSeries3

section CharFunLemmas
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] in
lemma charFun_map_real_eq {X : Ω → ℝ} (hX : AEMeasurable X P) (t : ℝ) :
    charFun (P.map X) t = ∫ ω, Complex.exp (t * X ω * Complex.I) ∂P := by
  rw [charFun_apply_real, integral_map hX]
  exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (t * x * Complex.I)).aestronglyMeasurable

omit [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] in
lemma norm_charFun_sub_le {X Y : Ω → ℝ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hint : Integrable (fun ω => X ω - Y ω) P) (t : ℝ) :
    ‖charFun (P.map X) t - charFun (P.map Y) t‖ ≤ |t| * ∫ ω, |X ω - Y ω| ∂P := by
  rw [charFun_map_real_eq hX, charFun_map_real_eq hY]
  have hbd : ∀ ω, ‖Complex.exp (t * X ω * Complex.I) - Complex.exp (t * Y ω * Complex.I)‖ ≤
      |t| * |X ω - Y ω| := by
    intro ω
    have h1 : Complex.exp (t * X ω * Complex.I) - Complex.exp (t * Y ω * Complex.I) =
        Complex.exp (t * Y ω * Complex.I) *
          (Complex.exp (Complex.I * ((t * (X ω - Y ω) : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, ← Complex.exp_add]
      simp only [mul_one, Complex.ofReal_mul, Complex.ofReal_sub]
      congr 2
      ring
    rw [h1, norm_mul, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
    rw [Real.norm_eq_abs, abs_mul]
  have hi1 : Integrable (fun ω => Complex.exp (t * X ω * Complex.I)) P := by
    refine Integrable.of_bound (C := 1) ?_ ?_
    · exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (t * x * Complex.I)).comp_aestronglyMeasurable hX.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  have hi2 : Integrable (fun ω => Complex.exp (t * Y ω * Complex.I)) P := by
    refine Integrable.of_bound (C := 1) ?_ ?_
    · exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (t * x * Complex.I)).comp_aestronglyMeasurable hY.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  rw [← integral_sub hi1 hi2]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ ω, ‖Complex.exp (t * X ω * Complex.I) - Complex.exp (t * Y ω * Complex.I)‖ ∂P
      ≤ ∫ ω, |t| * |X ω - Y ω| ∂P :=
        integral_mono (hi1.sub hi2).norm (hint.abs.const_mul _) hbd
    _ = _ := by rw [integral_const_mul]

end CharFunLemmas

section GaussSeries4

lemma exists_gauss_series (ℓ : ℕ → H) (hs : Summable fun j => ‖ℓ j‖ ^ 2) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P) (G : Ω → H),
      MemLp G 2 P ∧ ∀ x : H, P.map (fun ω => inner ℝ x (G ω)) =
        gaussianReal 0 (Real.toNNReal (∑' j, (inner ℝ x (ℓ j)) ^ 2)) := by
  obtain ⟨Ω, mΩ, P, g, hgm, hg, hind, hP⟩ := ProbabilityTheory.exists_iid ℕ (gaussianReal 0 1)
  let Gk : ℕ → Ω → H := fun k ω => ∑ j ∈ Finset.range k, g j ω • ℓ j
  have hGk : ∀ k, MemLp (Gk k) 2 P := by
    intro k
    refine memLp_finsetSum (Finset.range k) (fun j _ => ?_)
    exact (ContinuousLinearMap.toSpanSingleton ℝ (ℓ j)).comp_memLp' (gauss_memLp hg j)
  have hdiff : ∀ n m, n ≤ m → ∫ ω, ‖Gk m ω - Gk n ω‖ ^ 2 ∂P =
      ∑ j ∈ Finset.range m, ‖ℓ j‖ ^ 2 - ∑ j ∈ Finset.range n, ‖ℓ j‖ ^ 2 := by
    intro n m hnm
    have : ∀ ω, Gk m ω - Gk n ω = ∑ j ∈ Finset.Ico n m, g j ω • ℓ j := fun ω => by
      simp only [Gk]; rw [Finset.sum_Ico_eq_sub _ hnm]
    simp_rw [this]
    rw [gauss_sum_sq_integral hg hind ℓ, Finset.sum_Ico_eq_sub _ hnm]
  have hcau : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, ∫ ω, ‖Gk m ω - Gk n ω‖ ^ 2 ∂P < ε := by
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
        have h0 : 0 ≤ ∫ ω, ‖Gk m ω - Gk n ω‖ ^ 2 ∂P := integral_nonneg fun _ => by positivity
        linarith)] at this
    · have e : ∫ ω, ‖Gk m ω - Gk n ω‖ ^ 2 ∂P = ∫ ω, ‖Gk n ω - Gk m ω‖ ^ 2 ∂P := by
        congr 1; ext ω; rw [norm_sub_rev]
      rw [e, hdiff m n h]
      have := hN n hn m hm
      have h0 : 0 ≤ ∫ ω, ‖Gk n ω - Gk m ω‖ ^ 2 ∂P := integral_nonneg fun _ => by positivity
      have h1 := hdiff m n h
      rwa [Real.dist_eq, abs_of_nonneg (by linarith)] at this
  obtain ⟨F, hF, hlim⟩ := exists_L2_limit hGk hcau
  refine ⟨Ω, mΩ, P, hP, F, hF, fun x => ?_⟩
  set a : ℕ → ℝ := fun j => inner ℝ x (ℓ j) with ha
  have ha_sum : Summable fun j => (a j) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) (hs.mul_left (‖x‖ ^ 2))
    calc (a j) ^ 2 = |a j| ^ 2 := (sq_abs _).symm
      _ ≤ (‖x‖ * ‖ℓ j‖) ^ 2 := by gcongr; exact abs_real_inner_le_norm x (ℓ j)
      _ = _ := by ring
  set σ2 := ∑' j, (a j) ^ 2 with hσ2
  have hσ : 0 ≤ σ2 := tsum_nonneg fun _ => sq_nonneg _
  have hFm : AEMeasurable F P := hF.aemeasurable
  have hGm : ∀ k, AEMeasurable (Gk k) P := fun k => (hGk k).aemeasurable
  have hinner : ∀ (G : Ω → H), AEMeasurable G P → AEMeasurable (fun ω => inner ℝ x (G ω)) P :=
    fun G hG => (Measurable.comp_aemeasurable (by fun_prop : Measurable fun y : H => inner ℝ x y) hG)
  refine Measure.ext_of_charFun (funext fun t => ?_)
  -- the characteristic functions of the partial sums
  have hu : ∀ k, charFun (P.map fun ω => inner ℝ x (Gk k ω)) t =
      Complex.exp (t * 0 * Complex.I - ((∑ j ∈ Finset.range k, (a j) ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    intro k
    have hlaw := gauss_sum_hasLaw hg hind a k
    have e : (fun ω => inner ℝ x (Gk k ω)) = fun ω => ∑ j ∈ Finset.range k, a j * g j ω := by
      ext ω
      simp only [Gk, inner_sum, real_inner_smul_right, ha]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e, hlaw.map_eq, charFun_gaussianReal]
    congr 2
    push_cast
    simp
  have hv : Tendsto (fun k => ∑ j ∈ Finset.range k, (a j) ^ 2) atTop (𝓝 σ2) :=
    ha_sum.hasSum.tendsto_sum_nat
  let f : ℝ → ℂ := fun v => Complex.exp (t * 0 * Complex.I - (v : ℂ) * (t : ℂ) ^ 2 / 2)
  have hf : Continuous f := by fun_prop
  have hlim1 : Tendsto (fun k => charFun (P.map fun ω => inner ℝ x (Gk k ω)) t) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal σ2)) t)) := by
    simp_rw [hu]
    rw [charFun_gaussianReal, Real.coe_toNNReal _ hσ]
    exact (hf.tendsto σ2).comp hv
  have hlim2 : Tendsto (fun k => charFun (P.map fun ω => inner ℝ x (Gk k ω)) t) atTop
      (𝓝 (charFun (P.map fun ω => inner ℝ x (F ω)) t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun k => |t| * (‖x‖ * Real.sqrt (∫ ω, ‖Gk k ω - F ω‖ ^ 2 ∂P))) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hlim
      rw [Real.sqrt_zero] at this
      simpa using ((this.const_mul ‖x‖).const_mul |t|)
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hb
    have hint : Integrable (fun ω => inner ℝ x (Gk k ω) - inner ℝ x (F ω)) P := by
      have h1 := ((hGk k).sub hF).integrable one_le_two
      refine Integrable.mono' (h1.norm.const_mul ‖x‖) ?_ (Filter.Eventually.of_forall fun ω => ?_)
      · exact ((hinner _ (hGm k)).sub (hinner _ hFm)).aestronglyMeasurable
      · rw [← inner_sub_right, Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _)
    refine (norm_charFun_sub_le (hinner _ (hGm k)) (hinner _ hFm) hint t).trans ?_
    gcongr
    have hL2 : MemLp (fun ω => ‖Gk k ω - F ω‖) 2 P := ((hGk k).sub hF).norm
    calc ∫ ω, |inner ℝ x (Gk k ω) - inner ℝ x (F ω)| ∂P
        ≤ ∫ ω, ‖x‖ * ‖Gk k ω - F ω‖ ∂P := by
          refine integral_mono hint.abs ((hL2.integrable one_le_two).const_mul _) (fun ω => ?_)
          rw [← inner_sub_right]
          exact abs_real_inner_le_norm _ _
      _ = ‖x‖ * ∫ ω, ‖Gk k ω - F ω‖ ∂P := integral_const_mul _ _
      _ ≤ ‖x‖ * Real.sqrt (∫ ω, ‖Gk k ω - F ω‖ ^ 2 ∂P) := by
          gcongr
          exact integral_le_sqrt P hL2
  exact tendsto_nhds_unique hlim2 hlim1
end GaussSeries4

section ExistsGaussian

/-- The operator representing a bounded bilinear form. -/
def formOp (C : H →L[ℝ] H →L[ℝ] ℝ) : H →L[ℝ] H :=
  ((InnerProductSpace.toDual ℝ H).symm : StrongDual ℝ H ≃ₗᵢ[ℝ] H).toContinuousLinearEquiv.toContinuousLinearMap
    ∘L C

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma inner_formOp (C : H →L[ℝ] H →L[ℝ] ℝ) (x y : H) : inner ℝ (formOp C x) y = C x y := by
  simp [formOp, InnerProductSpace.toDual_symm_apply]

lemma exists_gaussian_of_rank_one (ℓ : ℕ → H) (hs : Summable fun j => ‖ℓ j‖ ^ 2) :
    ∃ γ : Measure H, IsProbabilityMeasure γ ∧ IsCenteredGaussian γ ∧
      ∀ x, ProbabilityTheory.covarianceBilin γ x x = ∑' j, (inner ℝ x (ℓ j)) ^ 2 := by
  obtain ⟨Ω, mΩ, P, hP, G, hG, hlaw⟩ := exists_gauss_series ℓ hs
  have hGm : AEMeasurable G P := hG.aemeasurable
  set γ : Measure H := P.map G with hγ
  have hmap : ∀ x : H, γ.map (fun z => inner ℝ x z) =
      gaussianReal 0 (Real.toNNReal (∑' j, (inner ℝ x (ℓ j)) ^ 2)) := by
    intro x
    rw [hγ, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hGm]
    exact hlaw x
  have hmean : ∀ x : H, ∫ z, inner ℝ x z ∂γ = 0 := by
    intro x
    have := integral_map (μ := γ) (φ := fun z => inner ℝ x z) (f := fun y : ℝ => y)
      (by fun_prop) aestronglyMeasurable_id
    rw [hmap x, integral_id_gaussianReal] at this
    exact this.symm
  have hvar : ∀ x : H, Var[fun z => inner ℝ x z; γ] = ∑' j, (inner ℝ x (ℓ j)) ^ 2 := by
    intro x
    have hnn : 0 ≤ ∑' j, (inner ℝ x (ℓ j)) ^ 2 := tsum_nonneg fun _ => sq_nonneg _
    have := variance_map (μ := γ) (X := fun y : ℝ => y) (Y := fun z => inner ℝ x z)
      (by rw [hmap x]; exact aemeasurable_id) (by fun_prop)
    rw [hmap x, variance_fun_id_gaussianReal] at this
    rw [show (fun z => inner ℝ x z) = (fun y : ℝ => y) ∘ (fun z => inner ℝ x z) from rfl, ← this]
    simp [Real.coe_toNNReal _ hnn]
  haveI : IsProbabilityMeasure γ := by rw [hγ]; infer_instance
  have hL2 : MemLp id 2 γ := by
    rw [hγ, memLp_map_measure_iff aestronglyMeasurable_id hGm]; exact hG
  refine ⟨γ, inferInstance, ⟨⟨fun L => ?_⟩, fun L => ?_⟩, fun x => ?_⟩
  · set x := (InnerProductSpace.toDual ℝ H).symm L with hx
    have hLx : ∀ z, L z = inner ℝ x z := fun z => (InnerProductSpace.toDual_symm_apply).symm
    have e : (fun z => L z) = fun z => inner ℝ x z := funext hLx
    have hnn : 0 ≤ ∑' j, (inner ℝ x (ℓ j)) ^ 2 := tsum_nonneg fun _ => sq_nonneg _
    have h1 : ∫ z, L z ∂γ = 0 := by rw [e]; exact hmean x
    have h2 : Var[L; γ] = ∑' j, (inner ℝ x (ℓ j)) ^ 2 := by
      have : (L : H → ℝ) = fun z => inner ℝ x z := e
      rw [this]; exact hvar x
    have e' : γ.map L = γ.map (fun z => inner ℝ x z) := by rw [← e]
    rw [e', hmap x]
    show _ = gaussianReal (∫ z, L z ∂γ) _
    rw [h1, h2]
  · have hLx : ∀ z, L z = inner ℝ ((InnerProductSpace.toDual ℝ H).symm L) z :=
      fun z => (InnerProductSpace.toDual_symm_apply).symm
    have e : (fun z => L z) = fun z => inner ℝ ((InnerProductSpace.toDual ℝ H).symm L) z := funext hLx
    rw [e]; exact hmean _
  · rw [ProbabilityTheory.covarianceBilin_self hL2 x]
    exact hvar x

end ExistsGaussian

end HilbertCLTAux

/-- Existence of the centered Gaussian measure with a prescribed trace-class covariance on a
separable real Hilbert space (external: Kuo, *Gaussian measures in Banach spaces*, Ch. I;
used in Proposition 4.21, source lines 5513-5520, and Example A.17, lines 10469-10472). -/
theorem exists_centeredGaussian_of_traceClass (C : H →L[ℝ] H →L[ℝ] ℝ)
    (hC : IsTraceClassCov C) :
    ∃ γ : Measure H, IsProbabilityMeasure γ ∧ IsCenteredGaussian γ ∧
      ∀ x y, ProbabilityTheory.covarianceBilin γ x y = C x y := by
  obtain ⟨ι, b, htr⟩ := hC.trace
  have hA : HilbertCLTAux.IsPSDOp (HilbertCLTAux.formOp C) :=
    ⟨fun x y => by
      rw [HilbertCLTAux.inner_formOp, real_inner_comm, HilbertCLTAux.inner_formOp, hC.symm],
     fun x => by rw [HilbertCLTAux.inner_formOp]; exact hC.nonneg x⟩
  obtain ⟨ℓ, hs, hsum⟩ := HilbertCLTAux.exists_rank_one_decomp hA b
    (by simpa only [HilbertCLTAux.inner_formOp] using htr)
  obtain ⟨γ, hγ, hcg, hcov⟩ := HilbertCLTAux.exists_gaussian_of_rank_one ℓ hs
  refine ⟨γ, hγ, hcg, fun x y => ?_⟩
  have hdiag : ∀ x, ProbabilityTheory.covarianceBilin γ x x = C x x := by
    intro x
    rw [hcov x]
    have := (hsum x x).tsum_eq
    rw [HilbertCLTAux.inner_formOp] at this
    rw [← this]
    refine tsum_congr fun j => ?_
    rw [real_inner_comm, sq]
  have e1 := hdiag (x + y)
  simp only [map_add, ContinuousLinearMap.add_apply] at e1
  rw [hdiag x, hdiag y, ProbabilityTheory.covarianceBilin_comm y x, hC.symm y x] at e1
  linarith

/-- The covariance form of a centered law with finite second moment is trace class, with
trace `E‖X‖²` (Parseval). -/
theorem isTraceClassCov_covarianceBilin {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → H) (hX : MemLp X 2 P) (hmean : ∫ ω, X ω ∂P = 0) :
    IsTraceClassCov (ProbabilityTheory.covarianceBilin (law P X)) ∧
      ∀ (ι : Type) (b : HilbertBasis ι ℝ H),
        HasSum (fun i => ProbabilityTheory.covarianceBilin (law P X) (b i) (b i))
          (∫ ω, ‖X ω‖ ^ 2 ∂P) := by
  refine ⟨⟨fun x y => ProbabilityTheory.covarianceBilin_comm x y,
    fun x => ProbabilityTheory.covarianceBilin_self_nonneg x, ?_⟩,
    fun ι b => HilbertCLTAux.hasSum_cov_basis P X hX hmean b⟩
  obtain ⟨ι, -, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  exact ⟨ι, b, (HilbertCLTAux.hasSum_cov_basis P X hX hmean b).summable⟩

-- BEGIN W2
namespace HilbertCLTAux
open ProbabilityTheory

section W2
variable {Ω : Type*} [MeasurableSpace Ω]

omit [CompleteSpace H] in
lemma wassersteinE_comm_aux (p : ℝ) (P Q : Measure H) :
    wassersteinE p P Q ≤ wassersteinE p Q P := by
  refine le_iInf fun π => ?_
  have hsw : IsCoupling (π.1.map Prod.swap) P Q := by
    refine ⟨?_, ?_⟩
    · rw [Measure.map_map measurable_fst measurable_swap]
      exact π.2.2
    · rw [Measure.map_map measurable_snd measurable_swap]
      exact π.2.1
  refine (wassersteinE_le_cost (p := p) hsw).trans (le_of_eq ?_)
  congr 1
  have hm : Measurable fun z : H × H => ENNReal.ofReal (‖z.1 - z.2‖ ^ p) :=
    ENNReal.measurable_ofReal.comp (((measurable_fst.sub measurable_snd).norm).pow_const p)
  rw [lintegral_map hm measurable_swap]
  congr 1; ext z
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [norm_sub_rev]

omit [CompleteSpace H] in
lemma wassersteinE_comm (p : ℝ) (P Q : Measure H) : wassersteinE p P Q = wassersteinE p Q P :=
  le_antisymm (wassersteinE_comm_aux p P Q) (wassersteinE_comm_aux p Q P)

omit [CompleteSpace H] [SecondCountableTopology H] in
/-- A coupling with quadratic cost `≤ c` bounds `W₂` by `√c`. -/
lemma wE2_le_of_cost {ρ ν : Measure H} {π : Measure (H × H)} (hπ : IsCoupling π ρ ν) {c : ℝ}
    (hc : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) ∂π ≤ ENNReal.ofReal c) :
    wassersteinE 2 ρ ν ≤ ENNReal.ofReal (Real.sqrt c) := by
  refine (wassersteinE_le_cost (p := 2) hπ).trans ?_
  have h2 : ∀ z : H × H, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2:ℝ)) = ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) := by
    intro z; rw [Real.rpow_two]
  simp only [h2]
  calc _ ≤ (ENNReal.ofReal c) ^ (1 / (2:ℝ)) := ENNReal.rpow_le_rpow hc (by norm_num)
    _ ≤ _ := by
        rcases le_or_gt c 0 with h | h
        · rw [ENNReal.ofReal_of_nonpos h, ENNReal.zero_rpow_of_pos (by norm_num)]
          exact bot_le
        · rw [ENNReal.ofReal_rpow_of_pos h, Real.sqrt_eq_rpow]

end W2

section Quant

lemma f_le_one {L : ℕ} {f : Fin L → H → ℝ} (hf0 : ∀ k x, 0 ≤ f k x) (hf1 : ∀ x, ∑ k, f k x = 1)
    (k : Fin L) (x : H) : f k x ≤ 1 := by
  rw [← hf1 x]
  exact Finset.single_le_sum (f := fun j => f j x) (fun j _ => hf0 j x) (Finset.mem_univ k)

lemma integrable_f {L : ℕ} (ρ : Measure H) [IsProbabilityMeasure ρ] {f : Fin L → H → ℝ}
    (hfm : ∀ k, Measurable (f k)) (hf0 : ∀ k x, 0 ≤ f k x) (hf1 : ∀ x, ∑ k, f k x = 1) (k : Fin L) :
    Integrable (f k) ρ := by
  refine Integrable.of_bound (C := 1) (hfm k).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hf0 k x)]
  exact f_le_one hf0 hf1 k x

lemma quant_coupling {L : ℕ} (ρ : Measure H) [IsProbabilityMeasure ρ] (f : Fin L → H → ℝ)
    (hfm : ∀ k, Measurable (f k)) (hf0 : ∀ k x, 0 ≤ f k x) (hf1 : ∀ x, ∑ k, f k x = 1)
    (a : Fin L → H) :
    IsCoupling (∑ k, (ρ.withDensity (fun x => ENNReal.ofReal (f k x))).map (fun x => (x, a k)))
      ρ (∑ k, ENNReal.ofReal (∫ x, f k x ∂ρ) • Measure.dirac (a k)) := by
  have hmk : ∀ k, Measurable fun x : H => (x, a k) := fun k => measurable_id.prodMk measurable_const
  constructor
  · rw [Measure.map_finset_sum' measurable_fst.aemeasurable]
    have : ∀ k, ((ρ.withDensity (fun x => ENNReal.ofReal (f k x))).map (fun x => (x, a k))).map
        Prod.fst = ρ.withDensity (fun x => ENNReal.ofReal (f k x)) := by
      intro k
      rw [Measure.map_map measurable_fst (hmk k)]
      exact Measure.map_id
    simp_rw [this]
    ext s hs
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    simp_rw [withDensity_apply _ hs]
    rw [← lintegral_finsetSum (μ := ρ.restrict s) Finset.univ
      (f := fun k x => ENNReal.ofReal (f k x)) (fun k _ => (ENNReal.measurable_ofReal.comp (hfm k)))]
    have : ∀ x, ∑ k, ENNReal.ofReal (f k x) = 1 := by
      intro x
      rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hf0 k x), hf1 x, ENNReal.ofReal_one]
    simp_rw [this]
    simp
  · rw [Measure.map_finset_sum' measurable_snd.aemeasurable]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Measure.map_map measurable_snd (hmk k)]
    have : (Prod.snd ∘ fun x : H => (x, a k)) = fun _ => a k := rfl
    rw [this, Measure.map_const, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    congr 1
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_f ρ hfm hf0 hf1 k)
      (Filter.Eventually.of_forall fun x => hf0 k x)]

lemma quant_cost {L : ℕ} (ρ : Measure H) [IsProbabilityMeasure ρ] (f : Fin L → H → ℝ)
    (hfm : ∀ k, Measurable (f k)) (hf0 : ∀ k x, 0 ≤ f k x) (a : Fin L → H) :
    ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2)
      ∂(∑ k, (ρ.withDensity (fun x => ENNReal.ofReal (f k x))).map (fun x => (x, a k))) =
    ∑ k, ∫⁻ x, ENNReal.ofReal (f k x * ‖x - a k‖ ^ 2) ∂ρ := by
  rw [lintegral_finsetSum_measure]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hmk : Measurable fun x : H => (x, a k) := measurable_id.prodMk measurable_const
  have hm : Measurable fun z : H × H => ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (((measurable_fst.sub measurable_snd).norm).pow_const 2)
  rw [lintegral_map hm hmk]
  have hm2 : Measurable fun x : H => ENNReal.ofReal (‖x - a k‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (((measurable_id.sub measurable_const).norm).pow_const 2)
  have := lintegral_withDensity_eq_lintegral_mul ρ (ENNReal.measurable_ofReal.comp (hfm k)) hm2
  simp only
  refine this.trans (lintegral_congr fun x => ?_)
  simp only [Pi.mul_apply, Function.comp]
  rw [ENNReal.ofReal_mul (hf0 k x)]

end Quant

section Discrete2

lemma discrete_w2 {L : ℕ} (z : Fin L → H) (w w' : Fin L → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hw' : ∀ k, 0 ≤ w' k) (hs : ∑ k, w k = 1) (hs' : ∑ k, w' k = 1) (D : ℝ)
    (hD : ∀ k l, ‖z k - z l‖ ≤ D) :
    wassersteinE 2 (∑ k, ENNReal.ofReal (w k) • Measure.dirac (z k))
      (∑ k, ENNReal.ofReal (w' k) • Measure.dirac (z k)) ≤
      ENNReal.ofReal (Real.sqrt (D ^ 2 * ∑ k, |w k - w' k|)) := by
  classical
  set m : Fin L → ℝ := fun k => min (w k) (w' k) with hm
  have hm0 : ∀ k, 0 ≤ m k := fun k => le_min (hw k) (hw' k)
  have hmw : ∀ k, m k ≤ w k := fun k => min_le_left _ _
  have hmw' : ∀ k, m k ≤ w' k := fun k => min_le_right _ _
  set s : ℝ := ∑ k, (w k - m k) with hsdef
  have hs2 : ∑ k, (w' k - m k) = s := by
    simp only [hsdef, Finset.sum_sub_distrib, hs, hs']
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun k _ => sub_nonneg.2 (hmw k)
  set π : Fin L × Fin L → ℝ := fun q =>
    (if q.1 = q.2 then m q.1 else 0) + (w q.1 - m q.1) * (w' q.2 - m q.2) / s with hπ
  have hπ0 : ∀ q, 0 ≤ π q := fun q => by
    simp only [hπ]
    refine add_nonneg (by split_ifs; exacts [hm0 _, le_rfl]) ?_
    exact div_nonneg (mul_nonneg (sub_nonneg.2 (hmw _)) (sub_nonneg.2 (hmw' _))) hs0
  have hrow : ∀ k, ∑ l, π (k, l) = w k := by
    intro k
    simp only [hπ, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, hs2]
    by_cases h : s = 0
    · have : w k - m k = 0 := by
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.2 (hmw j))).1 h k (Finset.mem_univ k)
        exact h1
      have e : m k = w k := by linarith
      simp [e]
    · field_simp; ring
  have hcol : ∀ l, ∑ k, π (k, l) = w' l := by
    intro l
    simp only [hπ, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    have e : ∑ k, (w k - m k) = s := rfl
    rw [e]
    by_cases h : s = 0
    · have : w' l - m l = 0 := by
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.2 (hmw' j))).1
          (hs2.trans h) l (Finset.mem_univ l)
        exact h1
      have e : m l = w' l := by linarith
      simp [e]
    · field_simp; ring
  have hcoup := coupling_sum_dirac z π w w' hπ0 hrow hcol
  refine wE2_le_of_cost hcoup ?_
  have hmeas : Measurable fun x : H × H => ENNReal.ofReal (‖x.1 - x.2‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (((measurable_fst.sub measurable_snd).norm).pow_const 2)
  rw [lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac' _ hmeas, smul_eq_mul]
  simp_rw [← ENNReal.ofReal_mul (hπ0 _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => mul_nonneg (hπ0 q) (sq_nonneg _))]
  refine ENNReal.ofReal_le_ofReal ?_
  -- cost estimate
  have hterm : ∀ q : Fin L × Fin L, π q * ‖z q.1 - z q.2‖ ^ 2 ≤
      D ^ 2 * ((w q.1 - m q.1) * (w' q.2 - m q.2) / s) := by
    intro q
    simp only [hπ]
    by_cases hq : q.1 = q.2
    · rw [show (if q.1 = q.2 then m q.1 else 0) = m q.1 by simp [hq], hq, sub_self, norm_zero]
      have : 0 ≤ (w q.2 - m q.2) * (w' q.2 - m q.2) / s :=
        div_nonneg (mul_nonneg (sub_nonneg.2 (hmw _)) (sub_nonneg.2 (hmw' _))) hs0
      have h2 : 0 ≤ D ^ 2 := sq_nonneg _
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      positivity
    · rw [show (if q.1 = q.2 then m q.1 else 0) = 0 by simp [hq], zero_add]
      have hD2 : ‖z q.1 - z q.2‖ ^ 2 ≤ D ^ 2 := by
        have := hD q.1 q.2
        exact pow_le_pow_left₀ (norm_nonneg _) this 2
      have hnn : 0 ≤ (w q.1 - m q.1) * (w' q.2 - m q.2) / s :=
        div_nonneg (mul_nonneg (sub_nonneg.2 (hmw _)) (sub_nonneg.2 (hmw' _))) hs0
      calc _ ≤ _ := mul_le_mul_of_nonneg_left hD2 hnn
        _ = _ := mul_comm _ _
  have htot : ∑ q : Fin L × Fin L, (w q.1 - m q.1) * (w' q.2 - m q.2) / s ≤ s := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ← Finset.sum_div, hs2, ← Finset.sum_mul]
    have e : ∑ k, (w k - m k) = s := rfl
    rw [e]
    by_cases h : s = 0
    · simp [h]
    · rw [div_le_iff₀ (lt_of_le_of_ne hs0 (Ne.symm h))]
  have hsle : s ≤ ∑ k, |w k - w' k| := by
    refine Finset.sum_le_sum fun k _ => ?_
    have : w k - m k ≤ |w k - w' k| := by
      simp only [hm]
      rcases le_total (w k) (w' k) with h | h
      · rw [min_eq_left h]; simp
      · rw [min_eq_right h]; exact le_abs_self _
    exact this
  calc ∑ q : Fin L × Fin L, π q * ‖z q.1 - z q.2‖ ^ 2
      ≤ ∑ q : Fin L × Fin L, D ^ 2 * ((w q.1 - m q.1) * (w' q.2 - m q.2) / s) :=
        Finset.sum_le_sum fun q _ => hterm q
    _ = D ^ 2 * ∑ q : Fin L × Fin L, (w q.1 - m q.1) * (w' q.2 - m q.2) / s := by
        rw [← Finset.mul_sum]
    _ ≤ D ^ 2 * ∑ k, |w k - w' k| :=
        mul_le_mul_of_nonneg_left (htot.trans hsle) (sq_nonneg _)

end Discrete2

section PU

/-- Plateau bump of radius `δ` about `c i`. -/
def psiF (δ : ℝ) (c : ℕ → H) (i : ℕ) (x : H) : ℝ := max 0 (min 1 (2 - 2 * ‖x - c i‖ / δ))

/-- The tail product `∏_{j<N} (1 - ψ_j)`. -/
def tailF (δ : ℝ) (c : ℕ → H) (N : ℕ) (x : H) : ℝ := ∏ j ∈ Finset.range N, (1 - psiF δ c j x)

/-- The partition-of-unity piece `ψ_k ∏_{j<k}(1-ψ_j)`. -/
def phiF (δ : ℝ) (c : ℕ → H) (k : ℕ) (x : H) : ℝ := psiF δ c k x * tailF δ c k x

/-- The finite partition of unity `φ_0,…,φ_{N-1}, tail_N`. -/
def pF (δ : ℝ) (c : ℕ → H) (N : ℕ) (k : Fin (N + 1)) (x : H) : ℝ :=
  if k.val < N then phiF δ c k.val x else tailF δ c N x

/-- The anchor points `c_0,…,c_{N-1}, 0`. -/
def aF (c : ℕ → H) (N : ℕ) (k : Fin (N + 1)) : H := if k.val < N then c k.val else 0

lemma continuous_psiF (δ : ℝ) (c : ℕ → H) (i : ℕ) : Continuous (psiF δ c i) := by
  unfold psiF; fun_prop

lemma psiF_nonneg (δ : ℝ) (c : ℕ → H) (i : ℕ) (x : H) : 0 ≤ psiF δ c i x := le_max_left _ _

lemma psiF_le_one (δ : ℝ) (c : ℕ → H) (i : ℕ) (x : H) : psiF δ c i x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma psiF_eq_one {δ : ℝ} (hδ : 0 < δ) (c : ℕ → H) (i : ℕ) (x : H) (h : ‖x - c i‖ ≤ δ / 2) :
    psiF δ c i x = 1 := by
  unfold psiF
  have : 1 ≤ 2 - 2 * ‖x - c i‖ / δ := by
    have h1 : 2 * ‖x - c i‖ / δ ≤ 1 := by
      rw [div_le_iff₀ hδ]; nlinarith
    linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

lemma lt_of_psiF_ne_zero {δ : ℝ} (hδ : 0 < δ) (c : ℕ → H) (i : ℕ) (x : H)
    (h : psiF δ c i x ≠ 0) : ‖x - c i‖ < δ := by
  by_contra hc
  rw [not_lt] at hc
  apply h
  unfold psiF
  have : 2 - 2 * ‖x - c i‖ / δ ≤ 0 := by
    have : 2 * ‖x - c i‖ / δ ≥ 2 := by
      rw [ge_iff_le, le_div_iff₀ hδ]; nlinarith
    linarith
  rw [max_eq_left (le_trans (min_le_right _ _) this)]

lemma tailF_nonneg (δ : ℝ) (c : ℕ → H) (N : ℕ) (x : H) : 0 ≤ tailF δ c N x :=
  Finset.prod_nonneg fun j _ => sub_nonneg.2 (psiF_le_one δ c j x)

lemma tailF_le_one (δ : ℝ) (c : ℕ → H) (N : ℕ) (x : H) : tailF δ c N x ≤ 1 :=
  Finset.prod_le_one₀ (fun j _ => sub_nonneg.2 (psiF_le_one δ c j x))
    fun j _ => sub_le_self _ (psiF_nonneg δ c j x)

lemma continuous_tailF (δ : ℝ) (c : ℕ → H) (N : ℕ) : Continuous (tailF δ c N) := by
  unfold tailF
  exact continuous_finsetProd _ fun j _ => continuous_const.sub (continuous_psiF δ c j)

lemma tailF_succ (δ : ℝ) (c : ℕ → H) (N : ℕ) (x : H) :
    tailF δ c (N + 1) x = tailF δ c N x * (1 - psiF δ c N x) := by
  unfold tailF; rw [Finset.prod_range_succ]

lemma tailF_anti (δ : ℝ) (c : ℕ → H) (x : H) : Antitone fun N => tailF δ c N x := by
  refine antitone_nat_of_succ_le fun N => ?_
  rw [tailF_succ]
  have := tailF_nonneg δ c N x
  have := psiF_nonneg δ c N x
  nlinarith

lemma sum_phiF (δ : ℝ) (c : ℕ → H) (N : ℕ) (x : H) :
    ∑ k ∈ Finset.range N, phiF δ c k x + tailF δ c N x = 1 := by
  induction N with
  | zero => simp [tailF]
  | succ n ih =>
    rw [Finset.sum_range_succ, tailF_succ]
    unfold phiF at *
    nlinarith

lemma phiF_nonneg (δ : ℝ) (c : ℕ → H) (k : ℕ) (x : H) : 0 ≤ phiF δ c k x :=
  mul_nonneg (psiF_nonneg δ c k x) (tailF_nonneg δ c k x)

lemma continuous_phiF (δ : ℝ) (c : ℕ → H) (k : ℕ) : Continuous (phiF δ c k) :=
  (continuous_psiF δ c k).mul (continuous_tailF δ c k)

lemma pF_nonneg (δ : ℝ) (c : ℕ → H) (N : ℕ) (k : Fin (N + 1)) (x : H) : 0 ≤ pF δ c N k x := by
  unfold pF; split_ifs
  exacts [phiF_nonneg δ c _ x, tailF_nonneg δ c N x]

lemma continuous_pF (δ : ℝ) (c : ℕ → H) (N : ℕ) (k : Fin (N + 1)) : Continuous (pF δ c N k) := by
  unfold pF; split_ifs
  exacts [continuous_phiF δ c _, continuous_tailF δ c N]

lemma sum_pF (δ : ℝ) (c : ℕ → H) (N : ℕ) (x : H) : ∑ k : Fin (N + 1), pF δ c N k x = 1 := by
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ k : Fin N, pF δ c N k.castSucc x = phiF δ c k.val x := by
    intro k; simp [pF, k.2]
  have h2 : pF δ c N (Fin.last N) x = tailF δ c N x := by simp [pF]
  simp only [h1, h2]
  rw [Fin.sum_univ_eq_sum_range (fun k => phiF δ c k x) N]
  exact sum_phiF δ c N x

lemma tailF_eventually_zero {δ : ℝ} (hδ : 0 < δ) {c : ℕ → H} (hc : DenseRange c) (x : H) :
    ∃ N₀, ∀ N ≥ N₀, tailF δ c N x = 0 := by
  obtain ⟨i, hi⟩ := hc.exists_dist_lt x (half_pos hδ)
  refine ⟨i + 1, fun N hN => ?_⟩
  unfold tailF
  refine Finset.prod_eq_zero (i := i) (Finset.mem_range.2 (by omega)) ?_
  rw [psiF_eq_one hδ c i x (by rw [dist_eq_norm] at hi; exact hi.le), sub_self]

lemma tailF_eq_one_of_far {δ : ℝ} (hδ : 0 < δ) (c : ℕ → H) (N : ℕ) (x : H)
    (h : ∀ j < N, δ ≤ ‖x - c j‖) : tailF δ c N x = 1 := by
  unfold tailF
  refine Finset.prod_eq_one fun j hj => ?_
  have : psiF δ c j x = 0 := by
    by_contra hne
    exact absurd (lt_of_psiF_ne_zero hδ c j x hne) (not_lt.2 (h j (Finset.mem_range.1 hj)))
  rw [this, sub_zero]

lemma norm_le_of_tailF_ne_one {δ : ℝ} (hδ : 0 < δ) (c : ℕ → H) (N : ℕ) (x : H)
    (h : tailF δ c N x ≠ 1) : ‖x‖ ≤ ∑ j ∈ Finset.range N, ‖c j‖ + δ := by
  by_contra hcon
  apply h
  refine tailF_eq_one_of_far hδ c N x fun j hj => ?_
  by_contra hlt
  rw [not_le] at hlt
  apply hcon
  have h1 : ‖x‖ ≤ ‖x - c j‖ + ‖c j‖ := by
    calc ‖x‖ = ‖(x - c j) + c j‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have h2 : ‖c j‖ ≤ ∑ j ∈ Finset.range N, ‖c j‖ :=
    Finset.single_le_sum (f := fun j => ‖c j‖) (fun _ _ => norm_nonneg _) (Finset.mem_range.2 hj)
  linarith

end PU

section QuantW2

lemma measurable_pF (δ : ℝ) (c : ℕ → H) (N : ℕ) (k : Fin (N + 1)) : Measurable (pF δ c N k) :=
  (continuous_pF δ c N k).measurable

/-- The finite quantisation of `ρ`. -/
def quantMeas (δ : ℝ) (c : ℕ → H) (N : ℕ) (ρ : Measure H) : Measure H :=
  ∑ k : Fin (N + 1), ENNReal.ofReal (∫ x, pF δ c N k x ∂ρ) • Measure.dirac (aF c N k)

lemma sum_integral_pF (δ : ℝ) (c : ℕ → H) (N : ℕ) (ρ : Measure H) [IsProbabilityMeasure ρ] :
    ∑ k : Fin (N + 1), ∫ x, pF δ c N k x ∂ρ = 1 := by
  rw [← integral_finsetSum _ (fun k _ => integrable_f ρ (measurable_pF δ c N)
    (pF_nonneg δ c N) (sum_pF δ c N) k)]
  simp only [sum_pF]
  simp

lemma isProb_quantMeas (δ : ℝ) (c : ℕ → H) (N : ℕ) (ρ : Measure H) [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (quantMeas δ c N ρ) := by
  refine ⟨?_⟩
  simp only [quantMeas, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => integral_nonneg (pF_nonneg δ c N k)),
    sum_integral_pF, ENNReal.ofReal_one]

lemma pF_cost_le {δ : ℝ} (hδ : 0 < δ) (c : ℕ → H) (N : ℕ) (x : H) :
    ∑ k : Fin (N + 1), pF δ c N k x * ‖x - aF c N k‖ ^ 2 ≤ δ ^ 2 + tailF δ c N x * ‖x‖ ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ k : Fin N, pF δ c N k.castSucc x * ‖x - aF c N k.castSucc‖ ^ 2
      = phiF δ c k.val x * ‖x - c k.val‖ ^ 2 := by
    intro k; simp [pF, aF, k.2]
  have h2 : pF δ c N (Fin.last N) x * ‖x - aF c N (Fin.last N)‖ ^ 2 = tailF δ c N x * ‖x‖ ^ 2 := by
    simp [pF, aF]
  simp only [h1, h2]
  rw [Fin.sum_univ_eq_sum_range (fun k => phiF δ c k x * ‖x - c k‖ ^ 2) N]
  have hk : ∀ k ∈ Finset.range N, phiF δ c k x * ‖x - c k‖ ^ 2 ≤ phiF δ c k x * δ ^ 2 := by
    intro k _
    by_cases h0 : psiF δ c k x = 0
    · simp [phiF, h0]
    · have hlt := lt_of_psiF_ne_zero hδ c k x h0
      refine mul_le_mul_of_nonneg_left ?_ (phiF_nonneg δ c k x)
      exact pow_le_pow_left₀ (norm_nonneg _) hlt.le 2
  have hs := sum_phiF δ c N x
  have ht := tailF_nonneg δ c N x
  have : ∑ k ∈ Finset.range N, phiF δ c k x ≤ 1 := by linarith
  calc _ ≤ ∑ k ∈ Finset.range N, phiF δ c k x * δ ^ 2 + tailF δ c N x * ‖x‖ ^ 2 := by
        exact add_le_add_left (Finset.sum_le_sum hk) _
    _ = (∑ k ∈ Finset.range N, phiF δ c k x) * δ ^ 2 + tailF δ c N x * ‖x‖ ^ 2 := by
        rw [Finset.sum_mul]
    _ ≤ _ := by
        have := sq_nonneg δ
        nlinarith

lemma integrable_tail_sq {δ : ℝ} (c : ℕ → H) (N : ℕ) (ρ : Measure H)
    (hρ : Integrable (fun x : H => ‖x‖ ^ 2) ρ) :
    Integrable (fun x => tailF δ c N x * ‖x‖ ^ 2) ρ := by
  refine hρ.mono' ((continuous_tailF δ c N).mul (continuous_norm.pow 2)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (tailF_nonneg δ c N x) (sq_nonneg _))]
  exact mul_le_of_le_one_left (sq_nonneg _) (tailF_le_one δ c N x)

lemma wE2_quant_le {δ : ℝ} (hδ : 0 < δ) (c : ℕ → H) (N : ℕ) (ρ : Measure H)
    [IsProbabilityMeasure ρ] (hρ : Integrable (fun x : H => ‖x‖ ^ 2) ρ) :
    wassersteinE 2 ρ (quantMeas δ c N ρ) ≤
      ENNReal.ofReal (Real.sqrt (δ ^ 2 + ∫ x, tailF δ c N x * ‖x‖ ^ 2 ∂ρ)) := by
  refine wE2_le_of_cost (quant_coupling ρ (pF δ c N) (measurable_pF δ c N) (pF_nonneg δ c N)
    (sum_pF δ c N) (aF c N)) ?_
  rw [quant_cost ρ (pF δ c N) (measurable_pF δ c N) (pF_nonneg δ c N) (aF c N)]
  have hm : ∀ k : Fin (N + 1), Measurable fun x : H => pF δ c N k x * ‖x - aF c N k‖ ^ 2 :=
    fun k => (measurable_pF δ c N k).mul (((measurable_id.sub measurable_const).norm).pow_const 2)
  have hnn : ∀ k : Fin (N + 1), ∀ x : H, 0 ≤ pF δ c N k x * ‖x - aF c N k‖ ^ 2 :=
    fun k x => mul_nonneg (pF_nonneg δ c N k x) (sq_nonneg _)
  rw [← lintegral_finsetSum (μ := ρ) Finset.univ
    (f := fun k x => ENNReal.ofReal (pF δ c N k x * ‖x - aF c N k‖ ^ 2))
    (fun k _ => ENNReal.measurable_ofReal.comp (hm k))]
  have hint : Integrable (fun x => δ ^ 2 + tailF δ c N x * ‖x‖ ^ 2) ρ :=
    (integrable_const _).add (integrable_tail_sq c N ρ hρ)
  calc ∫⁻ x, ∑ k : Fin (N + 1), ENNReal.ofReal (pF δ c N k x * ‖x - aF c N k‖ ^ 2) ∂ρ
      = ∫⁻ x, ENNReal.ofReal (∑ k : Fin (N + 1), pF δ c N k x * ‖x - aF c N k‖ ^ 2) ∂ρ := by
        refine lintegral_congr fun x => ?_
        rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hnn k x)]
    _ ≤ ∫⁻ x, ENNReal.ofReal (δ ^ 2 + tailF δ c N x * ‖x‖ ^ 2) ∂ρ :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (pF_cost_le hδ c N x)
    _ = ENNReal.ofReal (∫ x, (δ ^ 2 + tailF δ c N x * ‖x‖ ^ 2) ∂ρ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        exact Filter.Eventually.of_forall fun x =>
          add_nonneg (sq_nonneg _) (mul_nonneg (tailF_nonneg δ c N x) (sq_nonneg _))
    _ = _ := by
        rw [integral_add (integrable_const _) (integrable_tail_sq c N ρ hρ)]
        simp

end QuantW2

section W2conv

lemma tendsto_integral_bdd {μn : ℕ → ProbabilityMeasure H} {μ : ProbabilityMeasure H}
    (hweak : Tendsto μn atTop (𝓝 μ)) {f : H → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun n => ∫ x, f x ∂(μn n : Measure H)) atTop (𝓝 (∫ x, f x ∂(μ : Measure H))) :=
  (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hweak)
    (BoundedContinuousFunction.ofNormedAddCommGroup f hf C hC)

lemma lintegral_sq_eq (ρ : Measure H) :
    ∫⁻ x, ‖x‖ₑ ^ 2 ∂ρ = ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂ρ := by
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

lemma integrable_sq_of_lintegral_lt_top (ρ : Measure H) (h : ∫⁻ x, ‖x‖ₑ ^ 2 ∂ρ < ⊤) :
    Integrable (fun x : H => ‖x‖ ^ 2) ρ := by
  rw [lintegral_sq_eq] at h
  exact (lintegral_ofReal_ne_top_iff_integrable (continuous_norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => sq_nonneg _)).1 h.ne

lemma integral_sq_eq_toReal (ρ : Measure H) :
    ∫ x, ‖x‖ ^ 2 ∂ρ = (∫⁻ x, ‖x‖ₑ ^ 2 ∂ρ).toReal := by
  rw [lintegral_sq_eq]
  exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (continuous_norm.pow 2).aestronglyMeasurable

/-- The cut-off second moment `(1 - tail_N)‖x‖²` is bounded. -/
lemma Qsq_bound {δ : ℝ} (hδ : 0 < δ) (c : ℕ → H) (N : ℕ) (x : H) :
    ‖(1 - tailF δ c N x) * ‖x‖ ^ 2‖ ≤ (∑ j ∈ Finset.range N, ‖c j‖ + δ) ^ 2 := by
  have h1 := tailF_le_one δ c N x
  have h0 := tailF_nonneg δ c N x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.2 h1) (sq_nonneg _))]
  by_cases h : tailF δ c N x = 1
  · rw [h]; simp; positivity
  · have := norm_le_of_tailF_ne_one hδ c N x h
    calc (1 - tailF δ c N x) * ‖x‖ ^ 2 ≤ 1 * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ ≤ _ := by
          rw [one_mul]; exact pow_le_pow_left₀ (norm_nonneg _) this 2

lemma tail_integral_tendsto {δ : ℝ} (hδ : 0 < δ) {c : ℕ → H} (hc : DenseRange c) (ρ : Measure H)
    (hρ : Integrable (fun x : H => ‖x‖ ^ 2) ρ) :
    Tendsto (fun N => ∫ x, tailF δ c N x * ‖x‖ ^ 2 ∂ρ) atTop (𝓝 0) := by
  have := tendsto_integral_of_dominated_convergence (μ := ρ)
    (F := fun N x => tailF δ c N x * ‖x‖ ^ 2) (f := fun _ => (0:ℝ))
    (bound := fun x => ‖x‖ ^ 2)
    (fun N => ((continuous_tailF δ c N).mul (continuous_norm.pow 2)).aestronglyMeasurable) hρ
    (fun N => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (tailF_nonneg δ c N x) (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) (tailF_le_one δ c N x))
    (Filter.Eventually.of_forall fun x => by
      obtain ⟨N₀, hN₀⟩ := tailF_eventually_zero hδ hc x
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
      rw [hN₀ N hN, zero_mul])
  simpa using this

end W2conv

section W2main

lemma tendsto_integral_tail {δ : ℝ} (hδ : 0 < δ) (c : ℕ → H) (N : ℕ)
    {μn : ℕ → ProbabilityMeasure H} {μ : ProbabilityMeasure H}
    (hweak : Tendsto μn atTop (𝓝 μ))
    (hint : ∀ᶠ n in atTop, Integrable (fun x : H => ‖x‖ ^ 2) (μn n : Measure H))
    (hμ : Integrable (fun x : H => ‖x‖ ^ 2) (μ : Measure H))
    (hm : Tendsto (fun n => ∫ x, ‖x‖ ^ 2 ∂(μn n : Measure H)) atTop
      (𝓝 (∫ x, ‖x‖ ^ 2 ∂(μ : Measure H)))) :
    Tendsto (fun n => ∫ x, tailF δ c N x * ‖x‖ ^ 2 ∂(μn n : Measure H)) atTop
      (𝓝 (∫ x, tailF δ c N x * ‖x‖ ^ 2 ∂(μ : Measure H))) := by
  set R : ℝ := (∑ j ∈ Finset.range N, ‖c j‖ + δ) ^ 2
  have hQc : Continuous fun x : H => (1 - tailF δ c N x) * ‖x‖ ^ 2 :=
    (continuous_const.sub (continuous_tailF δ c N)).mul (continuous_norm.pow 2)
  have hQ := tendsto_integral_bdd hweak hQc (Qsq_bound hδ c N)
  have hQi : ∀ ρ : Measure H, IsProbabilityMeasure ρ →
      Integrable (fun x : H => (1 - tailF δ c N x) * ‖x‖ ^ 2) ρ := fun ρ _ =>
    Integrable.of_bound (C := R) hQc.aestronglyMeasurable
      (Filter.Eventually.of_forall (Qsq_bound hδ c N))
  have heq : ∀ ρ : Measure H, IsProbabilityMeasure ρ → Integrable (fun x : H => ‖x‖ ^ 2) ρ →
      ∫ x, tailF δ c N x * ‖x‖ ^ 2 ∂ρ =
        ∫ x, ‖x‖ ^ 2 ∂ρ - ∫ x, (1 - tailF δ c N x) * ‖x‖ ^ 2 ∂ρ := by
    intro ρ hρ hi
    rw [← integral_sub hi (hQi ρ hρ)]
    congr 1; ext x; ring
  have h1 := hm.sub hQ
  rw [← heq (μ : Measure H) inferInstance hμ] at h1
  refine h1.congr' ?_
  filter_upwards [hint] with n hn
  exact (heq (μn n : Measure H) inferInstance hn).symm

theorem wE2_tendsto_aux (μn : ℕ → ProbabilityMeasure H) (μ : ProbabilityMeasure H)
    (hweak : Tendsto μn atTop (𝓝 μ))
    (hfin : ∫⁻ x, ‖x‖ₑ ^ 2 ∂(μ : Measure H) < ∞)
    (hmom : Tendsto (fun n => ∫⁻ x, ‖x‖ₑ ^ 2 ∂(μn n : Measure H)) atTop
      (𝓝 (∫⁻ x, ‖x‖ₑ ^ 2 ∂(μ : Measure H)))) :
    Tendsto (fun n => wassersteinE 2 (μn n : Measure H) (μ : Measure H)) atTop (𝓝 0) := by
  have hμ := integrable_sq_of_lintegral_lt_top _ hfin
  have hint : ∀ᶠ n in atTop, Integrable (fun x : H => ‖x‖ ^ 2) (μn n : Measure H) := by
    filter_upwards [hmom.eventually (gt_mem_nhds hfin)] with n hn
    exact integrable_sq_of_lintegral_lt_top _ hn
  have hm : Tendsto (fun n => ∫ x, ‖x‖ ^ 2 ∂(μn n : Measure H)) atTop
      (𝓝 (∫ x, ‖x‖ ^ 2 ∂(μ : Measure H))) := by
    simp only [integral_sq_eq_toReal]
    exact (ENNReal.tendsto_toReal hfin.ne).comp hmom
  obtain c := TopologicalSpace.denseSeq H
  set c : ℕ → H := TopologicalSpace.denseSeq H with hcdef
  have hc : DenseRange c := TopologicalSpace.denseRange_denseSeq H
  have key : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      wassersteinE 2 (μn n : Measure H) (μ : Measure H) ≤ ENNReal.ofReal η := by
    intro η hη
    set δ : ℝ := η / 6 with hδdef
    have hδ : 0 < δ := by positivity
    have hr := tail_integral_tendsto hδ hc (μ : Measure H) hμ
    obtain ⟨N, hN⟩ := (hr.eventually (gt_mem_nhds (show (0:ℝ) < η ^ 2 / 36 by positivity))).exists
    have hrn := tendsto_integral_tail hδ c N hweak hint hμ hm
    have hev1 : ∀ᶠ n in atTop, ∫ x, tailF δ c N x * ‖x‖ ^ 2 ∂(μn n : Measure H) < η ^ 2 / 12 :=
      hrn.eventually (gt_mem_nhds (by have : (0:ℝ) < η ^ 2 := by positivity
                                      linarith))
    -- discrete weights
    set a : Fin (N + 1) → H := aF c N with hadef
    set D : ℝ := 2 * ∑ k, ‖a k‖ with hD
    have hDk : ∀ k l, ‖a k - a l‖ ≤ D := by
      intro k l
      have h1 : ‖a k‖ ≤ ∑ j, ‖a j‖ :=
        Finset.single_le_sum (f := fun j => ‖a j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
      have h2 : ‖a l‖ ≤ ∑ j, ‖a j‖ :=
        Finset.single_le_sum (f := fun j => ‖a j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ l)
      calc ‖a k - a l‖ ≤ ‖a k‖ + ‖a l‖ := norm_sub_le _ _
        _ ≤ D := by rw [hD]; linarith
    have hw : ∀ k, Tendsto (fun n => ∫ x, pF δ c N k x ∂(μn n : Measure H)) atTop
        (𝓝 (∫ x, pF δ c N k x ∂(μ : Measure H))) := fun k =>
      tendsto_integral_bdd hweak (continuous_pF δ c N k) (C := 1) (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pF_nonneg δ c N k x)]
        exact f_le_one (pF_nonneg δ c N) (sum_pF δ c N) k x)
    have hS : Tendsto (fun n => ∑ k, |∫ x, pF δ c N k x ∂(μn n : Measure H) -
        ∫ x, pF δ c N k x ∂(μ : Measure H)|) atTop (𝓝 0) := by
      have := tendsto_finsetSum Finset.univ (fun k _ => ((hw k).sub_const
        (∫ x, pF δ c N k x ∂(μ : Measure H))).abs)
      simpa using this
    have hev2 : ∀ᶠ n in atTop, D ^ 2 * ∑ k, |∫ x, pF δ c N k x ∂(μn n : Measure H) -
        ∫ x, pF δ c N k x ∂(μ : Measure H)| < (η / 3) ^ 2 := by
      have := (hS.const_mul (D ^ 2))
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    filter_upwards [hev1, hev2, hint] with n h1 h2 hi
    have : IsProbabilityMeasure (μn n : Measure H) := inferInstance
    have := isProb_quantMeas δ c N (μn n : Measure H)
    have := isProb_quantMeas δ c N (μ : Measure H)
    have e1 := wE2_quant_le hδ c N (μn n : Measure H) hi
    have e3 := wE2_quant_le hδ c N (μ : Measure H) hμ
    have e2 := discrete_w2 a (fun k => ∫ x, pF δ c N k x ∂(μn n : Measure H))
      (fun k => ∫ x, pF δ c N k x ∂(μ : Measure H))
      (fun k => integral_nonneg (pF_nonneg δ c N k)) (fun k => integral_nonneg (pF_nonneg δ c N k))
      (sum_integral_pF δ c N _) (sum_integral_pF δ c N _) D hDk
    have hsq : ∀ t : ℝ, t ≤ (η / 3) ^ 2 → ENNReal.ofReal (Real.sqrt t) ≤ ENNReal.ofReal (η / 3) := by
      intro t ht
      exact ENNReal.ofReal_le_ofReal ((Real.sqrt_le_left (by positivity)).2 ht)
    have b1 := e1.trans (hsq _ (by nlinarith))
    have hr' : ∫ x, tailF δ c N x * ‖x‖ ^ 2 ∂(μ : Measure H) < η ^ 2 / 36 := hN
    have b3 := e3.trans (hsq _ (by nlinarith))
    have b2 := e2.trans (hsq _ h2.le)
    have t1 := wassersteinE_triangle 2 (by norm_num) (μn n : Measure H) (quantMeas δ c N (μn n)) (μ : Measure H)
    have t2 := wassersteinE_triangle 2 (by norm_num) (quantMeas δ c N (μn n : Measure H))
      (quantMeas δ c N (μ : Measure H)) (μ : Measure H)
    rw [wassersteinE_comm] at b3
    calc _ ≤ _ := t1
      _ ≤ wassersteinE 2 (μn n : Measure H) (quantMeas δ c N (μn n)) +
          (wassersteinE 2 (quantMeas δ c N (μn n : Measure H)) (quantMeas δ c N (μ : Measure H)) +
            wassersteinE 2 (quantMeas δ c N (μ : Measure H)) (μ : Measure H)) :=
          add_le_add le_rfl t2
      _ ≤ ENNReal.ofReal (η / 3) + (ENNReal.ofReal (η / 3) + ENNReal.ofReal (η / 3)) :=
          add_le_add b1 (add_le_add b2 b3)
      _ = ENNReal.ofReal η := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases htop : ε = ⊤
  · exact Filter.Eventually.of_forall fun n => htop ▸ le_top
  · have := key ε.toReal (ENNReal.toReal_pos hε.ne' htop)
    rwa [ENNReal.ofReal_toReal htop] at this

end W2main

end HilbertCLTAux
-- END W2

-- BEGIN CLT
namespace HilbertCLTAux
open ProbabilityTheory

section WeakApprox
open scoped BoundedContinuousFunction

lemma lip_tail_bound (ρ : Measure H) [IsProbabilityMeasure ρ] (K : Submodule ℝ H)
    [K.HasOrthogonalProjection] {f : H → ℝ} {C : ℝ} (hC : ∀ x y, dist (f x) (f y) ≤ C) {L : ℝ≥0}
    (hL : LipschitzWith L f)
    (hint : Integrable (fun x : H => ‖x - K.starProjection x‖) ρ) :
    |∫ x, f x ∂ρ - ∫ x, f (K.starProjection x) ∂ρ| ≤ L * ∫ x, ‖x - K.starProjection x‖ ∂ρ := by
  have hfc : Continuous f := hL.continuous
  have hbd : ∀ x, ‖f x‖ ≤ ‖f 0‖ + C := fun x => by
    have := hC x 0
    rw [Real.dist_eq] at this
    calc ‖f x‖ = ‖f x - f 0 + f 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖f x - f 0‖ + ‖f 0‖ := norm_add_le _ _
      _ ≤ _ := by rw [Real.norm_eq_abs]; linarith
  have hi1 : Integrable f ρ := Integrable.of_bound (C := ‖f 0‖ + C) hfc.aestronglyMeasurable
    (Filter.Eventually.of_forall hbd)
  have hi2 : Integrable (fun x => f (K.starProjection x)) ρ :=
    Integrable.of_bound (C := ‖f 0‖ + C)
      (hfc.comp (K.starProjection).continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hbd _)
  rw [← integral_sub hi1 hi2, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans ?_
  refine integral_mono (hi1.sub hi2).abs (hint.const_mul _) fun x => ?_
  have := hL.dist_le_mul x (K.starProjection x)
  rw [Real.dist_eq, dist_eq_norm] at this
  simpa using this

lemma tendsto_of_approx (μN : ℕ → ProbabilityMeasure H) (γ : ProbabilityMeasure H)
    (h : ∀ η : ℝ, 0 < η → ∃ (K : Submodule ℝ H) (_ : K.HasOrthogonalProjection),
      (∀ᶠ N in atTop, Integrable (fun x : H => ‖x - K.starProjection x‖) (μN N : Measure H) ∧
        ∫ x, ‖x - K.starProjection x‖ ∂(μN N : Measure H) ≤ η) ∧
      Integrable (fun x : H => ‖x - K.starProjection x‖) (γ : Measure H) ∧
        ∫ x, ‖x - K.starProjection x‖ ∂(γ : Measure H) ≤ η ∧
      ∀ g : K →ᵇ ℝ, Tendsto (fun N => ∫ x, g (K.orthogonalProjectionOnto x) ∂(μN N : Measure H))
        atTop (𝓝 (∫ x, g (K.orthogonalProjectionOnto x) ∂(γ : Measure H)))) :
    Tendsto μN atTop (𝓝 γ) := by
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro f ⟨C, hC⟩ ⟨L, hL⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hK, hev, hγi, hγη, hfd⟩ := h (ε / (4 * (L + 1))) (by positivity)
  have hKc : Continuous fun k : K => f (k : H) := hL.continuous.comp continuous_subtype_val
  let g : K →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨fun k : K => f (k : H), hKc⟩ C
    (fun x y => hC _ _)
  have hg : ∀ x, g (K.orthogonalProjectionOnto x) = f (K.starProjection x) := fun x => by
    show f ((K.orthogonalProjectionOnto x : K) : H) = f (K.starProjection x)
    rw [Submodule.starProjection_apply]
  have hfd' := hfd g
  simp_rw [hg] at hfd'
  have hLη : (L : ℝ) * (ε / (4 * (L + 1))) ≤ ε / 4 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hε, L.2]
  have h3 := (Metric.tendsto_nhds.1 hfd') (ε / 4) (by positivity)
  filter_upwards [hev, h3] with N ⟨hNi, hNη⟩ hN3
  have b1 := lip_tail_bound (μN N : Measure H) K hC hL hNi
  have b2 := lip_tail_bound (γ : Measure H) K hC hL hγi
  have hL0 : (0 : ℝ) ≤ L := L.2
  have b1' : |∫ x, f x ∂(μN N : Measure H) - ∫ x, f (K.starProjection x) ∂(μN N : Measure H)| ≤ ε / 4 :=
    b1.trans ((mul_le_mul_of_nonneg_left hNη hL0).trans hLη)
  have b2' : |∫ x, f x ∂(γ : Measure H) - ∫ x, f (K.starProjection x) ∂(γ : Measure H)| ≤ ε / 4 :=
    b2.trans ((mul_le_mul_of_nonneg_left hγη hL0).trans hLη)
  rw [Real.dist_eq] at hN3 ⊢
  rw [abs_lt] at hN3 ⊢
  rw [abs_le] at b1' b2'
  constructor <;> linarith [hN3.1, hN3.2, b1'.1, b1'.2, b2'.1, b2'.2]

end WeakApprox

section L2sum
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma integrable_inner_of_memLp2 {S Y : Ω → H} (hS : MemLp S 2 P) (hY : MemLp Y 2 P) :
    Integrable (fun ω => inner ℝ (S ω) (Y ω)) P := by
  have h2S := integrable_sq_norm_of_memLp2 hS
  have h2Y := integrable_sq_norm_of_memLp2 hY
  refine Integrable.mono' (h2S.fun_add h2Y) ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (hS.aestronglyMeasurable.inner hY.aestronglyMeasurable)
  · calc ‖inner ℝ (S ω) (Y ω)‖ ≤ ‖S ω‖ * ‖Y ω‖ := norm_inner_le_norm _ _
      _ ≤ ‖S ω‖ ^ 2 + ‖Y ω‖ ^ 2 := by
          nlinarith [norm_nonneg (S ω), norm_nonneg (Y ω), sq_nonneg (‖S ω‖ - ‖Y ω‖)]

lemma integral_sq_add2 {S Y : Ω → H} (hind : IndepFun S Y P) (hS : MemLp S 2 P) (hY : MemLp Y 2 P)
    (hY0 : ∫ ω, Y ω ∂P = 0) :
    ∫ ω, ‖S ω + Y ω‖ ^ 2 ∂P = ∫ ω, ‖S ω‖ ^ 2 ∂P + ∫ ω, ‖Y ω‖ ^ 2 ∂P := by
  have hSi : Integrable S P := hS.integrable (by norm_num)
  have hYi : Integrable Y P := hY.integrable (by norm_num)
  have h2S := integrable_sq_norm_of_memLp2 hS
  have h2Y := integrable_sq_norm_of_memLp2 hY
  have hc := integrable_inner_of_memLp2 hS hY
  have : ∀ ω, ‖S ω + Y ω‖ ^ 2 = ‖S ω‖ ^ 2 + ‖Y ω‖ ^ 2 + 2 * inner ℝ (S ω) (Y ω) := by
    intro ω; rw [norm_add_sq_real]; ring
  simp_rw [this]
  rw [integral_add (h2S.fun_add h2Y) (hc.const_mul 2), integral_add h2S h2Y, integral_const_mul,
    integral_inner_indep hind hSi hYi hY0]
  ring

lemma iid_L2_sum {X : ℕ → Ω → H} (hiid : IsIIDCopies P X) (hL2 : MemLp (X 0) 2 P)
    (hm : ∀ i, AEMeasurable (X i) P) (hmean : ∫ ω, X 0 ω ∂P = 0) (n : ℕ) :
    MemLp (fun ω => ∑ i ∈ Finset.range n, X i ω) 2 P ∧
    ∫ ω, ‖∑ i ∈ Finset.range n, X i ω‖ ^ 2 ∂P = n * ∫ ω, ‖X 0 ω‖ ^ 2 ∂P ∧
    ∫ ω, ∑ i ∈ Finset.range n, X i ω ∂P = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hM, h2, h0⟩ := ih
    obtain ⟨hMn, hIn, hKn⟩ := iid_memLp_integral hiid hL2 hm n
    have hind : IndepFun (fun ω => ∑ i ∈ Finset.range n, X i ω) (X n) P := by
      have := hiid.1.indepFun_finsetSum_of_notMem₀ hm (s := Finset.range n) (i := n) (by simp)
      convert this using 1
      ext ω; simp
    simp only [Finset.sum_range_succ]
    refine ⟨hM.add hMn, ?_, ?_⟩
    · rw [integral_sq_add2 hind hM hMn (by rw [hIn, hmean]), h2, hKn 2]; push_cast; ring
    · rw [integral_add (hM.integrable (by norm_num)) (hMn.integrable (by norm_num)), h0, hIn, hmean]
      simp

/-- Composing an i.i.d. family with a continuous linear map keeps it i.i.d. -/
lemma iid_comp_clm {X : ℕ → Ω → H} (hiid : IsIIDCopies P X) (hm : ∀ i, AEMeasurable (X i) P)
    (A : H →L[ℝ] H) : IsIIDCopies P (fun i ω => A (X i ω)) := by
  refine ⟨hiid.1.comp (fun _ => A) (fun _ => A.continuous.measurable), fun i j => ?_⟩
  have h : ∀ k, law P (fun ω => A (X k ω)) = (law P (X k)).map A := fun k =>
    (AEMeasurable.map_map_of_aemeasurable A.continuous.aemeasurable (hm k)).symm
  rw [h i, h j, hiid.2 i j]

end L2sum

section FDCLT
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma aemeasurable_normalizedSum {X : ℕ → Ω → H} (hm : ∀ i, AEMeasurable (X i) P) (N : ℕ) :
    AEMeasurable (normalizedSum X N) P := by
  unfold normalizedSum
  exact (Finset.aemeasurable_fun_sum _ fun i _ => hm i).const_smul _

lemma charFun_normalizedSum_tendsto {X : ℕ → Ω → H} (hiid : IsIIDCopies P X)
    (hL2 : MemLp (X 0) 2 P) (hm : ∀ i, AEMeasurable (X i) P) (hmean : ∫ ω, X 0 ω ∂P = 0) (t : H) :
    Tendsto (fun N => charFun (law P (normalizedSum X N)) t) atTop
      (𝓝 (Complex.exp (-(ProbabilityTheory.covarianceBilin (law P (X 0)) t t : ℂ) / 2))) := by
  set Y : ℕ → Ω → ℝ := fun k ω => inner ℝ t (X k ω) with hY
  have hmY : ∀ k, AEMeasurable (Y k) P := fun k =>
    (innerSL ℝ t).continuous.measurable.comp_aemeasurable (hm k)
  have hindep : iIndepFun Y P :=
    hiid.1.comp (fun _ x => inner ℝ t x) (fun _ => (innerSL ℝ t).continuous.measurable)
  have hident : ∀ k, IdentDistrib (Y k) (Y 0) P P := fun k =>
    (identDistrib_of_iid hiid hL2.aemeasurable hm k).comp (u := fun x => inner ℝ t x)
      (innerSL ℝ t).continuous.measurable
  have hLY : MemLp (Y 0) 2 P := (innerSL ℝ t).comp_memLp' hL2
  have hmeanY : P[Y 0] = 0 := by
    show ∫ ω, inner ℝ t (X 0 ω) ∂P = 0
    rw [integral_inner (hL2.integrable (by norm_num)), hmean]; simp
  have hvar : Var[Y 0; P] = ProbabilityTheory.covarianceBilin (law P (X 0)) t t := by
    rw [variance_of_integral_eq_zero (hmY 0) hmeanY,
      covarianceBilin_law_self P (X 0) hL2 hmean t]
  have hCLT := tendstoInDistribution_inv_sqrt_mul_sum_sub (X := Y) (P := P)
    (Y := (id : ℝ → ℝ)) (P' := gaussianReal 0 Var[Y 0; P].toNNReal)
    (HasLaw.id) hLY hindep hident
  have h1 := hCLT.tendsto_charFun 1
  rw [hmeanY] at h1
  simp only [Measure.map_id, charFun_gaussianReal] at h1
  have hc : Complex.exp (((1:ℝ):ℂ) * ((0:ℝ):ℂ) * Complex.I - ((Var[Y 0; P].toNNReal : ℝ≥0) : ℂ) * ((1:ℝ):ℂ) ^ 2 / 2)
      = Complex.exp (-(ProbabilityTheory.covarianceBilin (law P (X 0)) t t : ℂ) / 2) := by
    congr 1
    have hnn : (0:ℝ) ≤ Var[Y 0; P] := variance_nonneg _ _
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, Complex.ofReal_one, one_pow,
      mul_one]
    rw [← hvar]
    have : ((Var[Y 0; P].toNNReal : ℝ≥0) : ℂ) = ((Var[Y 0; P] : ℝ) : ℂ) := by
      simp [Real.coe_toNNReal _ hnn]
    rw [this]; ring
  rw [hc] at h1
  refine h1.congr fun N => ?_
  rw [charFun_map_eq_charFun_map_inner_one (aemeasurable_normalizedSum hm N) t]
  congr 2
  funext ω
  simp only [hY, normalizedSum, mul_zero, sub_zero, inner_smul_left, sum_inner,
    RCLike.conj_to_real]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_comm]

end FDCLT

section FDCLT2
open scoped BoundedContinuousFunction

lemma gaussian_mean_zero {γ : Measure H} (hγ : IsCenteredGaussian γ) : γ[id] = 0 := by
  have := hγ.1
  refine ext_inner_left ℝ fun t => ?_
  rw [inner_zero_right]
  have h := hγ.2 (innerSL ℝ t)
  simp only [innerSL_apply_apply] at h
  rw [← h, ← integral_inner IsGaussian.integrable_id]
  rfl

lemma charFun_centered_gaussian {γ : Measure H} (hγ : IsCenteredGaussian γ) (t : H) :
    charFun γ t = Complex.exp (-(ProbabilityTheory.covarianceBilin γ t t : ℂ) / 2) := by
  have := hγ.1
  rw [IsGaussian.charFun_eq', gaussian_mean_zero hγ]
  simp [neg_div]

lemma charFun_map_proj (μ : Measure H) (K : Submodule ℝ H) [K.HasOrthogonalProjection] (t : K) :
    charFun (μ.map K.orthogonalProjectionOnto) t = charFun μ (t : H) := by
  rw [charFun_apply, charFun_apply, integral_map (K.orthogonalProjectionOnto.continuous.aemeasurable)
    (by fun_prop)]
  simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma fd_clt {X : ℕ → Ω → H} (hiid : IsIIDCopies P X) (hL2 : MemLp (X 0) 2 P)
    (hm : ∀ i, AEMeasurable (X i) P) (hmean : ∫ ω, X 0 ω ∂P = 0) {γ : Measure H}
    (hγ : IsCenteredGaussian γ)
    (hcov : ∀ x y, ProbabilityTheory.covarianceBilin γ x y =
      ProbabilityTheory.covarianceBilin (law P (X 0)) x y)
    (K : Submodule ℝ H) [K.HasOrthogonalProjection] [FiniteDimensional ℝ K] (g : K →ᵇ ℝ) :
    Tendsto (fun N => ∫ x, g (K.orthogonalProjectionOnto x) ∂(law P (normalizedSum X N))) atTop
      (𝓝 (∫ x, g (K.orthogonalProjectionOnto x) ∂γ)) := by
  have := hγ.1
  have hT : Measurable (K.orthogonalProjectionOnto : H → K) :=
    K.orthogonalProjectionOnto.continuous.measurable
  have hlaw : ∀ N, IsProbabilityMeasure (law P (normalizedSum X N)) := fun N => inferInstance
  let μN : ℕ → ProbabilityMeasure K := fun N =>
    ⟨(law P (normalizedSum X N)).map K.orthogonalProjectionOnto, by
      have := hlaw N
      exact inferInstance⟩
  let ν : ProbabilityMeasure K := ⟨γ.map K.orthogonalProjectionOnto, inferInstance⟩
  have hlevy : Tendsto μN atTop (𝓝 ν) := by
    apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    intro t
    have e1 : ∀ N, charFun (μN N : Measure K) t = charFun (law P (normalizedSum X N)) (t : H) :=
      fun N => charFun_map_proj _ K t
    have e2 : charFun (ν : Measure K) t = charFun γ (t : H) := charFun_map_proj _ K t
    simp only [e1, e2]
    rw [charFun_centered_gaussian hγ, hcov]
    exact charFun_normalizedSum_tendsto hiid hL2 hm hmean (t : H)
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlevy) g
  simp only [μN, ν, ProbabilityMeasure.coe_mk] at this
  rw [integral_map hT.aemeasurable g.continuous.aestronglyMeasurable] at this
  simp_rw [integral_map hT.aemeasurable g.continuous.aestronglyMeasurable] at this
  exact this

end FDCLT2

section DenseSub

/-- The span of the first `n` points of a fixed dense sequence. -/
def denseSub (n : ℕ) : Submodule ℝ H :=
  Submodule.span ℝ (Set.range fun i : Fin n => TopologicalSpace.denseSeq H i)

instance finiteDimensional_denseSub (n : ℕ) : FiniteDimensional ℝ (denseSub (H := H) n) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

lemma monotone_denseSub : Monotone (denseSub (H := H)) := by
  intro m n hmn
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, lt_of_lt_of_le i.2 hmn⟩, rfl⟩

lemma dense_denseSub : ⊤ ≤ (⨆ n, denseSub (H := H) n).topologicalClosure := by
  intro x _
  have hx : x ∈ closure (Set.range (TopologicalSpace.denseSeq H)) := by
    rw [(TopologicalSpace.denseRange_denseSeq H).closure_range]; trivial
  refine closure_mono ?_ hx
  rintro _ ⟨i, rfl⟩
  refine (Submodule.mem_iSup_of_mem (i + 1) ?_)
  exact Submodule.subset_span ⟨⟨i, Nat.lt_succ_self i⟩, rfl⟩

lemma denseSub_tendsto (x : H) :
    Tendsto (fun n => (denseSub (H := H) n).starProjection x) atTop (𝓝 x) :=
  Submodule.starProjection_tendsto_self (fun n => denseSub (H := H) n) monotone_denseSub x
    dense_denseSub

lemma norm_sub_starProjection_le (K : Submodule ℝ H) [K.HasOrthogonalProjection] (x : H) :
    ‖x - K.starProjection x‖ ≤ ‖x‖ := by
  have h := K.norm_sq_eq_add_norm_sq_starProjection x
  have h2 := K.starProjection_orthogonal' (𝕜 := ℝ) (E := H)
  have : Kᗮ.starProjection x = x - K.starProjection x := by
    rw [h2]; simp
  rw [this] at h
  nlinarith [norm_nonneg x, norm_nonneg (x - K.starProjection x), sq_nonneg ‖K.starProjection x‖]

lemma denseSub_tail (ρ : Measure H) [IsProbabilityMeasure ρ]
    (hρ : Integrable (fun x : H => ‖x‖ ^ 2) ρ) :
    Tendsto (fun n => ∫ x, ‖x - (denseSub (H := H) n).starProjection x‖ ^ 2 ∂ρ) atTop (𝓝 0) := by
  have := tendsto_integral_of_dominated_convergence (μ := ρ)
    (F := fun n x => ‖x - (denseSub (H := H) n).starProjection x‖ ^ 2) (f := fun _ => (0:ℝ))
    (bound := fun x => ‖x‖ ^ 2)
    (fun n => ((continuous_id.sub (denseSub n).starProjection.continuous).norm.pow 2).aestronglyMeasurable)
    hρ
    (fun n => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_starProjection_le _ x) 2)
    (Filter.Eventually.of_forall fun x => by
      have h1 : Tendsto (fun n => x - (denseSub (H := H) n).starProjection x) atTop (𝓝 (x - x)) :=
        tendsto_const_nhds.sub (denseSub_tendsto x)
      have h2 := h1.norm.pow 2
      simpa using h2)
  simpa using this

end DenseSub

section SumTail
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma sum_tail {X : ℕ → Ω → H} (hiid : IsIIDCopies P X) (hL2 : MemLp (X 0) 2 P)
    (hm : ∀ i, AEMeasurable (X i) P) (hmean : ∫ ω, X 0 ω ∂P = 0) (K : Submodule ℝ H)
    [K.HasOrthogonalProjection] (N : ℕ) (hN : 1 ≤ N) :
    Integrable (fun x : H => ‖x - K.starProjection x‖) (law P (normalizedSum X N)) ∧
    ∫ x, ‖x - K.starProjection x‖ ∂(law P (normalizedSum X N)) ≤
      Real.sqrt (∫ ω, ‖X 0 ω - K.starProjection (X 0 ω)‖ ^ 2 ∂P) := by
  set A : H →L[ℝ] H := ContinuousLinearMap.id ℝ H - K.starProjection with hA
  have hAx : ∀ x, A x = x - K.starProjection x := fun x => by simp [hA]
  have hiid' := iid_comp_clm hiid hm A
  have hL2' : MemLp (fun ω => A (X 0 ω)) 2 P := A.comp_memLp' hL2
  have hm' : ∀ i, AEMeasurable (fun ω => A (X i ω)) P := fun i =>
    A.continuous.measurable.comp_aemeasurable (hm i)
  have hmean' : ∫ ω, A (X 0 ω) ∂P = 0 := by
    rw [A.integral_comp_comm (hL2.integrable (by norm_num)), hmean, map_zero]
  obtain ⟨hM, h2, -⟩ := iid_L2_sum hiid' hL2' hm' hmean' N
  have hAS : ∀ ω, A (normalizedSum X N ω) = (Real.sqrt N)⁻¹ • ∑ i ∈ Finset.range N, A (X i ω) := by
    intro ω; simp [normalizedSum, map_smul, map_sum]
  have hMem : MemLp (fun ω => A (normalizedSum X N ω)) 2 P := by
    simp_rw [hAS]; exact hM.const_smul _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : ∫ ω, ‖A (normalizedSum X N ω)‖ ^ 2 ∂P = ∫ ω, ‖A (X 0 ω)‖ ^ 2 ∂P := by
    simp_rw [hAS, norm_smul, mul_pow, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt hNpos.le]
    rw [integral_const_mul, h2]
    field_simp
  have hmeasS := aemeasurable_normalizedSum hm N
  have hcont : Continuous fun x : H => ‖x - K.starProjection x‖ :=
    (continuous_id.sub K.starProjection.continuous).norm
  have hnorm : MemLp (fun ω => ‖A (normalizedSum X N ω)‖) 2 P := hMem.norm
  constructor
  · rw [integrable_map_measure hcont.aestronglyMeasurable hmeasS]
    have := hnorm.integrable (by norm_num)
    simpa [Function.comp_def, hAx] using this
  · rw [integral_map hmeasS hcont.aestronglyMeasurable]
    have := integral_le_sqrt P hnorm
    simp_rw [hAx] at this hsq
    refine this.trans (Real.sqrt_le_sqrt (le_of_eq ?_))
    simpa [hAx] using hsq

end SumTail

section CLTmain
open scoped BoundedContinuousFunction
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma lintegral_sq_eq_ofReal (ρ : Measure H) (h : Integrable (fun x : H => ‖x‖ ^ 2) ρ) :
    ∫⁻ x, ‖x‖ₑ ^ 2 ∂ρ = ENNReal.ofReal (∫ x, ‖x‖ ^ 2 ∂ρ) := by
  rw [lintegral_sq_eq, ofReal_integral_eq_lintegral_ofReal h (Filter.Eventually.of_forall fun x => sq_nonneg _)]

lemma normalizedSum_sq {X : ℕ → Ω → H} (hiid : IsIIDCopies P X) (hL2 : MemLp (X 0) 2 P)
    (hm : ∀ i, AEMeasurable (X i) P) (hmean : ∫ ω, X 0 ω ∂P = 0) (N : ℕ) (hN : 1 ≤ N) :
    MemLp (normalizedSum X N) 2 P ∧
      ∫ ω, ‖normalizedSum X N ω‖ ^ 2 ∂P = ∫ ω, ‖X 0 ω‖ ^ 2 ∂P := by
  obtain ⟨hM, h2, -⟩ := iid_L2_sum hiid hL2 hm hmean N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨hM.const_smul _, ?_⟩
  show ∫ ω, ‖(Real.sqrt N)⁻¹ • ∑ i ∈ Finset.range N, X i ω‖ ^ 2 ∂P = _
  simp_rw [norm_smul, mul_pow, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt hNpos.le]
  rw [integral_const_mul, h2]
  field_simp

lemma gaussian_sq_integral {γ : Measure H} (hγ : IsCenteredGaussian γ) {X : Ω → H}
    (hL2 : MemLp X 2 P) (hmean : ∫ ω, X ω ∂P = 0)
    (hcov : ∀ x, ProbabilityTheory.covarianceBilin γ x x =
      ProbabilityTheory.covarianceBilin (law P X) x x) :
    ∫ x, ‖x‖ ^ 2 ∂γ = ∫ ω, ‖X ω‖ ^ 2 ∂P := by
  have := hγ.1
  obtain ⟨ι, -, b, -⟩ := exists_hilbertBasis_type (H := H)
  have h1 := hasSum_cov_basis γ id (IsGaussian.memLp_two_id) (gaussian_mean_zero hγ) b
  have h2 := hasSum_cov_basis P X hL2 hmean b
  have e : law γ id = γ := Measure.map_id
  rw [e] at h1
  simp_rw [hcov] at h1
  exact h1.unique h2

lemma gaussian_tail_bound {γ : Measure H} (hγ : IsCenteredGaussian γ) (K : Submodule ℝ H)
    [K.HasOrthogonalProjection] :
    Integrable (fun x : H => ‖x - K.starProjection x‖) γ ∧
    ∫ x, ‖x - K.starProjection x‖ ∂γ ≤ Real.sqrt (∫ x, ‖x - K.starProjection x‖ ^ 2 ∂γ) := by
  have := hγ.1
  set A : H →L[ℝ] H := ContinuousLinearMap.id ℝ H - K.starProjection with hA
  have hAx : ∀ x, A x = x - K.starProjection x := fun x => by simp [hA]
  have hMem : MemLp (fun x : H => ‖x - K.starProjection x‖) 2 γ := by
    have := (A.comp_memLp' (IsGaussian.memLp_two_id (μ := γ))).norm
    simpa [hAx] using this
  exact ⟨hMem.integrable (by norm_num), integral_le_sqrt γ hMem⟩

theorem hilbert_clt_iid_aux {X : ℕ → Ω → H} (hiid : IsIIDCopies P X) (hL2 : MemLp (X 0) 2 P)
    (hm : ∀ i, AEMeasurable (X i) P) (hmean : ∫ ω, X 0 ω ∂P = 0) {γ : Measure H}
    (hγ : IsCenteredGaussian γ)
    (hcov : ∀ x y, ProbabilityTheory.covarianceBilin γ x y =
      ProbabilityTheory.covarianceBilin (law P (X 0)) x y) :
    Tendsto (fun N => wassersteinE 2 (law P (normalizedSum X N)) γ) atTop (𝓝 0) := by
  have := hγ.1
  let μN : ℕ → ProbabilityMeasure H := fun N => ⟨law P (normalizedSum X N), inferInstance⟩
  let μ : ProbabilityMeasure H := ⟨γ, inferInstance⟩
  have hγsq : Integrable (fun x : H => ‖x‖ ^ 2) γ := by
    have := (IsGaussian.memLp_two_id (μ := γ)).norm
    exact this.integrable_sq
  have hX0 : MemLp (fun ω => ‖X 0 ω‖) 2 P := hL2.norm
  have hlawsq : Integrable (fun x : H => ‖x‖ ^ 2) (law P (X 0)) := by
    rw [integrable_map_measure (by fun_prop : Continuous fun x : H => ‖x‖ ^ 2).aestronglyMeasurable
      hL2.aemeasurable]
    exact (integrable_sq_norm_of_memLp2 hL2)
  have hweak : Tendsto μN atTop (𝓝 μ) := by
    refine tendsto_of_approx μN μ fun η hη => ?_
    have t1 := denseSub_tail γ hγsq
    have t2 := denseSub_tail (law P (X 0)) hlawsq
    obtain ⟨n, hn1, hn2⟩ := ((t1.eventually (gt_mem_nhds (show (0:ℝ) < η ^ 2 by positivity))).and
      (t2.eventually (gt_mem_nhds (show (0:ℝ) < η ^ 2 by positivity)))).exists
    refine ⟨denseSub n, inferInstance, ?_, (gaussian_tail_bound hγ _).1, ?_, ?_⟩
    · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      obtain ⟨h1, h2⟩ := sum_tail hiid hL2 hm hmean (denseSub n) N hN
      refine ⟨h1, h2.trans ?_⟩
      have hc : Continuous fun x : H => ‖x - (denseSub (H := H) n).starProjection x‖ ^ 2 := by
        have := (denseSub (H := H) n).starProjection.continuous; fun_prop
      rw [integral_map hL2.aemeasurable hc.aestronglyMeasurable] at hn2
      refine Real.sqrt_le_iff.2 ⟨hη.le, hn2.le⟩
    · refine ((gaussian_tail_bound hγ _).2).trans (Real.sqrt_le_iff.2 ⟨hη.le, hn1.le⟩)
    · intro g
      exact fd_clt hiid hL2 hm hmean hγ hcov (denseSub n) g
  have hsqγ : ∫ x, ‖x‖ ^ 2 ∂γ = ∫ ω, ‖X 0 ω‖ ^ 2 ∂P := gaussian_sq_integral hγ hL2 hmean (fun x => hcov x x)
  have hfin : ∫⁻ x, ‖x‖ₑ ^ 2 ∂(μ : Measure H) < ∞ := by
    show ∫⁻ x, ‖x‖ₑ ^ 2 ∂γ < ∞
    rw [lintegral_sq_eq_ofReal γ hγsq]
    exact ENNReal.ofReal_lt_top
  have hmom : Tendsto (fun N => ∫⁻ x, ‖x‖ₑ ^ 2 ∂(μN N : Measure H)) atTop
      (𝓝 (∫⁻ x, ‖x‖ₑ ^ 2 ∂(μ : Measure H))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    obtain ⟨hMN, hsq⟩ := normalizedSum_sq hiid hL2 hm hmean N hN
    have hint : Integrable (fun x : H => ‖x‖ ^ 2) (law P (normalizedSum X N)) := by
      rw [integrable_map_measure (by fun_prop : Continuous fun x : H => ‖x‖ ^ 2).aestronglyMeasurable
        (aemeasurable_normalizedSum hm N)]
      exact integrable_sq_norm_of_memLp2 hMN
    symm
    show ∫⁻ x, ‖x‖ₑ ^ 2 ∂(law P (normalizedSum X N)) = ∫⁻ x, ‖x‖ₑ ^ 2 ∂γ
    rw [lintegral_sq_eq_ofReal _ hint, lintegral_sq_eq_ofReal γ hγsq, hsqγ,
      integral_map (aemeasurable_normalizedSum hm N)
        (by fun_prop : Continuous fun x : H => ‖x‖ ^ 2).aestronglyMeasurable, hsq]
  exact wE2_tendsto_aux μN μ hweak hfin hmom

end CLTmain

end HilbertCLTAux
-- END CLT

-- BEGIN FD1
namespace HilbertCLTAux
open ProbabilityTheory

section Analytic

lemma cexp_taylor3 (x : ℝ) :
    ‖Complex.exp (x * Complex.I) - 1 - x * Complex.I + ((x ^ 2 / 2 : ℝ) : ℂ)‖ ≤ 4 * |x| ^ 3 := by
  by_cases hx : |x| ≤ 1
  · have hn : ‖(x : ℂ) * Complex.I‖ ≤ 1 := by simpa using hx
    have h := Complex.exp_bound hn (n := 3) (by norm_num)
    have hs : ∑ m ∈ Finset.range 3, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
        1 + x * Complex.I - ((x ^ 2 / 2 : ℝ) : ℂ) := by
      simp [Finset.sum_range_succ, Nat.factorial, mul_pow]
      ring_nf
    rw [hs] at h
    have e : Complex.exp (x * Complex.I) - 1 - x * Complex.I + ((x ^ 2 / 2 : ℝ) : ℂ) =
        Complex.exp (x * Complex.I) - (1 + x * Complex.I - ((x ^ 2 / 2 : ℝ) : ℂ)) := by ring
    rw [e]
    refine h.trans ?_
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    have : (3 : ℕ).succ = 4 := rfl
    simp only [this, Nat.factorial]
    norm_num
    nlinarith [pow_nonneg (abs_nonneg x) 3]
  · rw [not_le] at hx
    have h1 : ‖Complex.exp (x * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp_ofReal_mul_I]
    calc _ ≤ ‖Complex.exp (x * Complex.I)‖ + ‖(1 : ℂ)‖ + ‖(x : ℂ) * Complex.I‖ +
          ‖((x ^ 2 / 2 : ℝ) : ℂ)‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ = 2 + |x| + x ^ 2 / 2 := by
          simp [h1]
          ring
      _ ≤ 4 * |x| ^ 3 := by
          have h1' : 1 < |x| := hx
          have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
          rw [hsq]
          nlinarith [pow_pos (zero_lt_one.trans h1') 2, mul_pos (zero_lt_one.trans h1') (zero_lt_one.trans h1')]

lemma norm_pow_sub_pow_le' {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ n * ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖a‖ * ‖a ^ n - b ^ n‖ ≤ n * ‖a - b‖ :=
      (mul_le_of_le_one_left (norm_nonneg _) ha).trans ih
    have h2 : ‖a - b‖ * ‖b‖ ^ n ≤ ‖a - b‖ :=
      mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hb)
    push_cast
    linarith

end Analytic

section CharTaylor
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma charFun_taylor_bound {U : Ω → ℝ} (hU : AEMeasurable U P) {R : ℝ}
    (hb : ∀ᵐ ω ∂P, |U ω| ≤ R) (h0 : ∫ ω, U ω ∂P = 0) (s : ℝ) :
    ‖charFun (P.map U) s - (1 - ((s ^ 2 * (∫ ω, U ω ^ 2 ∂P) / 2 : ℝ) : ℂ))‖ ≤ 4 * R ^ 3 * |s| ^ 3 := by
  have hint1 : Integrable U P := Integrable.of_bound (C := R) hU.aestronglyMeasurable
    (hb.mono fun ω h => by rwa [Real.norm_eq_abs])
  have hint2 : Integrable (fun ω => U ω ^ 2) P := by
    refine Integrable.of_bound (C := R ^ 2) (hU.aestronglyMeasurable.pow 2)
      (hb.mono fun ω h => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  set g : Ω → ℂ := fun ω => Complex.exp (((s * U ω : ℝ) : ℂ) * Complex.I) - 1 -
    ((s * U ω : ℝ) : ℂ) * Complex.I + (((s * U ω) ^ 2 / 2 : ℝ) : ℂ) with hg
  have hexp : Integrable (fun ω => Complex.exp (((s * U ω : ℝ) : ℂ) * Complex.I)) P := by
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · have : AEMeasurable (fun ω => Complex.exp (((s * U ω : ℝ) : ℂ) * Complex.I)) P := by
        have hm : AEMeasurable (fun ω => ((s * U ω : ℝ) : ℂ)) P :=
          Complex.measurable_ofReal.comp_aemeasurable (hU.const_mul s)
        exact (Complex.measurable_exp.comp_aemeasurable (hm.mul_const Complex.I))
      exact this.aestronglyMeasurable
    · rw [Complex.norm_exp_ofReal_mul_I]
  have hlin : Integrable (fun ω => ((s * U ω : ℝ) : ℂ) * Complex.I) P :=
    ((hint1.const_mul s).ofReal).mul_const Complex.I
  have hquad : Integrable (fun ω => (((s * U ω) ^ 2 / 2 : ℝ) : ℂ)) P := by
    have := (hint2.const_mul ((s ^ 2 / 2 : ℝ))).ofReal (𝕜 := ℂ)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    have e : s ^ 2 / 2 * U ω ^ 2 = (s * U ω) ^ 2 / 2 := by ring
    simp only [e]
    rfl
  have hcf : charFun (P.map U) s = ∫ ω, Complex.exp (((s * U ω : ℝ) : ℂ) * Complex.I) ∂P := by
    rw [charFun_apply_real, integral_map hU (by fun_prop)]
    simp [Complex.ofReal_mul]
  have hI : ∫ ω, g ω ∂P = charFun (P.map U) s - (1 - ((s ^ 2 * (∫ ω, U ω ^ 2 ∂P) / 2 : ℝ) : ℂ)) := by
    simp only [hg]
    have h1 : Integrable (fun ω => Complex.exp (((s * U ω : ℝ) : ℂ) * Complex.I) - 1) P :=
      hexp.sub (integrable_const _)
    have h2 : Integrable (fun ω => Complex.exp (((s * U ω : ℝ) : ℂ) * Complex.I) - 1 -
        ((s * U ω : ℝ) : ℂ) * Complex.I) P := h1.sub hlin
    rw [integral_add h2 hquad, integral_sub h1 hlin, integral_sub hexp (integrable_const _),
      ← hcf]
    simp only [integral_const, probReal_univ, one_smul]
    rw [integral_mul_const, integral_complex_ofReal, integral_const_mul, h0]
    rw [integral_complex_ofReal]
    have : ∫ ω, (s * U ω) ^ 2 / 2 ∂P = s ^ 2 * (∫ ω, U ω ^ 2 ∂P) / 2 := by
      rw [show (fun ω => (s * U ω) ^ 2 / 2) = fun ω => (s ^ 2 / 2) * U ω ^ 2 from by ext ω; ring,
        integral_const_mul]; ring
    rw [this]; push_cast; ring
  rw [← hI]
  refine norm_integral_le_of_norm_le_const (C := 4 * R ^ 3 * |s| ^ 3) (Filter.Eventually.mono hb fun ω h => ?_)
    |>.trans (by simp)
  refine (cexp_taylor3 (s * U ω)).trans ?_
  rw [abs_mul, mul_pow]
  have : |U ω| ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h 3
  nlinarith [pow_nonneg (abs_nonneg s) 3]

end CharTaylor

section CharClose
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma charFun_normalizedSum_eq_pow {X : ℕ → Ω → H} (hiid : IsIIDCopies P X)
    (hm : ∀ i, AEMeasurable (X i) P) (t : H) (N : ℕ) :
    charFun (law P (normalizedSum X N)) t =
      (charFun (P.map fun ω => inner ℝ t (X 0 ω)) ((Real.sqrt N)⁻¹)) ^ N := by
  set Y : ℕ → Ω → ℝ := fun k ω => inner ℝ t (X k ω) with hY
  have hindep : iIndepFun Y P :=
    hiid.1.comp (fun _ x => inner ℝ t x) (fun _ => (innerSL ℝ t).continuous.measurable)
  have hident : ∀ k, IdentDistrib (Y k) (Y 0) P P := fun k =>
    (identDistrib_of_iid hiid (hm 0) hm k).comp (u := fun x => inner ℝ t x)
      (innerSL ℝ t).continuous.measurable
  rw [charFun_map_eq_charFun_map_inner_one (aemeasurable_normalizedSum hm N) t]
  have h := charFun_inv_sqrt_mul_sum hindep hident (n := N) (t := 1)
  have e : (fun ω => inner ℝ (normalizedSum X N ω) t) =
      fun ω => (Real.sqrt N)⁻¹ * ∑ k ∈ Finset.range N, Y k ω := by
    funext ω
    simp only [hY, normalizedSum, inner_smul_left, sum_inner, RCLike.conj_to_real]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_comm]
  rw [e, h, mul_one]

lemma charFun_normalizedSum_close {X : ℕ → Ω → H} (hiid : IsIIDCopies P X)
    (hm : ∀ i, AEMeasurable (X i) P) (hmean : ∫ ω, X 0 ω ∂P = 0) (hL2 : MemLp (X 0) 2 P)
    {M : ℝ} (hM : ∀ᵐ ω ∂P, ‖X 0 ω‖ ≤ M) (t : H) (N : ℕ) (hN1 : 1 ≤ N)
    (hN : (M * ‖t‖) ^ 2 ≤ N) :
    ‖charFun (law P (normalizedSum X N)) t -
        Complex.exp (-(((∫ ω, (inner ℝ t (X 0 ω)) ^ 2 ∂P : ℝ) : ℂ)) / 2)‖ ≤
      4 * (M * ‖t‖) ^ 3 / Real.sqrt N + (M * ‖t‖) ^ 4 / (4 * N) := by
  set R : ℝ := M * ‖t‖ with hR
  set σ2 : ℝ := ∫ ω, (inner ℝ t (X 0 ω)) ^ 2 ∂P with hσ
  have hM0 : 0 ≤ M := by
    obtain ⟨ω, hω⟩ := (hM.and (Filter.Eventually.of_forall fun _ => trivial)).exists
    exact (norm_nonneg _).trans hω.1
  have hR0 : 0 ≤ R := mul_nonneg hM0 (norm_nonneg _)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set s : ℝ := (Real.sqrt N)⁻¹ with hs
  have hs2 : s ^ 2 = (N : ℝ)⁻¹ := by
    rw [hs, inv_pow, Real.sq_sqrt hNpos.le]
  have hs3 : s ^ 3 = (N : ℝ)⁻¹ * s := by rw [pow_succ, hs2]; 
  set U : Ω → ℝ := fun ω => inner ℝ t (X 0 ω) with hU
  have hUm : AEMeasurable U P := (innerSL ℝ t).continuous.measurable.comp_aemeasurable (hm 0)
  have hUb : ∀ᵐ ω ∂P, |U ω| ≤ R := hM.mono fun ω h => by
    calc |U ω| ≤ ‖t‖ * ‖X 0 ω‖ := abs_real_inner_le_norm t (X 0 ω)
      _ ≤ ‖t‖ * M := by gcongr
      _ = R := by rw [hR]; ring
  have hU0 : ∫ ω, U ω ∂P = 0 := by
    show ∫ ω, inner ℝ t (X 0 ω) ∂P = 0
    rw [integral_inner (hL2.integrable (by norm_num)), hmean]; simp
  have hσle : σ2 ≤ R ^ 2 := by
    have : ∫ ω, U ω ^ 2 ∂P ≤ ∫ ω, R ^ 2 ∂P := by
      refine integral_mono_ae ?_ (integrable_const _) (hUb.mono fun ω h => ?_)
      · refine Integrable.of_bound (C := R ^ 2) (hUm.aestronglyMeasurable.pow 2) (hUb.mono fun ω h => ?_)
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
      · calc U ω ^ 2 = |U ω| ^ 2 := (sq_abs _).symm
          _ ≤ R ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    simpa using this
  have hσ0 : 0 ≤ σ2 := integral_nonneg fun ω => sq_nonneg _
  rw [charFun_normalizedSum_eq_pow hiid hm t N]
  set a : ℂ := charFun (P.map U) s with ha
  set b : ℂ := Complex.exp (-(((σ2 * s ^ 2 / 2 : ℝ)) : ℂ)) with hb
  have hbN : b ^ N = Complex.exp (-(σ2 : ℂ) / 2) := by
    rw [hb, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    have : (s : ℂ) ^ 2 * (N : ℂ) = 1 := by
      have : s ^ 2 * (N : ℝ) = 1 := by rw [hs2]; field_simp
      exact_mod_cast this
    linear_combination (-(σ2 : ℂ) / 2) * this
  have ha1 : ‖a‖ ≤ 1 := norm_charFun_le_one _
  have hb1 : ‖b‖ ≤ 1 := by
    rw [hb, Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    rw [Real.exp_le_one_iff]
    have : 0 ≤ σ2 * s ^ 2 / 2 := by positivity
    linarith
  have hx1 : σ2 * s ^ 2 / 2 ≤ 1 := by
    rw [hs2]
    have : σ2 * (N : ℝ)⁻¹ / 2 ≤ 1 := by
      rw [mul_comm, ← div_eq_inv_mul, div_div, div_le_one (by positivity)]
      nlinarith
    exact this
  have h1 : ‖a - (1 - ((σ2 * s ^ 2 / 2 : ℝ) : ℂ))‖ ≤ 4 * R ^ 3 * |s| ^ 3 := by
    have h := charFun_taylor_bound hUm hUb hU0 s
    have hσU : ∫ ω, U ω ^ 2 ∂P = σ2 := rfl
    rw [hσU, show s ^ 2 * σ2 / 2 = σ2 * s ^ 2 / 2 by ring] at h
    exact h
  have h2 : ‖(1 - ((σ2 * s ^ 2 / 2 : ℝ) : ℂ)) - b‖ ≤ (σ2 * s ^ 2 / 2) ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := -(σ2 * s ^ 2 / 2)) (by
      rw [abs_neg, abs_of_nonneg (by positivity)]; exact hx1)
    have e : (1 - ((σ2 * s ^ 2 / 2 : ℝ) : ℂ)) - b = -((Real.exp (-(σ2 * s ^ 2 / 2)) - 1 -
        (-(σ2 * s ^ 2 / 2)) : ℝ) : ℂ) := by
      rw [hb]; push_cast; ring
    rw [e, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ _ := this
      _ = _ := by ring
  have hab : ‖a - b‖ ≤ 4 * R ^ 3 * |s| ^ 3 + (σ2 * s ^ 2 / 2) ^ 2 := by
    calc ‖a - b‖ = ‖(a - (1 - ((σ2 * s ^ 2 / 2 : ℝ) : ℂ))) + ((1 - ((σ2 * s ^ 2 / 2 : ℝ) : ℂ)) - b)‖ := by
          congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add h1 h2)
  rw [← hbN]
  refine (norm_pow_sub_pow_le' ha1 hb1 N).trans ?_
  refine (mul_le_mul_of_nonneg_left hab hNpos.le).trans ?_
  have hsabs : |s| = s := abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))
  rw [hsabs]
  have hsq : Real.sqrt N * s = 1 := by rw [hs]; field_simp
  have e1 : (N : ℝ) * (4 * R ^ 3 * s ^ 3) = 4 * R ^ 3 / Real.sqrt N := by
    rw [hs3, hs]; field_simp
  have e2 : (N : ℝ) * (σ2 * s ^ 2 / 2) ^ 2 ≤ R ^ 4 / (4 * N) := by
    rw [hs2]
    have : (σ2 * (N : ℝ)⁻¹ / 2) ^ 2 ≤ (R ^ 2 * (N : ℝ)⁻¹ / 2) ^ 2 := by
      gcongr
    calc (N : ℝ) * (σ2 * (N : ℝ)⁻¹ / 2) ^ 2 ≤ (N : ℝ) * (R ^ 2 * (N : ℝ)⁻¹ / 2) ^ 2 :=
          mul_le_mul_of_nonneg_left this hNpos.le
      _ = R ^ 4 / (4 * N) := by field_simp; ring
  calc (N : ℝ) * (4 * R ^ 3 * s ^ 3 + (σ2 * s ^ 2 / 2) ^ 2)
      = (N : ℝ) * (4 * R ^ 3 * s ^ 3) + (N : ℝ) * (σ2 * s ^ 2 / 2) ^ 2 := by ring
    _ ≤ 4 * R ^ 3 / Real.sqrt N + R ^ 4 / (4 * N) := by rw [e1]; exact add_le_add le_rfl e2

end CharClose

section Compactness

lemma exists_subseq_weak [FiniteDimensional ℝ H] {M : ℝ} (ν : ℕ → ProbabilityMeasure H)
    (hν : ∀ j, (ν j : Measure H) (Metric.closedBall 0 M) = 1) :
    ∃ (ν₀ : ProbabilityMeasure H) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (ν ∘ φ) atTop (𝓝 ν₀) := by
  have hcpt : IsCompact (Metric.closedBall (0 : H) M) := isCompact_closedBall _ _
  have htight : IsTightMeasureSet {((μ : ProbabilityMeasure H) : Measure H) | μ ∈ Set.range ν} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    refine ⟨Metric.closedBall 0 M, hcpt, ?_⟩
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    have h1 : (ν j : Measure H) (Metric.closedBall 0 M)ᶜ = 0 := by
      rw [prob_compl_eq_zero_iff Metric.isClosed_closedBall.measurableSet]
      exact hν j
    rw [h1]; exact bot_le
  have hclos := isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨ν₀, -, φ, hφ, hlim⟩ := hclos.tendsto_subseq (x := ν) (fun j => subset_closure ⟨j, rfl⟩)
  exact ⟨ν₀, φ, hφ, hlim⟩

lemma tendsto_integral_closed {νs : ℕ → ProbabilityMeasure H} {ν : ProbabilityMeasure H}
    (h : Tendsto νs atTop (𝓝 ν)) {F : Set H} (hF : IsClosed F)
    (hs : ∀ j, (νs j : Measure H) F = 1) :
    (ν : Measure H) F = 1 ∧ ∀ {f : H → ℝ}, Continuous f → ∀ {C : ℝ}, 0 ≤ C → (∀ x ∈ F, |f x| ≤ C) →
      Tendsto (fun j => ∫ x, f x ∂(νs j : Measure H)) atTop (𝓝 (∫ x, f x ∂(ν : Measure H))) := by
  have hν : (ν : Measure H) F = 1 := by
    have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h hF
    simp only [hs, Filter.limsup_const] at hlim
    exact le_antisymm prob_le_one hlim
  refine ⟨hν, fun {f} hf {C} hC0 hC => ?_⟩
  set f' : H → ℝ := fun x => max (-C) (min C (f x)) with hf'
  have hf'c : Continuous f' := by simp only [hf']; fun_prop
  have hb : ∀ x, ‖f' x‖ ≤ C := fun x => by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hT := tendsto_integral_bdd h hf'c hb
  have heq : ∀ (ρ : Measure H) [IsProbabilityMeasure ρ], ρ F = 1 → ∫ x, f x ∂ρ = ∫ x, f' x ∂ρ := by
    intro ρ _ hρ
    refine integral_congr_ae ?_
    have : ∀ᵐ x ∂ρ, x ∈ F := by
      rw [ae_iff]
      exact (prob_compl_eq_zero_iff hF.measurableSet).2 hρ
    filter_upwards [this] with x hx
    have hx' := hC x hx
    rw [abs_le] at hx'
    simp only [hf']
    rw [min_eq_right hx'.2, max_eq_right hx'.1]
  simp_rw [heq _ (hs _)]
  rw [heq _ hν]
  exact hT

end Compactness

section FDFam

/-- A family of data for the uniform finite-dimensional CLT. -/
structure FDFam (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] (M : ℝ) where
  Ω : Type
  [m : MeasurableSpace Ω]
  P : Measure Ω
  [hP : IsProbabilityMeasure P]
  X : ℕ → Ω → H
  hiid : IsIIDCopies P X
  hm : ∀ i, AEMeasurable (X i) P
  hmean : ∫ ω, X 0 ω ∂P = 0
  hbd : ∀ᵐ ω ∂P, ‖X 0 ω‖ ≤ M
  γ : Measure H
  hγ : IsCenteredGaussian γ
  hcov : ∀ x, ProbabilityTheory.covarianceBilin γ x x =
    ProbabilityTheory.covarianceBilin (law P (X 0)) x x

attribute [instance] FDFam.m FDFam.hP

namespace FDFam
variable {M : ℝ} (F : FDFam H M)

lemma memLp2 : MemLp (F.X 0) 2 F.P :=
  MemLp.of_bound (F.hm 0).aestronglyMeasurable M F.hbd

lemma M_nonneg (F : FDFam H M) : 0 ≤ M := by
  obtain ⟨ω, hω⟩ := F.hbd.exists
  exact (norm_nonneg _).trans hω

instance : IsProbabilityMeasure F.γ := by
  have := F.hγ.1
  infer_instance

/-- the law of the summand -/
def law0 : ProbabilityMeasure H := ⟨law F.P (F.X 0), inferInstance⟩

/-- the law of the normalised sum -/
def muN (N : ℕ) : ProbabilityMeasure H := ⟨law F.P (normalizedSum F.X N), inferInstance⟩

/-- the Gaussian -/
def gam : ProbabilityMeasure H := ⟨F.γ, inferInstance⟩

lemma law0_closedBall : (F.law0 : Measure H) (Metric.closedBall 0 M) = 1 := by
  show (law F.P (F.X 0)) (Metric.closedBall 0 M) = 1
  have hB : MeasurableSet (Metric.closedBall (0 : H) M) := Metric.isClosed_closedBall.measurableSet
  have h : ∀ᵐ x ∂(law F.P (F.X 0)), x ∈ Metric.closedBall (0 : H) M := by
    have := (ae_map_iff (F.hm 0) (p := fun x => x ∈ Metric.closedBall (0 : H) M) hB).2
      (F.hbd.mono fun ω h => by simpa using h)
    exact this
  exact (prob_compl_eq_zero_iff hB).1 (ae_iff.1 h)

end FDFam

end FDFam

end HilbertCLTAux
-- END FD1

-- BEGIN FD2
namespace HilbertCLTAux
open ProbabilityTheory

section FDFam2
namespace FDFam
variable {M : ℝ} (F : FDFam H M)

/-- second moment in direction `t` -/
def cov2 (t : H) : ℝ := ∫ ω, (inner ℝ t (F.X 0 ω)) ^ 2 ∂F.P

lemma integral_law0_sq (t : H) :
    ∫ x, (inner ℝ t x) ^ 2 ∂(F.law0 : Measure H) = F.cov2 t := by
  show ∫ x, (inner ℝ t x) ^ 2 ∂(law F.P (F.X 0)) = _
  rw [integral_map (F.hm 0) (by fun_prop : Continuous fun x : H => (inner ℝ t x) ^ 2).aestronglyMeasurable]
  rfl

lemma cov_law0 (t : H) : ProbabilityTheory.covarianceBilin (law F.P (F.X 0)) t t = F.cov2 t :=
  covarianceBilin_law_self F.P (F.X 0) F.memLp2 F.hmean t

lemma charFun_gam (t : H) :
    charFun F.γ t = Complex.exp (-((F.cov2 t : ℝ) : ℂ) / 2) := by
  rw [charFun_centered_gaussian F.hγ, F.hcov, F.cov_law0]

lemma charFun_muN_close (t : H) (N : ℕ) (hN1 : 1 ≤ N) (hN : (M * ‖t‖) ^ 2 ≤ N) :
    ‖charFun (law F.P (normalizedSum F.X N)) t - Complex.exp (-((F.cov2 t : ℝ) : ℂ) / 2)‖ ≤
      4 * (M * ‖t‖) ^ 3 / Real.sqrt N + (M * ‖t‖) ^ 4 / (4 * N) :=
  charFun_normalizedSum_close F.hiid F.hm F.hmean F.memLp2 F.hbd t N hN1 hN

lemma sq_gam : ∫ x, ‖x‖ ^ 2 ∂F.γ = ∫ ω, ‖F.X 0 ω‖ ^ 2 ∂F.P :=
  gaussian_sq_integral F.hγ F.memLp2 F.hmean F.hcov

lemma sq_law0 : ∫ x, ‖x‖ ^ 2 ∂(F.law0 : Measure H) = ∫ ω, ‖F.X 0 ω‖ ^ 2 ∂F.P := by
  show ∫ x, ‖x‖ ^ 2 ∂(law F.P (F.X 0)) = _
  rw [integral_map (F.hm 0) (by fun_prop : Continuous fun x : H => ‖x‖ ^ 2).aestronglyMeasurable]

lemma sq_muN (N : ℕ) (hN : 1 ≤ N) :
    ∫ x, ‖x‖ ^ 2 ∂(F.muN N : Measure H) = ∫ ω, ‖F.X 0 ω‖ ^ 2 ∂F.P := by
  show ∫ x, ‖x‖ ^ 2 ∂(law F.P (normalizedSum F.X N)) = _
  rw [integral_map (aemeasurable_normalizedSum F.hm N)
    (by fun_prop : Continuous fun x : H => ‖x‖ ^ 2).aestronglyMeasurable]
  exact (normalizedSum_sq F.hiid F.memLp2 F.hm F.hmean N hN).2

lemma integrable_sq_muN (N : ℕ) (hN : 1 ≤ N) :
    Integrable (fun x : H => ‖x‖ ^ 2) (F.muN N : Measure H) := by
  show Integrable (fun x : H => ‖x‖ ^ 2) (law F.P (normalizedSum F.X N))
  rw [integrable_map_measure (by fun_prop : Continuous fun x : H => ‖x‖ ^ 2).aestronglyMeasurable
    (aemeasurable_normalizedSum F.hm N)]
  exact integrable_sq_norm_of_memLp2 (normalizedSum_sq F.hiid F.memLp2 F.hm F.hmean N hN).1

lemma integrable_sq_gam : Integrable (fun x : H => ‖x‖ ^ 2) F.γ := by
  haveI := F.hγ.1
  exact (IsGaussian.memLp_two_id (μ := F.γ)).norm.integrable_sq

end FDFam
end FDFam2

section FDSeq

lemma fd_subseq [FiniteDimensional ℝ H] {M : ℝ} (F : ℕ → FDFam H M) (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) (ν₀ : ProbabilityMeasure H)
    (hν : Tendsto (fun j => (F j).law0) atTop (𝓝 ν₀)) :
    Tendsto (fun j => wassersteinE 2 ((F j).muN (N j) : Measure H) ((F j).gam : Measure H))
      atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (F 0).M_nonneg
  obtain ⟨hν₀F, hconv⟩ := tendsto_integral_closed hν Metric.isClosed_closedBall
    (fun j => (F j).law0_closedBall)
  -- convergence of covariances and second moments
  have hcov_conv : ∀ t : H, Tendsto (fun j => (F j).cov2 t) atTop
      (𝓝 (∫ x, (inner ℝ t x) ^ 2 ∂(ν₀ : Measure H))) := by
    intro t
    have := hconv (f := fun x => (inner ℝ t x) ^ 2) (by fun_prop) (C := (M * ‖t‖) ^ 2)
      (by positivity) (fun x hx => by
        rw [abs_pow]
        have h1 : |inner ℝ t x| ≤ ‖t‖ * ‖x‖ := abs_real_inner_le_norm t x
        have h2 : ‖x‖ ≤ M := by simpa using hx
        calc |inner ℝ t x| ^ 2 ≤ (‖t‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
          _ ≤ (M * ‖t‖) ^ 2 := by
              have : ‖t‖ * ‖x‖ ≤ M * ‖t‖ := by nlinarith [norm_nonneg t, norm_nonneg x]
              exact pow_le_pow_left₀ (by positivity) this 2)
    refine this.congr fun j => ?_
    exact (F j).integral_law0_sq t
  have hsq_conv : Tendsto (fun j => ∫ ω, ‖(F j).X 0 ω‖ ^ 2 ∂(F j).P) atTop
      (𝓝 (∫ x, ‖x‖ ^ 2 ∂(ν₀ : Measure H))) := by
    have := hconv (f := fun x => ‖x‖ ^ 2) (by fun_prop) (C := M ^ 2) (by positivity)
      (fun x hx => by
        rw [abs_pow, abs_norm]
        have h2 : ‖x‖ ≤ M := by simpa using hx
        exact pow_le_pow_left₀ (norm_nonneg _) h2 2)
    refine this.congr fun j => ?_
    exact (F j).sq_law0
  have hmean_t : ∀ t : H, ∫ x, inner ℝ t x ∂(ν₀ : Measure H) = 0 := by
    intro t
    have := hconv (f := fun x => inner ℝ t x) (by fun_prop) (C := ‖t‖ * M)
      (by positivity) (fun x hx => by
        have h1 : |inner ℝ t x| ≤ ‖t‖ * ‖x‖ := abs_real_inner_le_norm t x
        have h2 : ‖x‖ ≤ M := by simpa using hx
        exact h1.trans (by nlinarith [norm_nonneg t, norm_nonneg x]))
    refine tendsto_nhds_unique this (tendsto_const_nhds.congr fun j => ?_)
    symm
    have hj : ∫ x, inner ℝ t x ∂((F j).law0 : Measure H) = ∫ ω, inner ℝ t ((F j).X 0 ω) ∂(F j).P := by
      show ∫ x, inner ℝ t x ∂(law (F j).P ((F j).X 0)) = _
      exact integral_map ((F j).hm 0) (by fun_prop : Continuous fun x : H => inner ℝ t x).aestronglyMeasurable
    rw [hj, integral_inner ((F j).memLp2.integrable (by norm_num)), (F j).hmean]; simp
  -- the limit measure is centered with bounded support
  have hbd0 : ∀ᵐ x ∂(ν₀ : Measure H), ‖x‖ ≤ M := by
    have h : ∀ᵐ x ∂(ν₀ : Measure H), x ∈ Metric.closedBall (0 : H) M :=
      ae_iff.2 ((prob_compl_eq_zero_iff Metric.isClosed_closedBall.measurableSet).2 hν₀F)
    exact h.mono fun x hx => by simpa using hx
  have hL2 : MemLp id 2 (ν₀ : Measure H) := MemLp.of_bound aestronglyMeasurable_id M hbd0
  have hmeanν : ∫ x, id x ∂(ν₀ : Measure H) = 0 := by
    refine ext_inner_left ℝ fun t => ?_
    rw [inner_zero_right]
    show inner ℝ t (∫ x, x ∂(ν₀ : Measure H)) = 0
    have hint : Integrable (fun x : H => x) (ν₀ : Measure H) := hL2.integrable (by norm_num)
    rw [← integral_inner hint t]
    exact hmean_t t
  obtain ⟨γL, hγp, hγg, hγcov⟩ := exists_centeredGaussian_of_traceClass
    (ProbabilityTheory.covarianceBilin (law (ν₀ : Measure H) id))
    (isTraceClassCov_covarianceBilin (ν₀ : Measure H) id hL2 hmeanν).1
  have hcovν : ∀ t : H, ProbabilityTheory.covarianceBilin γL t t = ∫ x, (inner ℝ t x) ^ 2 ∂(ν₀ : Measure H) := by
    intro t
    rw [hγcov, covarianceBilin_law_self (ν₀ : Measure H) id hL2 hmeanν t]
    rfl
  haveI := hγg.1
  -- characteristic functions
  have hchL : ∀ t : H, charFun γL t = Complex.exp (-(((∫ x, (inner ℝ t x) ^ 2 ∂(ν₀ : Measure H) : ℝ)) : ℂ) / 2) := by
    intro t
    rw [charFun_centered_gaussian hγg, hcovν]
  have hexp_conv : ∀ t : H, Tendsto (fun j => Complex.exp (-(((F j).cov2 t : ℝ) : ℂ) / 2)) atTop
      (𝓝 (charFun γL t)) := by
    intro t
    rw [hchL]
    have h1 := Complex.continuous_ofReal.tendsto _ |>.comp (hcov_conv t)
    have h2 := (Complex.continuous_exp.tendsto _).comp ((h1.neg).div_const 2)
    exact h2
  have hchγ : ∀ t : H, Tendsto (fun j => charFun ((F j).gam : Measure H) t) atTop (𝓝 (charFun γL t)) := by
    intro t
    refine (hexp_conv t).congr fun j => ?_
    exact ((F j).charFun_gam t).symm
  have hchμ : ∀ t : H, Tendsto (fun j => charFun ((F j).muN (N j) : Measure H) t) atTop
      (𝓝 (charFun γL t)) := by
    intro t
    have hdiff : Tendsto (fun j => charFun ((F j).muN (N j) : Measure H) t -
        Complex.exp (-(((F j).cov2 t : ℝ) : ℂ) / 2)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun j => 4 * (M * ‖t‖) ^ 3 / Real.sqrt (N j) +
        (M * ‖t‖) ^ 4 / (4 * (N j : ℝ))) ?_ ?_
      · have hNe : ∀ᶠ j in atTop, 1 ≤ N j ∧ (M * ‖t‖) ^ 2 ≤ N j := by
          refine (hN.eventually_ge_atTop 1).and ?_
          exact hN.eventually_ge_atTop ⌈(M * ‖t‖) ^ 2⌉₊ |>.mono fun j hj => by
            exact (Nat.le_ceil _).trans (by exact_mod_cast hj)
        filter_upwards [hNe] with j ⟨h1, h2⟩
        exact (F j).charFun_muN_close t (N j) h1 h2
      · have hNr : Tendsto (fun j => (N j : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop.comp hN
        have hs : Tendsto (fun j => Real.sqrt (N j)) atTop atTop :=
          Real.tendsto_sqrt_atTop.comp hNr
        have e1 : Tendsto (fun j => 4 * (M * ‖t‖) ^ 3 / Real.sqrt (N j)) atTop (𝓝 0) :=
          hs.const_div_atTop _ |>.congr fun j => rfl
        have e2 : Tendsto (fun j => (M * ‖t‖) ^ 4 / (4 * (N j : ℝ))) atTop (𝓝 0) :=
          (hNr.const_mul_atTop (by norm_num : (0:ℝ) < 4)).const_div_atTop _ |>.congr fun j => rfl
        simpa using e1.add e2
    have := hdiff.add (hexp_conv t)
    simpa using this
  -- Levy
  let μL : ProbabilityMeasure H := ⟨γL, hγp⟩
  have hμ : Tendsto (fun j => (F j).muN (N j)) atTop (𝓝 μL) :=
    ProbabilityMeasure.tendsto_of_tendsto_charFun hchμ
  have hγ : Tendsto (fun j => (F j).gam) atTop (𝓝 μL) :=
    ProbabilityMeasure.tendsto_of_tendsto_charFun hchγ
  -- second moments
  have hLsq : ∫ x, ‖x‖ ^ 2 ∂γL = ∫ x, ‖x‖ ^ 2 ∂(ν₀ : Measure H) := by
    have := gaussian_sq_integral (P := (ν₀ : Measure H)) (X := id) hγg hL2 hmeanν (fun x => by
      rw [hγcov])
    simpa using this
  have hsqL : Integrable (fun x : H => ‖x‖ ^ 2) γL :=
    (IsGaussian.memLp_two_id (μ := γL)).norm.integrable_sq
  have hfin : ∫⁻ x, ‖x‖ₑ ^ 2 ∂(μL : Measure H) < ∞ := by
    show ∫⁻ x, ‖x‖ₑ ^ 2 ∂γL < ∞
    rw [lintegral_sq_eq_ofReal γL hsqL]; exact ENNReal.ofReal_lt_top
  have hmomL : (∫⁻ x, ‖x‖ₑ ^ 2 ∂(μL : Measure H)) =
      ENNReal.ofReal (∫ x, ‖x‖ ^ 2 ∂(ν₀ : Measure H)) := by
    show ∫⁻ x, ‖x‖ₑ ^ 2 ∂γL = _
    rw [lintegral_sq_eq_ofReal γL hsqL, hLsq]
  have hmomμ : Tendsto (fun j => ∫⁻ x, ‖x‖ₑ ^ 2 ∂((F j).muN (N j) : Measure H)) atTop
      (𝓝 (∫⁻ x, ‖x‖ₑ ^ 2 ∂(μL : Measure H))) := by
    rw [hmomL]
    refine (ENNReal.tendsto_ofReal hsq_conv).congr' ?_
    filter_upwards [hN.eventually_ge_atTop 1] with j hj
    rw [lintegral_sq_eq_ofReal _ ((F j).integrable_sq_muN (N j) hj), (F j).sq_muN (N j) hj]
  have hmomγ : Tendsto (fun j => ∫⁻ x, ‖x‖ₑ ^ 2 ∂((F j).gam : Measure H)) atTop
      (𝓝 (∫⁻ x, ‖x‖ₑ ^ 2 ∂(μL : Measure H))) := by
    rw [hmomL]
    refine (ENNReal.tendsto_ofReal hsq_conv).congr' (Filter.Eventually.of_forall fun j => ?_)
    show _ = ∫⁻ x, ‖x‖ₑ ^ 2 ∂(F j).γ
    rw [lintegral_sq_eq_ofReal _ (F j).integrable_sq_gam, (F j).sq_gam]
  have w1 := wE2_tendsto_aux (fun j => (F j).muN (N j)) μL hμ hfin hmomμ
  have w2 := wE2_tendsto_aux (fun j => (F j).gam) μL hγ hfin hmomγ
  have w2' : Tendsto (fun j => wassersteinE 2 (μL : Measure H) ((F j).gam : Measure H)) atTop (𝓝 0) :=
    w2.congr fun j => wassersteinE_comm 2 _ _
  have hsum := w1.add w2'
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun j => bot_le) (fun j => ?_)
  haveI := (F j).hP
  exact wassersteinE_triangle 2 (by norm_num) _ (μL : Measure H) _

end FDSeq

section FDUniform

lemma fd_seq_tendsto [FiniteDimensional ℝ H] {M : ℝ} (F : ℕ → FDFam H M) (N : ℕ → ℕ)
    (hN : Tendsto N atTop atTop) :
    Tendsto (fun j => wassersteinE 2 ((F j).muN (N j) : Measure H) ((F j).gam : Measure H))
      atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ν₀, φ, hφ, hlim⟩ := exists_subseq_weak (fun j => (F (ns j)).law0)
    (fun j => (F (ns j)).law0_closedBall)
  refine ⟨φ, ?_⟩
  exact fd_subseq (fun j => F (ns (φ j))) (fun j => N (ns (φ j)))
    (hN.comp (hns.comp hφ.tendsto_atTop)) ν₀ hlim

theorem fd_uniform [FiniteDimensional ℝ H] (M : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : ℕ → Ω → H), IsIIDCopies P X → (∀ i, AEMeasurable (X i) P) →
      ∫ ω, X 0 ω ∂P = 0 → (∀ᵐ ω ∂P, ‖X 0 ω‖ ≤ M) → ∀ γ : Measure H, IsCenteredGaussian γ →
      (∀ x, ProbabilityTheory.covarianceBilin γ x x =
        ProbabilityTheory.covarianceBilin (law P (X 0)) x x) →
      wassersteinE 2 (law P (normalizedSum X N)) γ ≤ ENNReal.ofReal ε := by
  by_contra hcon
  push Not at hcon
  choose N hN Ω mΩ P hP X hiid hm hmean hbd γ hγ hcov hbad using hcon
  let F : ℕ → FDFam H M := fun j => 
    { Ω := Ω j, m := mΩ j, P := P j, hP := hP j, X := X j, hiid := hiid j, hm := hm j,
      hmean := hmean j, hbd := hbd j, γ := γ j, hγ := hγ j, hcov := hcov j }
  have hNt : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun j => hN j) tendsto_id
  have hT := fd_seq_tendsto F N hNt
  have h1 : ∀ᶠ j in atTop, wassersteinE 2 ((F j).muN (N j) : Measure H) ((F j).gam : Measure H) <
      ENNReal.ofReal ε := hT.eventually (gt_mem_nhds (by simpa using hε))
  obtain ⟨j, hj⟩ := h1.exists
  exact absurd (hbad j) (not_lt.2 hj.le)

end FDUniform

end HilbertCLTAux
-- END FD2

-- BEGIN RED
namespace HilbertCLTAux
open ProbabilityTheory

section Reduction

lemma W2_embed (K : Submodule ℝ H) (μ ν : Measure K) :
    wassersteinE 2 (μ.map K.subtype) (ν.map K.subtype) ≤ wassersteinE 2 μ ν := by
  refine le_iInf fun π => ?_
  have hι : Measurable (K.subtype : K → H) := continuous_subtype_val.measurable
  have hιι : Measurable (Prod.map (K.subtype : K → H) (K.subtype : K → H)) := hι.prodMap hι
  have hπ : IsCoupling (π.1.map (Prod.map (K.subtype : K → H) (K.subtype : K → H)))
      (μ.map K.subtype) (ν.map K.subtype) := by
    constructor
    · rw [Measure.map_map measurable_fst hιι]
      have : (Prod.fst ∘ Prod.map (K.subtype : K → H) (K.subtype : K → H)) =
          (K.subtype : K → H) ∘ Prod.fst := rfl
      rw [this, ← Measure.map_map hι measurable_fst, π.2.1]
    · rw [Measure.map_map measurable_snd hιι]
      have : (Prod.snd ∘ Prod.map (K.subtype : K → H) (K.subtype : K → H)) =
          (K.subtype : K → H) ∘ Prod.snd := rfl
      rw [this, ← Measure.map_map hι measurable_snd, π.2.2]
  refine (wassersteinE_le_cost hπ).trans (le_of_eq ?_)
  congr 1
  have hm : Measurable fun z : H × H => ENNReal.ofReal (‖z.1 - z.2‖ ^ (2:ℝ)) :=
    ENNReal.measurable_ofReal.comp (((measurable_fst.sub measurable_snd).norm).pow_const _)
  rw [lintegral_map hm hιι]
  congr 1

lemma wE2_le_of_rv {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z W : Ω → H} (hZ : AEMeasurable Z P) (hW : AEMeasurable W P) {c : ℝ}
    (hc : ∫⁻ ω, ENNReal.ofReal (‖Z ω - W ω‖ ^ 2) ∂P ≤ ENNReal.ofReal c) :
    wassersteinE 2 (law P Z) (law P W) ≤ ENNReal.ofReal (Real.sqrt c) := by
  refine (wassersteinE_le_of_coupling P 2 (by norm_num) Z W hZ hW).trans ?_
  have h2 : ∀ ω, ENNReal.ofReal (‖Z ω - W ω‖ ^ (2:ℝ)) = ENNReal.ofReal (‖Z ω - W ω‖ ^ 2) := by
    intro ω; rw [Real.rpow_two]
  simp only [h2]
  calc _ ≤ (ENNReal.ofReal c) ^ (1 / (2:ℝ)) := ENNReal.rpow_le_rpow hc (by norm_num)
    _ ≤ _ := by
        rcases le_or_gt c 0 with h | h
        · rw [ENNReal.ofReal_of_nonpos h, ENNReal.zero_rpow_of_pos (by norm_num)]
          exact bot_le
        · rw [ENNReal.ofReal_rpow_of_pos h, Real.sqrt_eq_rpow]

lemma iid_comp_clm' {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → H} (hiid : IsIIDCopies P X) (hm : ∀ i, AEMeasurable (X i) P)
    (A : H →L[ℝ] F) : IsIIDCopies P (fun i ω => A (X i ω)) := by
  refine ⟨hiid.1.comp (fun _ => A) (fun _ => A.continuous.measurable), fun i j => ?_⟩
  have h : ∀ k, law P (fun ω => A (X k ω)) = (law P (X k)).map A := fun k =>
    (AEMeasurable.map_map_of_aemeasurable A.continuous.aemeasurable (hm k)).symm
  rw [h i, h j, hiid.2 i j]

lemma gaussian_map_data {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (A : H →L[ℝ] F) {γ : Measure H} (hγ : IsCenteredGaussian γ) {X : Ω → H}
    (hL2 : MemLp X 2 P)
    (hcov : ∀ x y, ProbabilityTheory.covarianceBilin γ x y =
      ProbabilityTheory.covarianceBilin (law P X) x y) :
    IsCenteredGaussian (γ.map A) ∧ ∀ u v, ProbabilityTheory.covarianceBilin (γ.map A) u v =
      ProbabilityTheory.covarianceBilin (law P (fun ω => A (X ω))) u v := by
  have := hγ.1
  have hX : AEMeasurable X P := hL2.aemeasurable
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · intro L
    rw [integral_map A.continuous.aemeasurable L.continuous.aestronglyMeasurable]
    exact hγ.2 (L.comp A)
  · intro u v
    have hlaw : law P (fun ω => A (X ω)) = (law P X).map A :=
      (AEMeasurable.map_map_of_aemeasurable A.continuous.aemeasurable hX).symm
    have hmem : MemLp id 2 (law P X) :=
      (memLp_map_measure_iff aestronglyMeasurable_id hX).2 hL2
    rw [hlaw, ProbabilityTheory.covarianceBilin_map IsGaussian.memLp_two_id A,
      ProbabilityTheory.covarianceBilin_map hmem A, hcov]

section ReductionP
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma clm_normalizedSum_sq {X : ℕ → Ω → H} (hiid : IsIIDCopies P X) (hL2 : MemLp (X 0) 2 P)
    (hm : ∀ i, AEMeasurable (X i) P) (hmean : ∫ ω, X 0 ω ∂P = 0) (B : H →L[ℝ] H) (N : ℕ)
    (hN : 1 ≤ N) :
    Integrable (fun ω => ‖B (normalizedSum X N ω)‖ ^ 2) P ∧
    ∫ ω, ‖B (normalizedSum X N ω)‖ ^ 2 ∂P = ∫ ω, ‖B (X 0 ω)‖ ^ 2 ∂P := by
  have hiid' := iid_comp_clm hiid hm B
  have hL2' : MemLp (fun ω => B (X 0 ω)) 2 P := B.comp_memLp' hL2
  have hm' : ∀ i, AEMeasurable (fun ω => B (X i ω)) P := fun i =>
    B.continuous.measurable.comp_aemeasurable (hm i)
  have hmean' : ∫ ω, B (X 0 ω) ∂P = 0 := by
    rw [B.integral_comp_comm (hL2.integrable (by norm_num)), hmean, map_zero]
  obtain ⟨hM, h2⟩ := normalizedSum_sq hiid' hL2' hm' hmean' N hN
  have e : ∀ ω, normalizedSum (fun i ω => B (X i ω)) N ω = B (normalizedSum X N ω) := fun ω => by
    simp [normalizedSum, map_smul, map_sum]
  have hM' : MemLp (fun ω => B (normalizedSum X N ω)) 2 P := by
    have : normalizedSum (fun i ω => B (X i ω)) N = fun ω => B (normalizedSum X N ω) := funext e
    rwa [this] at hM
  simp only [e] at h2
  exact ⟨integrable_sq_norm_of_memLp2 hM', h2⟩

end ReductionP

end Reduction

theorem hilbert_clt_uniform_aux (K : ℕ → Submodule ℝ H) [∀ n, (K n).HasOrthogonalProjection]
    (hK : ∀ n, FiniteDimensional ℝ (K n)) (τ : ℕ → ℝ) (hτ : Tendsto τ atTop (𝓝 0))
    (M : ℝ) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : ℕ → Ω → H), IsIIDCopies P X → (∀ i, AEMeasurable (X i) P) →
      MemLp (X 0) 2 P →
      ∫ ω, X 0 ω ∂P = 0 →
      (∀ n, ∫ ω, ‖X 0 ω - (K n).starProjection (X 0 ω)‖ ^ 2 ∂P ≤ τ n) →
      (∀ᵐ ω ∂P, ‖X 0 ω‖ ≤ M) →
      ∀ γ : Measure H, IsCenteredGaussian γ →
        (∀ x y, ProbabilityTheory.covarianceBilin γ x y =
          ProbabilityTheory.covarianceBilin (law P (X 0)) x y) →
        wassersteinE 2 (law P (normalizedSum X N)) γ ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := (hτ.eventually (gt_mem_nhds
    (show (0:ℝ) < (ε / 4) ^ 2 by positivity))).exists
  haveI : FiniteDimensional ℝ (K n₀) := hK n₀
  haveI : CompleteSpace (K n₀) := FiniteDimensional.complete ℝ (K n₀)
  obtain ⟨N₁, hN₁⟩ := fd_uniform (H := K n₀) M (ε / 2) (by positivity)
  refine ⟨max N₁ 1, fun N hN Ω _ P _ X hiid hm hL2 hmean htau hbd γ hγ hcov => ?_⟩
  have hNN1 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hγG := hγ.1
  set T : H →L[ℝ] H := (K n₀).starProjection with hT
  set A : H →L[ℝ] K n₀ := (K n₀).orthogonalProjectionOnto with hA
  set B : H →L[ℝ] H := ContinuousLinearMap.id ℝ H - T with hB
  have hBx : ∀ x, B x = x - T x := fun x => by simp [hB]
  have hιA : ∀ x, ((A x : K n₀) : H) = T x := fun x => rfl
  -- the finite-dimensional comparison
  set Y : ℕ → Ω → K n₀ := fun i ω => A (X i ω) with hY
  have hiidY : IsIIDCopies P Y := iid_comp_clm' hiid hm A
  have hmY : ∀ i, AEMeasurable (Y i) P := fun i =>
    A.continuous.measurable.comp_aemeasurable (hm i)
  have hmeanY : ∫ ω, Y 0 ω ∂P = 0 := by
    simp only [hY]
    rw [A.integral_comp_comm (hL2.integrable (by norm_num)), hmean, map_zero]
  have hbdY : ∀ᵐ ω ∂P, ‖Y 0 ω‖ ≤ M := by
    filter_upwards [hbd] with ω hω
    refine le_trans ?_ hω
    simp only [hY]
    exact (K n₀).norm_starProjection_apply_le (X 0 ω)
  obtain ⟨hγK, hcovK⟩ := gaussian_map_data A hγ hL2 hcov
  have hfd := hN₁ N hNN1 Ω P Y hiidY hmY hmeanY hbdY (γ.map A) hγK
    (fun x => hcovK x x)
  have hemb := (W2_embed (K n₀) _ _).trans hfd
  -- identify the embedded laws
  have hmS : AEMeasurable (normalizedSum X N) P := aemeasurable_normalizedSum hm N
  have hSY : ∀ ω, normalizedSum Y N ω = A (normalizedSum X N ω) := fun ω => by
    simp [hY, normalizedSum, map_smul, map_sum]
  have hq1 : (law P (normalizedSum Y N)).map (K n₀).subtype =
      law P (fun ω => T (normalizedSum X N ω)) := by
    have hmYS : AEMeasurable (normalizedSum Y N) P := aemeasurable_normalizedSum hmY N
    have hcomp : (K n₀).subtype ∘ normalizedSum Y N = fun ω => T (normalizedSum X N ω) :=
      funext fun ω => by
        show ((normalizedSum Y N ω : K n₀) : H) = _
        rw [hSY, hιA]
    show Measure.map _ (Measure.map _ _) = _
    have hsub : Measurable ((K n₀).subtype : K n₀ → H) := continuous_subtype_val.measurable
    rw [AEMeasurable.map_map_of_aemeasurable hsub.aemeasurable hmYS, hcomp]
  have hq2 : (γ.map A).map (K n₀).subtype = γ.map T := by
    have hsub : Measurable ((K n₀).subtype : K n₀ → H) := continuous_subtype_val.measurable
    rw [Measure.map_map hsub A.continuous.measurable]
    rfl
  rw [hq1, hq2] at hemb
  -- tail terms
  have hX0m : AEMeasurable (X 0) P := hm 0
  have hTm : AEMeasurable (fun ω => T (normalizedSum X N ω)) P :=
    T.continuous.measurable.comp_aemeasurable hmS
  have hBsq := clm_normalizedSum_sq hiid hL2 hm hmean B N hN1
  have hτ0 : ∫ ω, ‖B (X 0 ω)‖ ^ 2 ∂P ≤ (ε / 4) ^ 2 := by
    refine le_trans (le_of_eq ?_) (le_trans (htau n₀) hn₀.le)
    simp only [hBx]
    rfl
  have hsqrt : Real.sqrt ((ε / 4) ^ 2) = ε / 4 := Real.sqrt_sq (by positivity)
  have hterm1 : wassersteinE 2 (law P (normalizedSum X N))
      (law P (fun ω => T (normalizedSum X N ω))) ≤ ENNReal.ofReal (ε / 4) := by
    have := wE2_le_of_rv (P := P) hmS hTm (c := (ε / 4) ^ 2) (by
      have e : ∀ ω, ‖normalizedSum X N ω - T (normalizedSum X N ω)‖ ^ 2 =
          ‖B (normalizedSum X N ω)‖ ^ 2 := fun ω => by rw [hBx]
      simp only [e]
      rw [← ofReal_integral_eq_lintegral_ofReal hBsq.1 (Filter.Eventually.of_forall
        fun ω => by positivity), hBsq.2]
      exact ENNReal.ofReal_le_ofReal hτ0)
    rwa [hsqrt] at this
  have hterm3 : wassersteinE 2 (γ.map T) γ ≤ ENNReal.ofReal (ε / 4) := by
    haveI := hγG
    have hmemB : MemLp (fun z : H => B z) 2 γ := B.comp_memLp' IsGaussian.memLp_two_id
    have hint : Integrable (fun z : H => ‖B z‖ ^ 2) γ := integrable_sq_norm_of_memLp2 hmemB
    obtain ⟨hγB, hcovB⟩ := gaussian_map_data B hγ hL2 hcov
    have hsq : ∫ z, ‖B z‖ ^ 2 ∂γ = ∫ ω, ‖B (X 0 ω)‖ ^ 2 ∂P := by
      rw [← gaussian_sq_integral hγB (X := fun ω => B (X 0 ω)) (P := P)
        (B.comp_memLp' hL2) (by rw [B.integral_comp_comm (hL2.integrable (by norm_num)), hmean,
          map_zero]) (fun x => hcovB x x)]
      rw [integral_map B.continuous.aemeasurable (by fun_prop)]
    have := wE2_le_of_rv (P := γ) (Z := fun z : H => T z) (W := fun z : H => z)
      T.continuous.aemeasurable aemeasurable_id (c := (ε / 4) ^ 2) (by
      have e : ∀ z : H, ‖T z - z‖ ^ 2 = ‖B z‖ ^ 2 := fun z => by
        rw [hBx, norm_sub_rev]
      simp only [e]
      rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall
        fun ω => by positivity), hsq]
      exact ENNReal.ofReal_le_ofReal hτ0)
    rw [hsqrt] at this
    have e1 : law γ (fun z : H => T z) = γ.map T := rfl
    have e2 : law γ (fun z : H => z) = γ := Measure.map_id
    rwa [e1, e2] at this
  -- assemble
  have hPN : IsProbabilityMeasure (law P (normalizedSum X N)) :=
    haveI : AEMeasurable (normalizedSum X N) P := hmS; inferInstance
  have hPT : IsProbabilityMeasure (law P (fun ω => T (normalizedSum X N ω))) :=
    haveI : AEMeasurable (fun ω => T (normalizedSum X N ω)) P := hTm; inferInstance
  have hγT : IsProbabilityMeasure (γ.map T) :=
    haveI : AEMeasurable T γ := T.continuous.aemeasurable; inferInstance
  haveI : IsProbabilityMeasure γ := hγG.toIsProbabilityMeasure
  have t1 := wassersteinE_triangle 2 (by norm_num) (law P (normalizedSum X N))
    (law P (fun ω => T (normalizedSum X N ω))) γ
  have t2 := wassersteinE_triangle 2 (by norm_num) (law P (fun ω => T (normalizedSum X N ω)))
    (γ.map T) γ
  calc wassersteinE 2 (law P (normalizedSum X N)) γ
      ≤ wassersteinE 2 (law P (normalizedSum X N)) (law P (fun ω => T (normalizedSum X N ω))) +
        wassersteinE 2 (law P (fun ω => T (normalizedSum X N ω))) γ := t1
    _ ≤ ENNReal.ofReal (ε / 4) + (ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 4)) := by
        gcongr
        exact t2.trans (add_le_add hemb hterm3)
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end HilbertCLTAux
-- END RED

/-- The i.i.d. central limit theorem in `W₂` on a separable Hilbert space (Proposition 4.21,
source lines 5521-5557, the probabilistic core): for i.i.d. centered `X_i` with `E‖X_1‖² < ∞`
and `γ` the centered Gaussian with covariance `Cov(X_1)` (possibly degenerate),
`W₂(Law(N^{-1/2} ∑_{i<N} X_i), γ) → 0`. -/
theorem hilbert_clt_iid {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → H) (hiid : IsIIDCopies P X) (hm : ∀ i, AEMeasurable (X i) P)
    (hL2 : MemLp (X 0) 2 P)
    (hmean : ∫ ω, X 0 ω ∂P = 0) (γ : Measure H) (hγ : IsCenteredGaussian γ)
    (hcov : ∀ x y, ProbabilityTheory.covarianceBilin γ x y =
      ProbabilityTheory.covarianceBilin (law P (X 0)) x y) :
    Tendsto (fun N => wassersteinE 2 (law P (normalizedSum X N)) γ) atTop (𝓝 0) :=
  HilbertCLTAux.hilbert_clt_iid_aux hiid hL2 hm hmean hγ hcov

/-- The uniform (triangular-array) form of the Hilbert CLT used for the uniformity in the
reference density in Proposition 4.21 (source lines 5548-5557: "uniformity via subsequences
and the triangular-array Lindeberg theorem, with varying laws having uniformly small Hilbert
tails"): fix finite-dimensional subspaces `K n`, a tail modulus `τ n → 0` and a bound `M`.
Then for every `ε > 0` there is `N₀` such that, for every i.i.d. centered family whose summand
has `E‖X - Π_{K n} X‖² ≤ τ n` for all `n` and `‖X‖ ≤ M` a.s., and every centered Gaussian `γ`
with the covariance of `X`, `W₂(Law(N^{-1/2}∑X_i), γ) ≤ ε` for all `N ≥ N₀`.
The a.s. bound is what Proposition 4.21 has (the summand `(δ_x - μ, Z(x))` is bounded in
`H^{-m}_0 ⊕ ℋ`); a bound on `E‖X‖²` alone would not suffice (no uniform Lindeberg
condition: `X = ±√M` with probability `1/(2M)` each, `M = N`, is a Poisson regime). -/
theorem hilbert_clt_uniform (K : ℕ → Submodule ℝ H) [∀ n, (K n).HasOrthogonalProjection]
    (hK : ∀ n, FiniteDimensional ℝ (K n)) (τ : ℕ → ℝ) (hτ : Tendsto τ atTop (𝓝 0))
    (M : ℝ) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : ℕ → Ω → H), IsIIDCopies P X → (∀ i, AEMeasurable (X i) P) →
      MemLp (X 0) 2 P →
      ∫ ω, X 0 ω ∂P = 0 →
      (∀ n, ∫ ω, ‖X 0 ω - (K n).starProjection (X 0 ω)‖ ^ 2 ∂P ≤ τ n) →
      (∀ᵐ ω ∂P, ‖X 0 ω‖ ≤ M) →
      ∀ γ : Measure H, IsCenteredGaussian γ →
        (∀ x y, ProbabilityTheory.covarianceBilin γ x y =
          ProbabilityTheory.covarianceBilin (law P (X 0)) x y) →
        wassersteinE 2 (law P (normalizedSum X N)) γ ≤ ENNReal.ofReal ε :=
  HilbertCLTAux.hilbert_clt_uniform_aux K hK τ hτ M

/-- `O:eq:fourth-sum` (source line 5540 region): for i.i.d. centered summands with a finite
fourth moment, `E‖N^{-1/2}∑_{i<N} X_i‖⁴ ≤ N⁻¹ E‖X_1‖⁴ + 3 (E‖X_1‖²)²`. -/
theorem iid_fourth_moment_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → H) (hiid : IsIIDCopies P X)
    (hm : ∀ i, AEMeasurable (X i) P) (hL4 : MemLp (X 0) 4 P)
    (hmean : ∫ ω, X 0 ω ∂P = 0) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, ‖normalizedSum X N ω‖ ^ 4 ∂P ≤
      (N : ℝ)⁻¹ * ∫ ω, ‖X 0 ω‖ ^ 4 ∂P + 3 * (∫ ω, ‖X 0 ω‖ ^ 2 ∂P) ^ 2 :=
  HilbertCLTAux.iid_fourth_aux hiid hL4 hm hmean N hN

/-- "Weak convergence and convergence of second moments imply `W₂` convergence in a separable
Hilbert space" (source line 5545 region; external: Villani, *Optimal transport*, Thm 6.9).
Second moments are taken as `lintegral`s so that no finiteness is presupposed. -/
theorem wassersteinE_two_tendsto_of_weak (μn : ℕ → ProbabilityMeasure H) (μ : ProbabilityMeasure H)
    (hweak : Tendsto μn atTop (𝓝 μ))
    (hfin : ∫⁻ x, ‖x‖ₑ ^ 2 ∂(μ : Measure H) < ∞)
    (hmom : Tendsto (fun n => ∫⁻ x, ‖x‖ₑ ^ 2 ∂(μn n : Measure H)) atTop
      (𝓝 (∫⁻ x, ‖x‖ₑ ^ 2 ∂(μ : Measure H)))) :
    Tendsto (fun n => wassersteinE 2 (μn n : Measure H) (μ : Measure H)) atTop (𝓝 0) :=
  HilbertCLTAux.wE2_tendsto_aux μn μ hweak hfin hmom

end HilbertCLT

end HRS

end
