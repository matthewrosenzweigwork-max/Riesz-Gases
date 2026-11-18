/-
# HRS.Equilibrium.FieldSingAux — helpers for Proposition 2.4 (`field_singularity`)

Abstract part: a sequence of jointly Gaussian centred variables whose finite linear combinations
have variance at least `c ‖a‖²` is a.s. unbounded (small-ball estimate by peeling off the
`L²`-residual of the last coordinate).
-/
import HRS.Equilibrium.StaticLimitsAux

open MeasureTheory ProbabilityTheory Set NNReal ENNReal
open scoped InnerProductSpace

noncomputable section

namespace HRS.FieldSingAux

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma gaussianReal_scale (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianReal 0 v = (gaussianReal 0 1).map (fun x => Real.sqrt v * x) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt]

lemma gauss_tail_lower (c : ℝ) (hc : 0 < c) (v : ℝ≥0) (hcv : c ≤ (v : ℝ)) (M : ℝ) (hM : 0 ≤ M) :
    gaussianReal 0 1 (Ioi (M / Real.sqrt c)) ≤ gaussianReal 0 v (Ioi M) ∧
    gaussianReal 0 1 (Iio (-(M / Real.sqrt c))) ≤ gaussianReal 0 v (Iio (-M)) := by
  have hv0 : v ≠ 0 := by
    intro h; rw [h] at hcv; simp at hcv; linarith
  have hvpos : 0 < (v : ℝ) := lt_of_lt_of_le hc hcv
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.2 hvpos
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hle : Real.sqrt c ≤ Real.sqrt v := Real.sqrt_le_sqrt hcv
  have hmeas : Measurable (fun x : ℝ => Real.sqrt v * x) := measurable_const.mul measurable_id
  have hdiv : M / Real.sqrt v ≤ M / Real.sqrt c := div_le_div_of_nonneg_left hM hsc hle
  rw [gaussianReal_scale v hv0]
  constructor
  · rw [Measure.map_apply hmeas measurableSet_Ioi]
    refine measure_mono fun x hx => ?_
    simp only [mem_Ioi, mem_preimage] at hx ⊢
    rw [← div_lt_iff₀' hsv]
    exact lt_of_le_of_lt hdiv hx
  · rw [Measure.map_apply hmeas measurableSet_Iio]
    refine measure_mono fun x hx => ?_
    simp only [mem_Iio, mem_preimage] at hx ⊢
    have : x < -(M / Real.sqrt v) := lt_of_lt_of_le hx (neg_le_neg hdiv)
    rw [← neg_div] at this
    rwa [lt_div_iff₀' hsv] at this

lemma gauss_pos_tails (a : ℝ) : 0 < gaussianReal 0 1 (Ioi a) ∧ 0 < gaussianReal 0 1 (Iio a) := by
  have hac := gaussianReal_absolutelyContinuous' 0 (v := 1) one_ne_zero
  constructor
  · by_contra h
    have h0 : gaussianReal 0 1 (Ioi a) = 0 := by simpa using h
    have := hac h0
    simp at this
  · by_contra h
    have h0 : gaussianReal 0 1 (Iio a) = 0 := by simpa using h
    have := hac h0
    simp at this

/-- uniform small-ball: probability that a variance-≥c centred gaussian lies in a unit-width-`2M`
interval is at most `1 - p`. -/
lemma gauss_ball_le (c : ℝ) (hc : 0 < c) (M : ℝ) (hM : 0 ≤ M) :
    ∃ q : ℝ≥0∞, q < 1 ∧ ∀ v : ℝ≥0, c ≤ (v : ℝ) → ∀ t : ℝ,
      gaussianReal 0 v {z | |z + t| ≤ M} ≤ q := by
  set p1 := gaussianReal 0 1 (Ioi (M / Real.sqrt c))
  set p2 := gaussianReal 0 1 (Iio (-(M / Real.sqrt c)))
  have h1 : 0 < p1 := (gauss_pos_tails _).1
  have h2 : 0 < p2 := (gauss_pos_tails _).2
  refine ⟨1 - min p1 p2, ?_, fun v hv t => ?_⟩
  · have hp : min p1 p2 ≤ 1 := (min_le_left _ _).trans prob_le_one
    exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (lt_min h1 h2).ne'
  · have hv0 : v ≠ 0 := by
      intro h; rw [h] at hv; simp at hv; linarith
    haveI : IsProbabilityMeasure (gaussianReal 0 v) := inferInstance
    obtain ⟨a1, a2⟩ := gauss_tail_lower c hc v hv M hM
    have hcompl : min p1 p2 ≤ gaussianReal 0 v {z | |z + t| ≤ M}ᶜ := by
      rcases le_total 0 t with ht | ht
      · refine (min_le_left _ _).trans (a1.trans (measure_mono fun z hz => ?_))
        simp only [mem_Ioi] at hz
        simp only [mem_compl_iff, mem_setOf_eq, not_le]
        rw [abs_of_pos (by linarith)]; linarith
      · refine (min_le_right _ _).trans (a2.trans (measure_mono fun z hz => ?_))
        simp only [mem_Iio] at hz
        simp only [mem_compl_iff, mem_setOf_eq, not_le]
        rw [abs_of_neg (by linarith)]; linarith
    have hms : MeasurableSet {z : ℝ | |z + t| ≤ M} :=
      measurableSet_le (by fun_prop) measurable_const
    rw [prob_compl_eq_one_sub hms] at hcompl
    have hle : gaussianReal 0 v {z | |z + t| ≤ M} ≤ 1 := prob_le_one
    calc gaussianReal 0 v {z | |z + t| ≤ M}
        = 1 - (1 - gaussianReal 0 v {z | |z + t| ≤ M}) := by
          rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hle]
      _ ≤ 1 - min p1 p2 := tsub_le_tsub_left hcompl _

/-- Residual of `X n` on the span of `X 0, …, X (n-1)` in `L²`. -/
lemma exists_residual (X : ℕ → Ω → ℝ) (hm2 : ∀ i, MemLp (X i) 2 P) (n : ℕ) :
    ∃ b : Fin n → ℝ, ∀ j : Fin n,
      ∫ ω, (X n ω - ∑ i, b i * X i ω) * X j ω ∂P = 0 := by
  classical
  set xs : Fin n → Lp ℝ 2 P := fun i => (hm2 i).toLp (X i) with hxs
  set U := Submodule.span ℝ (Set.range xs) with hU
  haveI : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range xs)
  set p := U.starProjection ((hm2 n).toLp (X n)) with hp
  have hpU : p ∈ U := U.starProjection_apply_mem _
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hpU
  refine ⟨b, fun j => ?_⟩
  have horth : ⟪(hm2 n).toLp (X n) - p, xs j⟫_ℝ = 0 :=
    U.starProjection_inner_eq_zero _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have inner_xs : ∀ f g : ℕ, ⟪(hm2 f).toLp (X f), (hm2 g).toLp (X g)⟫_ℝ = ∫ ω, X f ω * X g ω ∂P := by
    intro f g
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(hm2 f).coeFn_toLp, (hm2 g).coeFn_toLp] with ω h1 h2
    rw [h1, h2]
    simp [mul_comm]
  rw [← hb, inner_sub_left, sum_inner] at horth
  simp only [inner_smul_left, hxs] at horth
  rw [inner_xs] at horth
  have e2 : ∀ i : Fin n, ⟪(hm2 i).toLp (X i), (hm2 j).toLp (X j)⟫_ℝ = ∫ ω, X i ω * X j ω ∂P :=
    fun i => inner_xs i j
  simp only [e2] at horth
  simp only [conj_trivial] at horth
  have hi : ∀ f g : ℕ, Integrable (fun ω => X f ω * X g ω) P := fun f g => (hm2 f).integrable_mul (hm2 g)
  have : ∫ ω, (X n ω - ∑ i : Fin n, b i * X i ω) * X j ω ∂P
      = ∫ ω, X n ω * X j ω ∂P - ∑ i : Fin n, b i * ∫ ω, X i ω * X j ω ∂P := by
    simp_rw [sub_mul, Finset.sum_mul, mul_assoc]
    rw [integral_sub (hi n j), integral_finset_sum]
    · simp_rw [integral_const_mul]
    · intro i _
      exact (hi i j).const_mul _
    · exact integrable_finset_sum _ fun i _ => ((hi i j).const_mul (b i))
  rw [this]
  exact horth


lemma step (X : ℕ → Ω → ℝ) (hX : ∀ n, HasGaussianLaw (fun ω (i : Fin n) => X i ω) P)
    (h0 : ∀ i, P[X i] = 0) (c : ℝ) (hc : 0 < c)
    (hcov : ∀ (n : ℕ) (a : Fin n → ℝ), c * ∑ i, a i ^ 2 ≤ ∫ ω, (∑ i, a i * X i ω) ^ 2 ∂P)
    (M : ℝ) (q : ℝ≥0∞)
    (hq : ∀ v : ℝ≥0, c ≤ (v : ℝ) → ∀ t : ℝ, gaussianReal 0 v {z | |z + t| ≤ M} ≤ q) (n : ℕ) :
    P {ω | ∀ i : Fin (n + 1), |X i ω| ≤ M} ≤ q * P {ω | ∀ i : Fin n, |X i ω| ≤ M} := by
  classical
  have hg : ∀ i, HasGaussianLaw (X i) P := fun i => by
    have := (hX (i + 1)).eval (Fin.last i)
    simpa using this
  have hm2 : ∀ i, MemLp (X i) 2 P := fun i => (hg i).memLp_two
  obtain ⟨b, hb⟩ := exists_residual P X hm2 n
  set Z : Ω → ℝ := fun ω => X n ω - ∑ i, b i * X i ω with hZ
  set V : Ω → (Fin n → ℝ) := fun ω i => X i ω with hV
  -- the linear map
  let Ψ : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin 2 → Option (Fin n) → ℝ) :=
    { toFun := fun u i k => if i = 0 then
          (k.elim (u (Fin.last n) - ∑ j, b j * u (Fin.castSucc j)) (fun _ => 0))
        else (k.elim 0 (fun j => u (Fin.castSucc j)))
      map_add' := by
        intro u w
        ext i k
        by_cases hi : i = 0 <;> cases k <;> simp [hi, Finset.sum_add_distrib, mul_add]
        ring
      map_smul' := by
        intro r u
        ext i k
        by_cases hi : i = 0 <;> cases k <;> simp [hi, Finset.mul_sum, mul_left_comm, mul_sub] }
  let Xb : Fin 2 → Option (Fin n) → Ω → ℝ := fun i k ω =>
    if i = 0 then (k.elim (Z ω) (fun _ => 0)) else (k.elim 0 (fun j => X j ω))
  have hW : HasGaussianLaw (fun ω i k => Xb i k ω) P := by
    have := (hX (n + 1)).map_fun (LinearMap.toContinuousLinearMap Ψ)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    ext i k
    simp [Xb, Ψ, Z]
  have hint : ∀ i : Fin n, Integrable (fun ω => b i * X i ω) P := fun i =>
    ((hm2 i).integrable (by simp)).const_mul _
  have hsumint : Integrable (fun ω => ∑ i : Fin n, b i * X i ω) P :=
    integrable_finsetSum _ fun i _ => hint i
  have hZ0 : P[Z] = 0 := by
    simp only [hZ]
    rw [integral_sub ((hm2 n).integrable (by simp)) hsumint, h0 n,
      integral_finsetSum _ fun i _ => hint i]
    simp [integral_const_mul, h0]
  have hZm : MemLp Z 2 P := by
    refine (hm2 n).sub ?_
    exact memLp_finset_sum _ fun i _ => (hm2 i).const_mul _
  have key : ∀ j : Fin n, cov[Z, X j; P] = 0 := by
    intro j
    rw [covariance_eq_sub hZm (hm2 j), hZ0, h0]
    have := hb j
    simpa using this
  have hcomm : ∀ j : Fin n, cov[X j, Z; P] = 0 := fun j => by
    rw [covariance_comm]; exact key j
  have hcovXb : ∀ i j : Fin 2, i ≠ j → ∀ k l, cov[Xb i k, Xb j l; P] = 0 := by
    have h01 : ∀ k l, cov[Xb 0 k, Xb 1 l; P] = 0 := by
      intro k l
      cases k <;> cases l
      · simp [Xb, covariance]
      · rename_i j
        have := key j
        simpa [Xb] using this
      · simp [Xb, covariance]
      · simp [Xb, covariance]
    intro i j hij k l
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact h01 k l
    · rw [covariance_comm]; exact h01 l k
    · exact absurd rfl hij
  have hindep := hW.iIndepFun_of_covariance_eval (X := Xb) hcovXb
  have hindep := hW.iIndepFun_of_covariance_eval (X := Xb) hcovXb
  have hZg : HasGaussianLaw Z P := by
    have h1 : HasGaussianLaw (fun ω k => Xb 0 k ω) P := hW.eval 0
    have h2 : HasGaussianLaw (fun ω => Xb 0 none ω) P := h1.eval none
    simpa [Xb] using h2
  -- variance lower bound
  have hvar : c ≤ ∫ ω, Z ω ^ 2 ∂P := by
    set a : Fin (n + 1) → ℝ := fun i => if h : (i : ℕ) < n then -b ⟨i, h⟩ else 1 with ha
    have hsum : ∀ ω, ∑ i, a i * X i ω = Z ω := by
      intro ω
      rw [Fin.sum_univ_castSucc]
      simp [a, Z, sub_eq_add_neg, Finset.sum_neg_distrib]
      ring
    have h1 : 1 ≤ ∑ i, a i ^ 2 := by
      rw [Fin.sum_univ_castSucc]
      have : a (Fin.last n) = 1 := by simp [a]
      rw [this]
      have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (a (Fin.castSucc i)))
      linarith
    have := hcov (n + 1) a
    simp_rw [hsum] at this
    nlinarith
  have hlawZ : P.map Z = gaussianReal 0 (ProbabilityTheory.variance Z P).toNNReal := by
    have := hZg.map_eq_gaussianReal
    rwa [hZ0] at this
  have hvarZ : ProbabilityTheory.variance Z P = ∫ ω, Z ω ^ 2 ∂P :=
    variance_of_integral_eq_zero hZg.aemeasurable hZ0
  have hvge : c ≤ (((ProbabilityTheory.variance Z P).toNNReal : ℝ≥0) : ℝ) := by
    rw [Real.coe_toNNReal _ (variance_nonneg _ _), hvarZ]; exact hvar
  -- independence
  have hind2 : IndepFun (fun ω k => Xb 0 k ω) (fun ω k => Xb 1 k ω) P :=
    hindep.indepFun (by decide : (0 : Fin 2) ≠ 1)
  have hind3 : IndepFun Z V P := by
    have m1 : Measurable (fun f : Option (Fin n) → ℝ => f none) := measurable_pi_apply none
    have m2 : Measurable (fun f : Option (Fin n) → ℝ => fun j : Fin n => f (some j)) :=
      measurable_pi_iff.2 fun j => measurable_pi_apply (some j)
    have := hind2.comp m1 m2
    have e1 : ((fun f : Option (Fin n) → ℝ => f none) ∘ fun ω k => Xb 0 k ω) = Z := by
      ext ω; simp [Xb]
    have e2 : ((fun f : Option (Fin n) → ℝ => fun j : Fin n => f (some j)) ∘ fun ω k => Xb 1 k ω) = V := by
      ext ω j; simp [Xb, hV]
    rwa [e1, e2] at this
  have hZmeas : AEMeasurable Z P := hZg.aemeasurable
  have hVmeas : AEMeasurable V P := by
    exact aemeasurable_pi_iff.2 fun j => (hg j).aemeasurable
  set A' : Set (Fin n → ℝ) := {v | ∀ j, |v j| ≤ M} with hA'
  set 𝔅 : Set (ℝ × (Fin n → ℝ)) := {w | w.2 ∈ A' ∧ |w.1 + ∑ i, b i * w.2 i| ≤ M} with hB
  have hA'm : MeasurableSet A' := by
    have : A' = ⋂ j, {v : Fin n → ℝ | |v j| ≤ M} := by ext; simp [A']
    rw [this]
    exact MeasurableSet.iInter fun j => measurableSet_le (by fun_prop) measurable_const
  have hBm : MeasurableSet 𝔅 := by
    have h2 : MeasurableSet {w : ℝ × (Fin n → ℝ) | |w.1 + ∑ i, b i * w.2 i| ≤ M} :=
      measurableSet_le (by fun_prop) measurable_const
    exact (measurable_snd hA'm).inter h2
  have hsub : {ω | ∀ i : Fin (n + 1), |X i ω| ≤ M} ⊆ (fun ω => (Z ω, V ω)) ⁻¹' 𝔅 := by
    intro ω hω
    simp only [mem_setOf_eq] at hω
    refine ⟨fun j => ?_, ?_⟩
    · have := hω (Fin.castSucc j); simpa [V] using this
    · have := hω (Fin.last n); simpa [Z, V] using this
  calc P {ω | ∀ i : Fin (n + 1), |X i ω| ≤ M}
      ≤ P ((fun ω => (Z ω, V ω)) ⁻¹' 𝔅) := measure_mono hsub
    _ = (P.map (fun ω => (Z ω, V ω))) 𝔅 :=
        (Measure.map_apply_of_aemeasurable (hZmeas.prodMk hVmeas) hBm).symm
    _ = ((P.map Z).prod (P.map V)) 𝔅 := by
        rw [(indepFun_iff_map_prod_eq_prod_map_map hZmeas hVmeas).1 hind3]
    _ = ∫⁻ v, (P.map Z) ((fun z => (z, v)) ⁻¹' 𝔅) ∂(P.map V) := Measure.prod_apply_symm hBm
    _ ≤ ∫⁻ v, q * A'.indicator 1 v ∂(P.map V) := by
        refine lintegral_mono fun v => ?_
        by_cases hv : v ∈ A'
        · have : (fun z => (z, v)) ⁻¹' 𝔅 = {z | |z + ∑ i, b i * v i| ≤ M} := by
            ext z; simp [hB, hv]
          rw [this, hlawZ]
          simpa [hv] using hq _ hvge _
        · have : (fun z => (z, v)) ⁻¹' 𝔅 = ∅ := by
            ext z; simp [hB, hv]
          rw [this]; simp
    _ = q * (P.map V) A' := by
        rw [lintegral_const_mul _ (measurable_one.indicator hA'm), lintegral_indicator_one hA'm]
    _ = q * P {ω | ∀ i : Fin n, |X i ω| ≤ M} := by
        rw [Measure.map_apply_of_aemeasurable hVmeas hA'm]; rfl


theorem sup_unbounded (X : ℕ → Ω → ℝ) (hX : ∀ n, HasGaussianLaw (fun ω (i : Fin n) => X i ω) P)
    (h0 : ∀ i, P[X i] = 0) (c : ℝ) (hc : 0 < c)
    (hcov : ∀ (n : ℕ) (a : Fin n → ℝ), c * ∑ i, a i ^ 2 ≤ ∫ ω, (∑ i, a i * X i ω) ^ 2 ∂P) :
    P {ω | ∃ M : ℕ, ∀ i, |X i ω| ≤ M} = 0 := by
  have hU : {ω | ∃ M : ℕ, ∀ i, |X i ω| ≤ M} = ⋃ M : ℕ, {ω | ∀ i, |X i ω| ≤ M} := by
    ext ω; simp
  rw [hU]
  refine measure_iUnion_null fun M => ?_
  obtain ⟨q, hq1, hq⟩ := gauss_ball_le c hc M (by positivity)
  have hind : ∀ n : ℕ, P {ω | ∀ i : Fin n, |X i ω| ≤ M} ≤ q ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc P {ω | ∀ i : Fin (n + 1), |X i ω| ≤ M}
          ≤ q * P {ω | ∀ i : Fin n, |X i ω| ≤ M} := step P X hX h0 c hc hcov M q hq n
        _ ≤ q * q ^ n := by gcongr
        _ = q ^ (n + 1) := by rw [pow_succ']
  have hle : ∀ n : ℕ, P {ω | ∀ i, |X i ω| ≤ M} ≤ q ^ n := fun n =>
    le_trans (measure_mono (fun ω (hω : ω ∈ {ω | ∀ i, |X i ω| ≤ M}) =>
      (fun (i : Fin n) => hω i) : {ω | ∀ i, |X i ω| ≤ M} ⊆ {ω | ∀ i : Fin n, |X i ω| ≤ M})) (hind n)
  have ht := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq1
  exact le_antisymm (ge_of_tendsto' ht hle) bot_le


section Sobolev

variable {d : ℕ} {m : ℝ}

lemma continuous_realMode (k : NonzeroLattice d) : Continuous (Torus.realMode k) := by
  unfold Torus.realMode
  split_ifs
  · exact continuous_const.mul (Torus.continuous_cosMode _)
  · exact continuous_const.mul (Torus.continuous_sinMode _)

open Classical in
lemma isSmooth_realMode (k : NonzeroLattice d) : Torus.IsSmooth (Torus.realMode k) := by
  unfold Torus.IsSmooth Torus.IsCk
  have hdot : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Euc d => Lattice.dot k.1 y) := by
    unfold Lattice.dot
    refine ContDiff.sum fun i _ => contDiff_const.mul ?_
    exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
  have hlift : Torus.lift (Torus.realMode k) = fun y : Euc d =>
      if Lattice.IsPosHalf k.1 then Real.sqrt 2 * Real.cos (2 * Real.pi * Lattice.dot k.1 y)
      else Real.sqrt 2 * Real.sin (2 * Real.pi * Lattice.dot k.1 y) := by
    funext y
    unfold Torus.lift Torus.realMode
    simp only [Function.comp, Torus.cosMode_mk, Torus.sinMode_mk]
  rw [hlift]
  split_ifs
  · exact contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul hdot))
  · exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul hdot))

/-- the trigonometric polynomial with prescribed real coefficients on a finite set -/
def trigPoly (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) : Torus d → ℝ :=
  fun x => ∑ k ∈ T, c k * Torus.realMode k x

lemma isSmooth_trigPoly (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) :
    Torus.IsSmooth (trigPoly T c) := by
  unfold Torus.IsSmooth Torus.IsCk
  have : Torus.lift (trigPoly T c) = fun y => ∑ k ∈ T, c k * Torus.lift (Torus.realMode k) y := by
    funext y; simp [Torus.lift, trigPoly]
  rw [this]
  refine ContDiff.sum fun k _ => contDiff_const.mul ?_
  exact isSmooth_realMode k

lemma integrable_realMode_mul (k l : NonzeroLattice d) :
    Integrable (fun x => Torus.realMode k x * Torus.realMode l x) :=
  ((continuous_realMode k).mul (continuous_realMode l)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma funRealCoeff_trigPoly (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ)
    (k : NonzeroLattice d) :
    Torus.funRealCoeff (trigPoly T c) k = if k ∈ T then c k else 0 := by
  unfold Torus.funRealCoeff trigPoly
  have : ∀ x, Torus.realMode k x * ∑ l ∈ T, c l * Torus.realMode l x =
      ∑ l ∈ T, c l * (Torus.realMode k x * Torus.realMode l x) := by
    intro x; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
  simp_rw [this]
  rw [integral_finsetSum _ fun l _ => (integrable_realMode_mul k l).const_mul _]
  simp_rw [integral_const_mul, Torus.realMode_orthonormal]
  simp [Finset.sum_ite_eq]

lemma integral_trigPoly_sq (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) :
    ∫ x, trigPoly T c x ^ 2 = ∑ k ∈ T, c k ^ 2 := by
  have : ∀ x, trigPoly T c x ^ 2 = ∑ k ∈ T, ∑ l ∈ T,
      c k * c l * (Torus.realMode k x * Torus.realMode l x) := by
    intro x; unfold trigPoly; rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [this]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    (integrable_realMode_mul k l).const_mul _]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_finsetSum _ fun l _ => (integrable_realMode_mul k l).const_mul _]
  simp_rw [integral_const_mul, Torus.realMode_orthonormal]
  simp [Finset.sum_ite_eq, hk, sq]

lemma mean_trigPoly (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) :
    Torus.mean (trigPoly T c) = 0 := by
  unfold Torus.mean trigPoly
  have hi : ∀ k, Integrable (fun x => c k * Torus.realMode k x) := fun k =>
    ((continuous_realMode k).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  rw [integral_finsetSum _ fun k _ => hi k]
  simp [integral_const_mul, Torus.integral_realMode]

lemma eval_trigPoly (F : NegSobolev d m) (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) :
    NegSobolev.eval F (trigPoly T c) = ∑ k ∈ T, c k * NegSobolev.fourierCoeff F k := by
  unfold NegSobolev.eval
  rw [tsum_eq_sum (s := T)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [funRealCoeff_trigPoly, if_pos hk]; ring
  · intro k hk
    rw [funRealCoeff_trigPoly, if_neg hk]; ring

/-- the coordinate `F ↦ F̂(k)` as a continuous linear functional -/
def coordCLM (m : ℝ) (k : NonzeroLattice d) : NegSobolev d m →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun F => NegSobolev.fourierCoeff F k
      map_add' := fun F G => by
        unfold NegSobolev.fourierCoeff NegSobolev.coord
        rw [← mul_add]; rfl
      map_smul' := fun r F => by
        show Lattice.jp k.1 ^ m * (r * NegSobolev.coord F k) =
          r * (Lattice.jp k.1 ^ m * NegSobolev.coord F k)
        ring }
    (Lattice.jp k.1 ^ m) (fun F => by
      show |Lattice.jp k.1 ^ m * NegSobolev.coord F k| ≤ _
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (Torus.jp_pos k.1) m)]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos (Torus.jp_pos k.1) m).le
      exact lp.norm_apply_le_norm (by norm_num) (F : lp (fun _ : NonzeroLattice d => ℝ) 2) k)

lemma coordCLM_apply (k : NonzeroLattice d) (F : NegSobolev d m) :
    coordCLM m k F = NegSobolev.fourierCoeff F k := rfl


def kseq (hd : 1 ≤ d) (n : ℕ) : NonzeroLattice d :=
  ⟨fun i => if i = ⟨0, hd⟩ then ((n : ℤ) + 1) else 0, by
    intro h
    have := congrFun h ⟨0, hd⟩
    simp at this
    omega⟩

lemma kseq_injective (hd : 1 ≤ d) : Function.Injective (kseq hd) := by
  intro a b h
  have := congrFun (congrArg Subtype.val h) ⟨0, hd⟩
  simp [kseq] at this
  omega

lemma measurable_fourierCoeff (k : NonzeroLattice d) :
    Measurable (fun F : NegSobolev d m => NegSobolev.fourierCoeff F k) :=
  (coordCLM m k).continuous.measurable

lemma fourierCoeff_smul (r : ℝ) (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (r • F) k = r * NegSobolev.fourierCoeff F k :=
  (coordCLM m k).map_smul r F

/-- Under the hypotheses of Proposition 2.4, the unweighted Fourier coefficients along the
sequence `kseq` are almost surely unbounded. -/
theorem coeff_unbounded (hd : 1 ≤ d) (γ : Measure (NegSobolev d m)) [IsProbabilityMeasure γ]
    (hG : IsGaussian γ) (hmean : ∀ L : StrongDual ℝ (NegSobolev d m), ∫ z, L z ∂γ = 0)
    (c : ℝ) (hc : 0 < c)
    (hlow : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → Torus.mean φ = 0 →
      c * ∫ x, φ x ^ 2 ≤ ∫ F, NegSobolev.eval F φ ^ 2 ∂γ) :
    γ {F | ∃ M : ℕ, ∀ i, |NegSobolev.fourierCoeff F (kseq hd i)| ≤ M} = 0 := by
  refine sup_unbounded γ (fun i F => NegSobolev.fourierCoeff F (kseq hd i)) ?_ ?_ c hc ?_
  · intro n
    have h1 : HasGaussianLaw id γ := IsGaussian.hasGaussianLaw_id
    have := h1.map_fun (ContinuousLinearMap.pi fun i : Fin n => coordCLM m (kseq hd i))
    exact this
  · intro i
    exact hmean (coordCLM m (kseq hd i))
  · intro n a
    classical
    set cc : NonzeroLattice d → ℝ := Function.extend (fun i : Fin n => kseq hd i) a 0 with hcc
    have hinj : Function.Injective (fun i : Fin n => kseq hd i) :=
      (kseq_injective hd).comp Fin.val_injective
    have hcca : ∀ i : Fin n, cc (kseq hd i) = a i := fun i => hinj.extend_apply a 0 i
    set T : Finset (NonzeroLattice d) := Finset.univ.image (fun i : Fin n => kseq hd i) with hT
    have hsum : ∀ g : NonzeroLattice d → ℝ, ∑ k ∈ T, cc k * g k = ∑ i : Fin n, a i * g (kseq hd i) := by
      intro g
      rw [hT, Finset.sum_image (fun x _ y _ h => hinj h)]
      exact Finset.sum_congr rfl fun i _ => by rw [hcca]
    have hsq : ∑ k ∈ T, cc k ^ 2 = ∑ i : Fin n, a i ^ 2 := by
      have := hsum (fun k => cc k)
      rw [hT, Finset.sum_image (fun x _ y _ h => hinj h)]
      exact Finset.sum_congr rfl fun i _ => by rw [hcca]
    have h := hlow (trigPoly T cc) (isSmooth_trigPoly T cc) (mean_trigPoly T cc)
    rw [integral_trigPoly_sq, hsq] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    funext F
    rw [eval_trigPoly, hsum]


lemma gamma_singleton_null (hd : 1 ≤ d) (γ : Measure (NegSobolev d m)) [IsProbabilityMeasure γ]
    (hG : IsGaussian γ) (hmean : ∀ L : StrongDual ℝ (NegSobolev d m), ∫ z, L z ∂γ = 0)
    (c : ℝ) (hc : 0 < c)
    (hlow : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → Torus.mean φ = 0 →
      c * ∫ x, φ x ^ 2 ≤ ∫ F, NegSobolev.eval F φ ^ 2 ∂γ) (x0 : NegSobolev d m) :
    γ {x0} = 0 := by
  classical
  set L := coordCLM m (kseq hd 0) with hL
  have h1 : HasGaussianLaw id γ := IsGaussian.hasGaussianLaw_id
  have hLg : HasGaussianLaw (fun F => L F) γ := h1.map_fun L
  have hm0 : γ[fun F => L F] = 0 := hmean L
  have hmap := hLg.map_eq_gaussianReal
  rw [hm0] at hmap
  have hvar : ProbabilityTheory.variance (fun F => L F) γ = ∫ F, L F ^ 2 ∂γ :=
    variance_of_integral_eq_zero hLg.aemeasurable hm0
  have hc' : c ≤ ∫ F, L F ^ 2 ∂γ := by
    have h := hlow (trigPoly {kseq hd 0} (fun _ => 1)) (isSmooth_trigPoly _ _) (mean_trigPoly _ _)
    rw [integral_trigPoly_sq] at h
    simp only [Finset.sum_singleton, one_pow, mul_one] at h
    refine h.trans (le_of_eq ?_)
    congr 1
    funext F
    rw [eval_trigPoly]
    simp [hL, coordCLM_apply]
  have hv0 : (ProbabilityTheory.variance (fun F => L F) γ).toNNReal ≠ 0 := by
    intro h
    rw [Real.toNNReal_eq_zero] at h
    rw [hvar] at h
    linarith
  have hsub : γ {x0} ≤ γ ((fun F => L F) ⁻¹' {L x0}) :=
    measure_mono fun F hF => by simp at hF; simp [hF]
  rw [← Measure.map_apply L.continuous.measurable (measurableSet_singleton _)] at hsub
  have hmap' : γ.map L = gaussianReal 0 (ProbabilityTheory.variance (fun F => L F) γ).toNNReal := hmap
  rw [hmap'] at hsub
  have : gaussianReal 0 (ProbabilityTheory.variance (fun F => L F) γ).toNNReal {L x0} = 0 :=
    gaussianReal_absolutelyContinuous 0 hv0 (by simp)
  exact le_antisymm (this ▸ hsub) bot_le

theorem field_singularity_main (hd : 1 ≤ d) (hm : (d : ℝ) / 2 < m)
    (γ : Measure (NegSobolev d m)) [IsProbabilityMeasure γ] (hγ : IsCenteredGaussian γ)
    (c : ℝ) (hc : 0 < c)
    (hlow : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → Torus.mean φ = 0 →
      c * ∫ x, φ x ^ 2 ≤ ∫ F, NegSobolev.eval F φ ^ 2 ∂γ)
    (N : ℕ) (P : Measure (Config d N)) [IsProbabilityMeasure P] (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] :
    γ ⟂ₘ law P (fun X => Real.sqrt N • NegSobolev.ofMeasureDiff m (empirical X) ν) := by
  classical
  have hm' : (d : ℝ) < 2 * m := by linarith
  set S : Set (NegSobolev d m) :=
    {F | ∃ M : ℕ, ∀ i, |NegSobolev.fourierCoeff F (kseq hd i)| ≤ M} with hS
  have hSm : MeasurableSet S := by
    have : S = ⋃ M : ℕ, ⋂ i, {F : NegSobolev d m | |NegSobolev.fourierCoeff F (kseq hd i)| ≤ M} := by
      ext F; simp [hS]
    rw [this]
    exact MeasurableSet.iUnion fun M => MeasurableSet.iInter fun i =>
      measurableSet_le ((measurable_fourierCoeff _).abs) measurable_const
  have hfS : ∀ X : Config d N,
      (Real.sqrt N • NegSobolev.ofMeasureDiff m (empirical X) ν) ∈ S := by
    intro X
    by_cases hN : N = 0
    · subst hN
      refine ⟨0, fun i => ?_⟩
      have h0 := (coordCLM m (kseq hd i)).map_zero
      rw [coordCLM_apply] at h0
      simp only [Nat.cast_zero, Real.sqrt_zero, zero_smul]
      rw [h0]; simp
    · haveI := empirical_isProbabilityMeasure (Nat.pos_of_ne_zero hN) X
      refine ⟨⌈Real.sqrt N * (Real.sqrt 2 + Real.sqrt 2)⌉₊, fun i => ?_⟩
      rw [fourierCoeff_smul, NegSobolev.fourierCoeff_ofMeasureDiff hm', abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      refine le_trans ?_ (Nat.le_ceil _)
      refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ?_ ?_))
        (Real.sqrt_nonneg _)
      · simpa using NegSobolev.abs_measureRealCoeff_le (empirical X) (kseq hd i)
      · simpa using NegSobolev.abs_measureRealCoeff_le ν (kseq hd i)
  by_cases hf : AEMeasurable (fun X : Config d N => Real.sqrt N • NegSobolev.ofMeasureDiff m (empirical X) ν) P
  · refine ⟨S, hSm, coeff_unbounded hd γ hγ.1 hγ.2 c hc hlow, ?_⟩
    rw [Measure.map_apply_of_aemeasurable hf hSm.compl]
    have : (fun X : Config d N => Real.sqrt N • NegSobolev.ofMeasureDiff m (empirical X) ν) ⁻¹' Sᶜ = ∅ := by
      ext X; simpa using hfS X
    rw [this]; simp
  · obtain ⟨x0, hx0⟩ : ∃ x0, P.map (fun X : Config d N => Real.sqrt N • NegSobolev.ofMeasureDiff m (empirical X) ν)
        = Measure.dirac x0 :=
      ⟨_, Measure.map_of_not_aemeasurable_of_ne_zero hf (IsProbabilityMeasure.ne_zero P)⟩
    refine ⟨S ∪ {x0}, hSm.union (measurableSet_singleton _), ?_, ?_⟩
    · exact le_antisymm ((measure_union_le _ _).trans (by
        rw [coeff_unbounded hd γ hγ.1 hγ.2 c hc hlow,
          gamma_singleton_null hd γ hγ.1 hγ.2 c hc hlow x0]; simp)) bot_le
    · show P.map _ _ = 0
      rw [hx0, Measure.dirac_apply' _ (hSm.union (measurableSet_singleton _)).compl]
      simp

end Sobolev

end HRS.FieldSingAux
