import HRS.MS.WrCalAux1

/-!
# HRS.MS.WrCalAux2 -- the calibration objective on a Hilbert space (WR-11a, part 2)

Abstract objective `J(t) = c * log E_P exp ⟪t,S⟫ + ‖t‖²/(2β)` (`c = 1/N` later) for a bounded strongly
measurable `S : Ω → H`, `H` a real Hilbert space.  Torus template: `CalibratedReference.lean:390, 503, 567`
(there `H = ℝ^M`, minimiser by compactness).  Here the minimiser is obtained from strong convexity:

* `wr11_strongConvexOn_obj`: `J` is `StrongConvexOn univ (1/β)` (Mathlib `Analysis/Convex/Strong.lean`);
* `wr11_exists_min_of_strongConvex`: a continuous bounded-below `m`-strongly convex function on a complete
  inner product space has a minimiser (minimising sequence is Cauchy by the parallelogram law; no weak
  lower semicontinuity); `wr11_min_unique`: the minimiser is unique;
* `wr11_obj_bddBelow`, `wr11_exists_obj_min`;
* `wr11_stationary`: a minimiser `t0` satisfies `t0 = -(β c) • E_{P tilted by ⟪t0,S⟫} S`
  (Gateaux derivative along every direction `v`, then the Riesz-type identification through
  `integral_inner` for the `H`-valued Bochner integral);
* `wr11_norm_le`: `‖t0‖ ≤ β c ‖E_P S‖` (monotonicity of the gradient).
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

section Min

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A continuous, bounded below, `m`-strongly convex function on a complete inner product space attains its
infimum (the minimising sequence is Cauchy by strong convexity, i.e. the parallelogram law). -/
lemma wr11_exists_min_of_strongConvex [CompleteSpace H] {J : H → ℝ} {m : ℝ} (hm : 0 < m)
    (hJ : StrongConvexOn Set.univ m J) (hcont : Continuous J) (hbdd : BddBelow (Set.range J)) :
    ∃ t, ∀ s, J t ≤ J s := by
  set L : ℝ := ⨅ t, J t with hL
  have hLle : ∀ t, L ≤ J t := fun t => ciInf_le hbdd t
  -- strong convexity at the midpoint
  have hmid : ∀ x y : H, m / 8 * ‖x - y‖ ^ 2 ≤ (J x + J y) / 2 - L := by
    intro x y
    have h1 := hJ.2 (Set.mem_univ x) (Set.mem_univ y) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have h2 := hLle ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)
    simp only [smul_eq_mul] at h1
    nlinarith [h1, h2]
  have hex : ∀ n : ℕ, ∃ t : H, J t < L + 1 / ((n : ℝ) + 1) := by
    intro n
    have : L < L + 1 / ((n : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    exact exists_lt_of_ciInf_lt this
  choose u hu using hex
  have hcauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (8 / (m * ε ^ 2))
    refine ⟨N, fun n hn => ?_⟩
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have h1 := hmid (u n) (u N)
    have hun := hu n
    have huN := hu N
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le hNpos (by linarith)
    have h3 : m / 8 * ‖u n - u N‖ ^ 2 ≤ 1 / ((N : ℝ) + 1) := by linarith
    have h4 : 8 / (m * ε ^ 2) < (N : ℝ) + 1 := by linarith
    have h5 : 8 / ((N : ℝ) + 1) < m * ε ^ 2 := by
      rw [div_lt_iff₀ hNpos]
      rw [div_lt_iff₀ (by positivity)] at h4
      nlinarith
    have h6 : ‖u n - u N‖ ^ 2 < ε ^ 2 := by
      have : ‖u n - u N‖ ^ 2 ≤ 8 / m * (1 / ((N : ℝ) + 1)) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hm]
        nlinarith
      refine lt_of_le_of_lt this ?_
      rw [div_mul_eq_mul_div, div_lt_iff₀ hm]
      have e : 8 * (1 / ((N : ℝ) + 1)) = 8 / ((N : ℝ) + 1) := by ring
      rw [e]
      linarith
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h6
  obtain ⟨t, ht⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hJt : Tendsto (fun n => J (u n)) atTop (𝓝 (J t)) := (hcont.tendsto t).comp ht
  have hJL : Tendsto (fun n => J (u n)) atTop (𝓝 L) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => hLle (u n)) (fun n => (hu n).le)
    have : Tendsto (fun n : ℕ => L + 1 / ((n : ℝ) + 1)) atTop (𝓝 (L + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using this
  have : J t = L := tendsto_nhds_unique hJt hJL
  exact ⟨t, fun s => by rw [this]; exact hLle s⟩

/-- The minimiser of a strongly convex function is unique. -/
lemma wr11_min_unique {J : H → ℝ} {m : ℝ} (hm : 0 < m) (hJ : StrongConvexOn Set.univ m J) {t₁ t₂ : H}
    (h₁ : ∀ s, J t₁ ≤ J s) (h₂ : ∀ s, J t₂ ≤ J s) : t₁ = t₂ := by
  have h1 := hJ.2 (Set.mem_univ t₁) (Set.mem_univ t₂) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have h2 := h₁ ((1 / 2 : ℝ) • t₁ + (1 / 2 : ℝ) • t₂)
  have h3 := h₁ t₂
  have h4 := h₂ t₁
  simp only [smul_eq_mul] at h1
  have h5 : m / 2 * (1 / 2) * (1 / 2) * ‖t₁ - t₂‖ ^ 2 ≤ 0 := by nlinarith
  have h6 : ‖t₁ - t₂‖ ^ 2 ≤ 0 := by
    by_contra hc
    push_neg at hc
    have : 0 < m / 2 * (1 / 2) * (1 / 2) * ‖t₁ - t₂‖ ^ 2 := by positivity
    linarith
  have : ‖t₁ - t₂‖ = 0 := by nlinarith [norm_nonneg (t₁ - t₂)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

end Min

section Obj

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {S : Ω → H} {C : ℝ}

/-- The calibration objective `c * log E_P exp ⟪t,S⟫ + ‖t‖²/(2β)`. -/
def wr11_obj (c β : ℝ) (P : Measure Ω) (S : Ω → H) (t : H) : ℝ :=
  c * wr11_cF P S t + ‖t‖ ^ 2 / (2 * β)

lemma wr11_continuous_obj [IsProbabilityMeasure P] (h : Wr11Bdd S C) (c β : ℝ) :
    Continuous (wr11_obj c β P S) := by
  unfold wr11_obj
  exact ((wr11_continuous_cF h).const_mul c).add (by fun_prop)

lemma wr11_obj_zero [IsProbabilityMeasure P] (c β : ℝ) : wr11_obj c β P S 0 = 0 := by
  simp [wr11_obj, wr11_cF_zero]

/-- The objective is `1/β`-strongly convex on all of `H`. -/
lemma wr11_strongConvexOn_obj [IsProbabilityMeasure P] (h : Wr11Bdd S C) {c : ℝ} (hc : 0 ≤ c)
    {β : ℝ} (hβ : 0 < β) : StrongConvexOn Set.univ (1 / β) (wr11_obj c β P S) := by
  rw [strongConvexOn_iff_convex]
  have e : (fun x : H => wr11_obj c β P S x - 1 / β / 2 * ‖x‖ ^ 2) = fun x => c • wr11_cF P S x := by
    funext x
    unfold wr11_obj
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [e]
  exact (wr11_convexOn_cF h).smul hc

lemma wr11_integrable_S [IsFiniteMeasure P] (h : Wr11Bdd S C) : Integrable S P :=
  Integrable.of_bound h.meas.aestronglyMeasurable C (Eventually.of_forall fun ω => h.bound ω)

lemma wr11_integral_Ya_eq [CompleteSpace H] (P' : Measure Ω) [IsFiniteMeasure P'] (h : Wr11Bdd S C)
    (t : H) : ∫ ω, wr11_Ya S t ω ∂P' = inner ℝ t (∫ ω, S ω ∂P') :=
  integral_inner (wr11_integrable_S h) t

lemma wr11_obj_bddBelow [CompleteSpace H] [IsProbabilityMeasure P] (h : Wr11Bdd S C) {c : ℝ}
    (hc : 0 ≤ c) {β : ℝ} (hβ : 0 < β) : BddBelow (Set.range (wr11_obj c β P S)) := by
  set m : H := ∫ ω, S ω ∂P with hm
  refine ⟨-(β * c ^ 2 * ‖m‖ ^ 2 / 2), ?_⟩
  rintro _ ⟨t, rfl⟩
  have h1 : inner ℝ t m ≤ wr11_cF P S t := by
    have := wr11_integral_Ya_le_cF (P := P) h t
    rwa [wr11_integral_Ya_eq P h] at this
  have h2 : -(‖t‖ * ‖m‖) ≤ inner ℝ t m := by
    have := abs_real_inner_le_norm t m
    linarith [neg_abs_le (inner ℝ t m)]
  unfold wr11_obj
  have h3 : 0 ≤ (‖t‖ - β * c * ‖m‖) ^ 2 / (2 * β) := by positivity
  have h4 : (‖t‖ - β * c * ‖m‖) ^ 2 / (2 * β) =
      ‖t‖ ^ 2 / (2 * β) - c * (‖t‖ * ‖m‖) + β * c ^ 2 * ‖m‖ ^ 2 / 2 := by
    field_simp
    ring
  have h5 : c * (-(‖t‖ * ‖m‖)) ≤ c * wr11_cF P S t :=
    mul_le_mul_of_nonneg_left (h2.trans h1) hc
  nlinarith [h3, h4, h5]

/-- Existence of a minimiser of the calibration objective. -/
lemma wr11_exists_obj_min [CompleteSpace H] [IsProbabilityMeasure P] (h : Wr11Bdd S C) {c : ℝ}
    (hc : 0 ≤ c) {β : ℝ} (hβ : 0 < β) : ∃ t, ∀ s, wr11_obj c β P S t ≤ wr11_obj c β P S s :=
  wr11_exists_min_of_strongConvex (one_div_pos.2 hβ) (wr11_strongConvexOn_obj h hc hβ)
    (wr11_continuous_obj h c β) (wr11_obj_bddBelow h hc hβ)

lemma wr11_obj_unique [IsProbabilityMeasure P] (h : Wr11Bdd S C) {c : ℝ} (hc : 0 ≤ c) {β : ℝ}
    (hβ : 0 < β) {t₁ t₂ : H} (h₁ : ∀ s, wr11_obj c β P S t₁ ≤ wr11_obj c β P S s)
    (h₂ : ∀ s, wr11_obj c β P S t₂ ≤ wr11_obj c β P S s) : t₁ = t₂ :=
  wr11_min_unique (one_div_pos.2 hβ) (wr11_strongConvexOn_obj h hc hβ) h₁ h₂

/-- Derivative of the objective along the line `s ↦ t + s v` at `s = 0`. -/
lemma wr11_hasDerivAt_obj [IsProbabilityMeasure P] (h : Wr11Bdd S C) (c β : ℝ) (hβ : 0 < β) (t v : H) :
    HasDerivAt (fun s : ℝ => wr11_obj c β P S (t + s • v))
      (c * ∫ ω, wr11_Ya S v ω ∂(P.tilted (wr11_Ya S t)) + inner ℝ t v / β) 0 := by
  have hc := (wr11_hasDerivAt_cF (P := P) h t v).const_mul c
  have hf : HasDerivAt (fun s : ℝ => t + s • v) v 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add t
    simpa using this
  have hn := hf.norm_sq
  have hall := hc.add (hn.div_const (2 * β))
  unfold wr11_obj
  convert hall using 1
  simp
  field_simp

/-- **Stationarity.**  A minimiser `t0` of the calibration objective satisfies `t0 = -(β c) E_{P_{t0}} S`. -/
lemma wr11_stationary [CompleteSpace H] [IsProbabilityMeasure P] (h : Wr11Bdd S C) {c : ℝ} (hc : 0 < c)
    {β : ℝ} (hβ : 0 < β) {t0 : H} (hmin : ∀ s, wr11_obj c β P S t0 ≤ wr11_obj c β P S s) :
    t0 = -(β * c) • ∫ ω, S ω ∂(P.tilted (wr11_Ya S t0)) := by
  have := wr11_isProb_tilted (P := P) h t0
  set m : H := ∫ ω, S ω ∂(P.tilted (wr11_Ya S t0)) with hm
  have hstat : ∀ v : H, inner ℝ v (c • m + (1 / β) • t0) = 0 := by
    intro v
    have hd := wr11_hasDerivAt_obj (P := P) h c β hβ t0 v
    have hlm : IsLocalMin (fun s : ℝ => wr11_obj c β P S (t0 + s • v)) 0 :=
      Eventually.of_forall fun s => by simpa using hmin (t0 + s • v)
    have h0 := hlm.hasDerivAt_eq_zero hd
    rw [wr11_integral_Ya_eq (P.tilted (wr11_Ya S t0)) h] at h0
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, real_inner_comm t0 v]
    have e : (1 / β) * inner ℝ t0 v = inner ℝ t0 v / β := by ring
    rw [e]
    exact h0
  have h0 := hstat (c • m + (1 / β) • t0)
  rw [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at h0
  have h1 : (1 / β) • t0 = -(c • m) := eq_neg_of_add_eq_zero_right h0
  calc t0 = β • ((1 / β) • t0) := by rw [smul_smul, mul_one_div_cancel hβ.ne', one_smul]
    _ = β • (-(c • m)) := by rw [h1]
    _ = -(β * c) • m := by rw [smul_neg, smul_smul, neg_smul]

/-- **Norm bound.**  A minimiser satisfies `‖t0‖ ≤ β c ‖E_P S‖`. -/
lemma wr11_norm_le [CompleteSpace H] [IsProbabilityMeasure P] (h : Wr11Bdd S C) {c : ℝ} (hc : 0 < c)
    {β : ℝ} (hβ : 0 < β) {t0 : H} (hmin : ∀ s, wr11_obj c β P S t0 ≤ wr11_obj c β P S s) :
    ‖t0‖ ≤ β * c * ‖∫ ω, S ω ∂P‖ := by
  have := wr11_isProb_tilted (P := P) h t0
  have hmono := wr11_integral_Ya_le_tilted_self (P := P) h t0
  rw [wr11_integral_Ya_eq P h, wr11_integral_Ya_eq (P.tilted (wr11_Ya S t0)) h] at hmono
  have hteq := wr11_stationary h hc hβ hmin
  set mt : H := ∫ ω, S ω ∂(P.tilted (wr11_Ya S t0)) with hmt
  have hbc : 0 < β * c := mul_pos hβ hc
  have hmt' : mt = -(1 / (β * c)) • t0 := by
    rw [hteq, smul_smul]
    have : -(1 / (β * c)) * -(β * c) = 1 := by field_simp
    rw [this, one_smul]
  rw [hmt', real_inner_smul_right, real_inner_self_eq_norm_sq] at hmono
  have h2 := abs_real_inner_le_norm t0 (∫ ω, S ω ∂P)
  have h3 : ‖t0‖ ^ 2 ≤ β * c * (‖t0‖ * ‖∫ ω, S ω ∂P‖) := by
    have hneg := neg_abs_le (inner ℝ t0 (∫ ω, S ω ∂P))
    have h4 : (1 / (β * c)) * ‖t0‖ ^ 2 ≤ ‖t0‖ * ‖∫ ω, S ω ∂P‖ := by linarith
    calc ‖t0‖ ^ 2 = β * c * ((1 / (β * c)) * ‖t0‖ ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 hbc.le
  by_cases h0 : ‖t0‖ = 0
  · rw [h0]; positivity
  · have hpos : 0 < ‖t0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

end Obj

end HRS.MS.Wr
