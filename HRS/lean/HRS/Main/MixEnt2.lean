import HRS.Main.MixEnt1

/-!
# MIXENT 2: relative entropy of the mixture preparation against `π = (μ°)^{⊗N}` (lemma M2)

TeX L6952-6962 (proof of the full bounds for the mixture, "each conditional product law has relative
entropy `O(1)` to `(μ°)^{⊗N}`"), Proposition 5.9 (TeX L6781-6800).

Route (a slight simplification of the plan, no Jensen for `log`): with `klFun x = x log x + 1 - x`
(Mathlib), `H(f π | π) = ∫ klFun(f) dπ` for probability densities `f`,
1. pointwise convexity `klFun((r₊+r₋)/2) ≤ (klFun r₊ + klFun r₋)/2`;
2. tensorisation `∫ klFun(∏ᵢ f(xᵢ)) dπ = N ∫ klFun f dμ` for mean-one densities `f`;
3. `klFun(1+u) ≤ u²` (from `log y ≤ y - 1`);
so that `H(mixturePrep | π) ≤ a₀² ∫ b² dμ`, uniformly in `N`.

Helpers carry the prefix `mx_`; they live in `HRS.Main`.
-/

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- `klFun (1 + u) ≤ u²` for `u > -1` (`(1+u) log (1+u) - u ≤ (1+u)u - u = u²`). -/
theorem mx_klFun_one_add_le {u : ℝ} (hu : -1 < u) : klFun (1 + u) ≤ u ^ 2 := by
  have hpos : 0 < 1 + u := by linarith
  have h := Real.log_le_sub_one_of_pos hpos
  unfold klFun
  nlinarith [mul_le_mul_of_nonneg_left h hpos.le]

/-- Convexity of `klFun` at the midpoint. -/
theorem mx_klFun_midpoint {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    klFun ((x + y) / 2) ≤ (klFun x + klFun y) / 2 := by
  have := convexOn_klFun.2 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hy)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at this
  have e1 : (1 / 2 : ℝ) * x + 1 / 2 * y = (x + y) / 2 := by ring
  rw [e1] at this
  linarith

/-- For a bounded density `f ∈ [1/2, 3/2]`: `|log f| ≤ 1`. -/
theorem mx_abs_log_le {y : ℝ} (hlo : 1 / 2 ≤ y) : |Real.log y| ≤ 1 ∨ 3 / 2 < y := by
  by_cases h : y ≤ 3 / 2
  · left
    have hp : 0 < y := by linarith
    rw [abs_le]
    constructor
    · have := Real.one_sub_inv_le_log_of_pos hp
      have : y⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hp (by norm_num)]; linarith
      linarith
    · have := Real.log_le_sub_one_of_pos hp
      linarith
  · right; linarith

/-- **Tensorisation of `klFun` for product densities.**  If `f ∈ [1/2, 3/2]` is a measurable
density with `∫ f dμ = 1` then `∫ klFun(∏ᵢ f(xᵢ)) dμ^{⊗N} = N ∫ klFun f dμ`, and the integrand is
integrable. -/
theorem mx_klFun_prod_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℝ) (hfm : Measurable f) (hlo : ∀ x, 1 / 2 ≤ f x)
    (hhi : ∀ x, f x ≤ 3 / 2) (hint : ∫ x, f x ∂μ = 1) (N : ℕ) :
    Integrable (fun X : Fin N → α => klFun (∏ i, f (X i))) (Measure.pi fun _ : Fin N => μ) ∧
      ∫ X : Fin N → α, klFun (∏ i, f (X i)) ∂(Measure.pi fun _ : Fin N => μ) =
        N * ∫ x, klFun (f x) ∂μ := by
  have hfpos : ∀ x, 0 < f x := fun x => by linarith [hlo x]
  have hlogb : ∀ x, |Real.log (f x)| ≤ 1 := fun x => by
    rcases mx_abs_log_le (hlo x) with h | h
    · exact h
    · exact absurd (hhi x) (not_le.2 h)
  have hLm : Measurable fun x => Real.log (f x) := hfm.log
  have hf_int : Integrable f μ := by
    refine Integrable.of_bound hfm.aestronglyMeasurable (3 / 2) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (hfpos x)]; exact hhi x
  have hfL_int : Integrable (fun x => f x * Real.log (f x)) μ := by
    refine Integrable.of_bound (hfm.mul hLm).aestronglyMeasurable (3 / 2) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hfpos x)]
    calc f x * |Real.log (f x)| ≤ (3 / 2) * 1 :=
          mul_le_mul (hhi x) (hlogb x) (abs_nonneg _) (by norm_num)
      _ = 3 / 2 := by norm_num
  set A : ℝ := ∫ x, f x * Real.log (f x) ∂μ with hA
  set π : Measure (Fin N → α) := Measure.pi fun _ : Fin N => μ with hπ
  -- the one-coordinate factors
  let G : Fin N → Fin N → α → ℝ := fun i j y => f y * (if j = i then Real.log (f y) else 1)
  have hG_int : ∀ i j, Integrable (G i j) μ := fun i j => by
    by_cases h : j = i
    · simpa [G, h] using hfL_int
    · simpa [G, h] using hf_int
  have hG_val : ∀ i j, ∫ y, G i j y ∂μ = if j = i then A else 1 := fun i j => by
    by_cases h : j = i
    · simp [G, h, hA]
    · simp [G, h, hint]
  have hprod_pt : ∀ (i : Fin N) (X : Fin N → α),
      ∏ j, G i j (X j) = (∏ j, f (X j)) * Real.log (f (X i)) := fun i X => by
    simp only [G]
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite_eq' Finset.univ i (fun j => Real.log (f (X j)))]
    simp
  have hterm_int : ∀ i : Fin N,
      Integrable (fun X : Fin N → α => (∏ j, f (X j)) * Real.log (f (X i))) π := fun i => by
    have := Integrable.fintype_prod (μ := fun _ : Fin N => μ) (f := G i) (hG_int i)
    simpa [hprod_pt] using this
  have hterm_val : ∀ i : Fin N,
      ∫ X : Fin N → α, (∏ j, f (X j)) * Real.log (f (X i)) ∂π = A := fun i => by
    have := integral_fintype_prod_eq_prod (μ := fun _ : Fin N => μ) (G i)
    simp only [hprod_pt] at this
    rw [this]
    simp_rw [hG_val]
    rw [Finset.prod_ite_eq' Finset.univ i (fun _ => A)]
    simp
  have hr_int : Integrable (fun X : Fin N → α => ∏ j, f (X j)) π :=
    Integrable.fintype_prod (μ := fun _ : Fin N => μ) (f := fun _ => f) (fun _ => hf_int)
  have hr_val : ∫ X : Fin N → α, ∏ j, f (X j) ∂π = 1 := by
    rw [integral_fintype_prod_eq_pow, hint]; simp
  have hklpt : ∀ X : Fin N → α, klFun (∏ i, f (X i)) =
      (∑ i, (∏ j, f (X j)) * Real.log (f (X i))) + 1 - ∏ j, f (X j) := fun X => by
    unfold klFun
    rw [Real.log_prod (fun j _ => (hfpos (X j)).ne'), Finset.mul_sum]
  have hsum_int : Integrable (fun X : Fin N → α =>
      ∑ i, (∏ j, f (X j)) * Real.log (f (X i))) π :=
    integrable_finsetSum _ fun i _ => hterm_int i
  have hk_int : Integrable (fun X : Fin N → α => klFun (∏ i, f (X i))) π := by
    simp_rw [hklpt]
    exact (hsum_int.add (integrable_const 1)).sub hr_int
  refine ⟨hk_int, ?_⟩
  simp_rw [hklpt]
  have h1 := integral_sub (μ := π)
    (f := fun X : Fin N → α => (∑ i, (∏ j, f (X j)) * Real.log (f (X i))) + 1)
    (g := fun X : Fin N → α => ∏ j, f (X j)) (hsum_int.add (integrable_const (1 : ℝ))) hr_int
  have h2 := integral_add (μ := π)
    (f := fun X : Fin N → α => ∑ i, (∏ j, f (X j)) * Real.log (f (X i)))
    (g := fun _ : Fin N → α => (1 : ℝ)) hsum_int (integrable_const (1 : ℝ))
  beta_reduce at h1 h2
  rw [h1, h2, integral_finsetSum _ fun i _ => hterm_int i]
  simp_rw [hterm_val]
  rw [hr_val]
  have hk1 : ∫ x, klFun (f x) ∂μ = A := by
    have : ∀ x, klFun (f x) = f x * Real.log (f x) + 1 - f x := fun x => rfl
    simp_rw [this]
    have h1 := integral_sub (μ := μ) (f := fun x => f x * Real.log (f x) + 1) (g := f)
      (hfL_int.add (integrable_const (1 : ℝ))) hf_int
    have h2 := integral_add (μ := μ) (f := fun x => f x * Real.log (f x)) (g := fun _ => (1 : ℝ))
      hfL_int (integrable_const (1 : ℝ))
    beta_reduce at h1 h2
    rw [h1, h2, hint]
    simp [hA]
  rw [hk1]
  simp

/-- The two one-coordinate densities `1 ± a₀ b/√N` have mean one when `μ(b) = 0`. -/
theorem mx_factor_mean (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (b : Torus d → ℝ)
    (hbi : Integrable b μ) (hb0 : ∫ x, b x ∂μ = 0) (a₀ : ℝ) (N : ℕ) (σ : ℝ) :
    ∫ x, (1 + σ * (a₀ * b x / Real.sqrt N)) ∂μ = 1 := by
  have h1 : Integrable (fun x => σ * (a₀ * b x / Real.sqrt N)) μ := by
    have : Integrable (fun x => (σ * a₀ / Real.sqrt N) * b x) μ := hbi.const_mul _
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only; ring
  rw [integral_add (integrable_const (1 : ℝ)) h1]
  have : ∀ x, σ * (a₀ * b x / Real.sqrt N) = (σ * a₀ / Real.sqrt N) * b x := fun x => by ring
  simp_rw [this]
  rw [integral_const_mul, hb0]
  simp

/-- A density `ofReal f` with `f ≥ 0` measurable integrable of mean one gives a probability measure. -/
theorem mx_isProb_withDensity {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f μ) (h1 : ∫ x, f x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (f x)) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0), h1]
  simp

/-- **M2, Step A**: the mixture preparation is a probability measure (for `|a₀ b| ≤ √N/2`,
`μ(b) = 0`, `b` bounded). -/
theorem mx_isProb_mixturePrep (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (b : Torus d → ℝ)
    (hb : Measurable b) (hbi : Integrable b μ) (hb0 : ∫ x, b x ∂μ = 0) (a₀ : ℝ) (N : ℕ)
    (hN : 1 ≤ N) (hB : ∀ x, |a₀ * b x| ≤ Real.sqrt N / 2) :
    IsProbabilityMeasure (mixturePrep μ b a₀ N) := by
  have hfi : ∀ σ : ℝ, Integrable (fun x => 1 + σ * (a₀ * b x / Real.sqrt N)) μ := fun σ => by
    refine (integrable_const (1 : ℝ)).add ?_
    have : Integrable (fun x => (σ * a₀ / Real.sqrt N) * b x) μ := hbi.const_mul _
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only; ring
  haveI hP : IsProbabilityMeasure
      (μ.withDensity fun x => ENNReal.ofReal (1 + a₀ * b x / Real.sqrt N)) := by
    have := mx_isProb_withDensity μ (fun x => 1 + 1 * (a₀ * b x / Real.sqrt N))
      (fun x => by have := (mx_factor_bounds hN hB x).1; simp only [one_mul]; linarith)
      (hfi 1) (mx_factor_mean μ b hbi hb0 a₀ N 1)
    simpa using this
  haveI hM : IsProbabilityMeasure
      (μ.withDensity fun x => ENNReal.ofReal (1 - a₀ * b x / Real.sqrt N)) := by
    have := mx_isProb_withDensity μ (fun x => 1 + (-1) * (a₀ * b x / Real.sqrt N))
      (fun x => by have := (mx_factor_bounds hN hB x).2.2.1; linarith [neg_one_mul (a₀ * b x / Real.sqrt N)])
      (hfi (-1)) (mx_factor_mean μ b hbi hb0 a₀ N (-1))
    simpa [sub_eq_add_neg] using this
  refine ⟨?_⟩
  unfold mixturePrep
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [one_div, ENNReal.inv_two_add_inv_two]

/-- **M2** (relative entropy of the mixture preparation against the product reference;
TeX L6952-6962, "each conditional product law has relative entropy `O(1)` to `(μ°)^{⊗N}`").
For a probability measure `μ`, a bounded measurable `b` with `μ(b) = 0`, `N ≥ 1` and
`|a₀ b| ≤ √N/2` (the condition `N ≥ 4a₀²‖b‖²_∞` of Proposition 5.9, TeX L6799-6800),
`H(mixturePrep | μ^{⊗N}) ≤ a₀² ∫ b² dμ`, uniformly in `N`.  (The constant is `1` times
`a₀² ‖b‖²_{L²(μ)}`: by convexity `H(mix | π) ≤ H(ν₊^{⊗N}|π)/2 + H(ν₋^{⊗N}|π)/2`,
`H(ν_±^{⊗N}|π) = N H(ν_±|μ) ≤ N (a₀²/N) ∫ b²`.) -/
theorem mx_relEntropy_mixturePrep_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (b : Torus d → ℝ) (hb : Measurable b) (M : ℝ) (hbM : ∀ x, |b x| ≤ M)
    (hb0 : ∫ x, b x ∂μ = 0) (a₀ : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hB : ∀ x, |a₀ * b x| ≤ Real.sqrt N / 2) :
    relEntropy (mixturePrep μ b a₀ N) (Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal (a₀ ^ 2 * ∫ x, b x ^ 2 ∂μ) := by
  have hbi : Integrable b μ :=
    Integrable.of_bound hb.aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hbM x)
  have hb2i : Integrable (fun x => b x ^ 2) μ :=
    Integrable.of_bound (hb.pow_const 2).aestronglyMeasurable (M ^ 2) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hbM x) 2)
  have hN0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  set π : Measure (Fin N → Torus d) := Measure.pi fun _ : Fin N => μ with hπ
  haveI := mx_isProb_mixturePrep μ b hb hbi hb0 a₀ N hN hB
  set mix := mixturePrep μ b a₀ N with hmix
  have hRm : Measurable (fun X : Fin N → Torus d => mxR b a₀ N X) := by
    unfold mxR mxRp mxRm
    refine Measurable.div_const (Measurable.add ?_ ?_) _
    · exact Finset.measurable_prod _ fun i _ => by
        have := hb.comp (measurable_pi_apply (X := fun _ : Fin N => Torus d) i); fun_prop
    · exact Finset.measurable_prod _ fun i _ => by
        have := hb.comp (measurable_pi_apply (X := fun _ : Fin N => Torus d) i); fun_prop
  have hmixeq : mix = π.withDensity (fun X => ENNReal.ofReal (mxR b a₀ N X)) :=
    mx_mixturePrep_eq_withDensity_real μ b hb a₀ N hN hB
  have hrn : mix.rnDeriv π =ᵐ[π] fun X => ENNReal.ofReal (mxR b a₀ N X) := by
    rw [hmixeq]
    exact Measure.rnDeriv_withDensity π (ENNReal.measurable_ofReal.comp hRm)
  have hac : mix ≪ π := by rw [hmixeq]; exact withDensity_absolutelyContinuous _ _
  unfold relEntropy
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  -- pointwise reduction to the two product densities
  have hfp_meas : Measurable fun x => 1 + a₀ * b x / Real.sqrt N := by fun_prop
  have hfm_meas : Measurable fun x => 1 - a₀ * b x / Real.sqrt N := by fun_prop
  have Tp := mx_klFun_prod_integral μ (fun x => 1 + a₀ * b x / Real.sqrt N) hfp_meas
    (fun x => (mx_factor_bounds hN hB x).1) (fun x => (mx_factor_bounds hN hB x).2.1)
    (by simpa using mx_factor_mean μ b hbi hb0 a₀ N 1) N
  have Tm := mx_klFun_prod_integral μ (fun x => 1 - a₀ * b x / Real.sqrt N) hfm_meas
    (fun x => (mx_factor_bounds hN hB x).2.2.1) (fun x => (mx_factor_bounds hN hB x).2.2.2)
    (by simpa [sub_eq_add_neg] using mx_factor_mean μ b hbi hb0 a₀ N (-1)) N
  set kp : (Fin N → Torus d) → ℝ := fun X => klFun (∏ i, (1 + a₀ * b (X i) / Real.sqrt N)) with hkp
  set km : (Fin N → Torus d) → ℝ := fun X => klFun (∏ i, (1 - a₀ * b (X i) / Real.sqrt N)) with hkm
  have hkp0 : ∀ X, 0 ≤ kp X := fun X => klFun_nonneg (Finset.prod_nonneg fun i _ => by
    linarith [(mx_factor_bounds hN hB (X i)).1])
  have hkm0 : ∀ X, 0 ≤ km X := fun X => klFun_nonneg (Finset.prod_nonneg fun i _ => by
    linarith [(mx_factor_bounds hN hB (X i)).2.2.1])
  have step1 : ∫⁻ X, ENNReal.ofReal (klFun ((mix.rnDeriv π X).toReal)) ∂π ≤
      ∫⁻ X, ENNReal.ofReal ((kp X + km X) / 2) ∂π := by
    refine lintegral_mono_ae ?_
    filter_upwards [hrn] with X hX
    rw [hX, ENNReal.toReal_ofReal (mx_R_pos hN hB X).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mx_klFun_midpoint (x := mxRp b a₀ N X) (y := mxRm b a₀ N X)
      (mx_Rp_pos hN hB X).le (mx_Rm_pos hN hB X).le
    simpa [mxR, hkp, hkm, mxRp, mxRm] using this
  refine step1.trans ?_
  have hint : Integrable (fun X => (kp X + km X) / 2) π :=
    ((Tp.1.add Tm.1).div_const 2)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun X => by have := hkp0 X; have := hkm0 X; positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_div, integral_add Tp.1 Tm.1, Tp.2, Tm.2]
  -- the one-coordinate entropy bounds
  have hc : (N : ℝ) * (a₀ / Real.sqrt N) ^ 2 = a₀ ^ 2 := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; field_simp
  have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      ∫ x, klFun (1 + σ * (a₀ * b x / Real.sqrt N)) ∂μ ≤ (a₀ / Real.sqrt N) ^ 2 * ∫ x, b x ^ 2 ∂μ := by
    intro σ hσ
    have hσ2 : σ ^ 2 = 1 := by rcases hσ with h | h <;> simp [h]
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hb2i.const_mul _) (ae_of_all _ fun x => ?_)
    · refine ae_of_all _ fun x => klFun_nonneg ?_
      rcases hσ with h | h
      · have := (mx_factor_bounds hN hB x).1; subst h; linarith
      · have := (mx_factor_bounds hN hB x).2.2.1; subst h; linarith
    · have hu : -1 < σ * (a₀ * b x / Real.sqrt N) := by
        rcases hσ with h | h
        · have := (mx_factor_bounds hN hB x).1; subst h; linarith
        · have := (mx_factor_bounds hN hB x).2.2.1; subst h; linarith
      refine (mx_klFun_one_add_le hu).trans (le_of_eq ?_)
      calc (σ * (a₀ * b x / Real.sqrt N)) ^ 2 = σ ^ 2 * ((a₀ / Real.sqrt N) ^ 2 * b x ^ 2) := by
            ring
        _ = _ := by rw [hσ2]; ring
  have kp' := key 1 (Or.inl rfl)
  have km' := key (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at kp' km'
  have e : (↑N * ∫ x, klFun (1 + a₀ * b x / Real.sqrt N) ∂μ +
      ↑N * ∫ x, klFun (1 - a₀ * b x / Real.sqrt N) ∂μ) / 2 ≤ a₀ ^ 2 * ∫ x, b x ^ 2 ∂μ := by
    have hN' : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have h1 := mul_le_mul_of_nonneg_left kp' hN'
    have h2 := mul_le_mul_of_nonneg_left km' hN'
    rw [← mul_assoc, hc] at h1 h2
    linarith
  exact e

end Main

end HRS
