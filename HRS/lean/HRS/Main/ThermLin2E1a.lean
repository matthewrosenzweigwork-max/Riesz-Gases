import HRS.Main.ThermLin2Ba1

/-!
# THERMLIN2 E1a: measure-theoretic helpers for `tl2_zero_start_comparison`

Weighted Cauchy-Schwarz and Fubini bound for a time integral of a jointly measurable process, an elementary bound for
the exponential weight, congruence lemmas for `IsStochConv`.  No plan statement is used.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P

variable {d : ℕ}

/-- Cauchy-Schwarz in `ℝ≥0∞`: `(∫ N)² ≤ μ(univ) ∫ N²`. -/
lemma tl2E1_cs {α : Type*} [MeasurableSpace α] (μ : Measure α) {N : α → ℝ≥0∞} (hN : AEMeasurable N μ) :
    (∫⁻ x, N x ∂μ) ^ 2 ≤ μ Set.univ * ∫⁻ x, N x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2) Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ≥0∞)) (g := N) aemeasurable_const hN
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have h2 : (∫⁻ x, N x ∂μ) ^ 2 ≤ ((μ Set.univ) ^ (1 / (2 : ℝ)) * (∫⁻ a, N a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) ^ 2 :=
    pow_le_pow_left' h 2
  refine h2.trans (le_of_eq ?_)
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  simp only [Nat.cast_ofNat, one_div]
  rw [show (2 : ℝ)⁻¹ * 2 = 1 by norm_num, ENNReal.rpow_one, ENNReal.rpow_one]
  congr 2
  funext x
  rw [← ENNReal.rpow_natCast]; norm_num

/-- Weighted Cauchy-Schwarz + Fubini: `E (∫_s g N_r dr)² ≤ (∫_s g)² M` if `E N_r² ≤ M` for `r ∈ s`. -/
lemma tl2E1_wcs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {s : Set ℝ}
    (hs : MeasurableSet s) {g : ℝ → ℝ≥0∞} (hg : Measurable g) {N : ℝ → Ω → ℝ≥0∞}
    (hN : Measurable (Function.uncurry N)) {M : ℝ≥0∞} (hM : ∀ r ∈ s, ∫⁻ ω, N r ω ^ 2 ∂P ≤ M) :
    ∫⁻ ω, (∫⁻ r in s, g r * N r ω) ^ 2 ∂P ≤ (∫⁻ r in s, g r) ^ 2 * M := by
  set μ : Measure ℝ := (volume.restrict s).withDensity g with hμ
  have hNω : ∀ ω, Measurable fun r => N r ω := fun ω => hN.comp (measurable_id.prodMk measurable_const)
  have hpt : ∀ ω, (∫⁻ r in s, g r * N r ω) ^ 2 ≤ (∫⁻ r in s, g r) * ∫⁻ r in s, g r * N r ω ^ 2 := by
    intro ω
    have h1 : ∫⁻ r in s, g r * N r ω = ∫⁻ r, N r ω ∂μ := by
      rw [hμ, lintegral_withDensity_eq_lintegral_mul _ hg (hNω ω)]; rfl
    have h2 : ∫⁻ r in s, g r * N r ω ^ 2 = ∫⁻ r, N r ω ^ 2 ∂μ := by
      rw [hμ, lintegral_withDensity_eq_lintegral_mul _ hg ((hNω ω).pow_const 2)]; rfl
    have h3 : μ Set.univ = ∫⁻ r in s, g r := by
      rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [h1, h2, ← h3]
    exact tl2E1_cs μ (hNω ω).aemeasurable
  have hm2 : Measurable fun q : Ω × ℝ => g q.2 * N q.2 q.1 ^ 2 :=
    (hg.comp measurable_snd).mul (((hN.comp (measurable_snd.prodMk measurable_fst))).pow_const 2)
  have hm3 : Measurable fun ω => ∫⁻ r in s, g r * N r ω ^ 2 :=
    hm2.lintegral_prod_right' (ν := volume.restrict s)
  calc ∫⁻ ω, (∫⁻ r in s, g r * N r ω) ^ 2 ∂P
      ≤ ∫⁻ ω, ((∫⁻ r in s, g r) * ∫⁻ r in s, g r * N r ω ^ 2) ∂P := lintegral_mono hpt
    _ = (∫⁻ r in s, g r) * ∫⁻ ω, (∫⁻ r in s, g r * N r ω ^ 2) ∂P := by
        rw [lintegral_const_mul'' _ hm3.aemeasurable]
    _ = (∫⁻ r in s, g r) * ∫⁻ r in s, g r * ∫⁻ ω, N r ω ^ 2 ∂P := by
        congr 1
        rw [lintegral_lintegral_swap hm2.aemeasurable]
        congr 1; funext r
        rw [lintegral_const_mul]
        exact (hN.comp (measurable_const.prodMk measurable_id)).pow_const 2
    _ ≤ (∫⁻ r in s, g r) * ∫⁻ r in s, g r * M := by
        exact mul_le_mul' le_rfl (setLIntegral_mono' hs fun r hr => mul_le_mul' le_rfl (hM r hr))
    _ = (∫⁻ r in s, g r) ^ 2 * M := by
        rw [lintegral_mul_const'' _ hg.aemeasurable, pow_two, mul_assoc]

/-- `∫ B ≤ (∫ B²)^{1/2}` on a probability space. -/
lemma tl2E1_l1_le_l2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {B : Ω → ℝ≥0∞}
    (hB : AEMeasurable B P) : ∫⁻ ω, B ω ∂P ≤ (∫⁻ ω, B ω ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  have h := tl2E1_cs P hB
  rw [measure_univ, one_mul] at h
  have h2 := ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h2
  simpa using h2

/-- `IsStochConv` only depends on the evolution on `{(t, s) : 0 ≤ s ≤ t}`. -/
lemma tl2E1_sc_evo_congr {m : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (V₁ V₂ : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (j : NegSobolev d m →L[ℝ] NegSobolev d m)
    {M : ℝ → Ω → NegSobolev d m} {t : ℝ} (ht : 0 ≤ t) (hV : ∀ s : ℝ, 0 ≤ s → s ≤ t → V₁ t s = V₂ t s)
    {Z : Ω → NegSobolev d m} (h : IsStochConv P V₁ j M 0 t Z) : IsStochConv P V₂ j M 0 t Z := by
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := h ε hε
  refine ⟨δ, hδ, fun n r h0 hn hmono hmesh => ?_⟩
  have hmem : ∀ i, r i ∈ Set.Icc (0 : ℝ) t := fun i => by
    refine ⟨h0 ▸ hmono (Fin.zero_le i), hn ▸ hmono (Fin.le_last i)⟩
  have e : ∀ ω, riemannSum V₂ j M t r ω = riemannSum V₁ j M t r ω := by
    intro ω
    unfold riemannSum
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hV _ (hmem _).1 (hmem _).2]
  simp_rw [e]
  exact hh n r h0 hn hmono hmesh

/-- `IsStochConv` is invariant under a.e. modification of the limit. -/
lemma tl2E1_sc_ae_congr {m : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (j : NegSobolev d m →L[ℝ] NegSobolev d m)
    {M : ℝ → Ω → NegSobolev d m} {a t : ℝ} {Z Z' : Ω → NegSobolev d m} (hZ : Z' =ᵐ[P] Z)
    (h : IsStochConv P V j M a t Z) : IsStochConv P V j M a t Z' := by
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := h ε hε
  refine ⟨δ, hδ, fun n r h0 hn hmono hmesh => ?_⟩
  refine lt_of_le_of_lt (le_of_eq ?_) (hh n r h0 hn hmono hmesh)
  refine lintegral_congr_ae ?_
  filter_upwards [hZ] with ω hω
  rw [hω]

/-- The shifted Sobolev norm is a measurable function. -/
lemma tl2E1_normShift_measurable (m b : ℝ) : Measurable (tl2NormShift (d := d) m b) := by
  unfold tl2NormShift
  refine Measurable.pow_const (Measurable.tsum fun k => ?_) _
  exact ((((HRS.Uniform.Q54c.continuous_coord m k |>.measurable).pow_const 2).const_mul _)).ennreal_ofReal

/-- The integral of the exponential weight of the remainder bound decays exponentially in `a`. -/
lemma tl2E1_phi {c κ T : ℝ} (hc : 0 < c) (hκ : 0 < κ) (hT : 0 < T) :
    ∃ Cφ cφ : ℝ, 0 ≤ Cφ ∧ 0 < cφ ∧ ∀ a : ℝ, 0 ≤ a →
      ∫⁻ r in Set.Icc (0 : ℝ) (a + T),
        ENNReal.ofReal (Real.exp (-c * max (a - r) 0) * Real.exp (-κ * r)) ≤
        ENNReal.ofReal (Cφ * Real.exp (-cφ * a)) := by
  set γ : ℝ := min c κ / 2 with hγ
  have hγ0 : 0 < γ := half_pos (lt_min hc hκ)
  have hmin1 : min c κ ≤ c := min_le_left _ _
  have hmin2 : min c κ ≤ κ := min_le_right _ _
  refine ⟨1 / γ + T, γ, by positivity, hγ0, fun a ha => ?_⟩
  set u : ℝ → ℝ := fun r => Real.exp (-γ * a) * Real.exp (-γ * max (a - r) 0) with hu
  have hpt : ∀ r ∈ Set.Icc (0 : ℝ) (a + T),
      Real.exp (-c * max (a - r) 0) * Real.exp (-κ * r) ≤ u r := by
    intro r hr
    simp only [hu]
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have hr0 := hr.1
    rcases le_total r a with h | h
    · rw [max_eq_left (by linarith)]
      nlinarith [mul_nonneg (sub_nonneg.2 hmin1) (sub_nonneg.2 h), mul_nonneg (sub_nonneg.2 hmin2) hr0,
        lt_min hc hκ |>.le, mul_nonneg (lt_min hc hκ).le hr0]
    · rw [max_eq_right (by linarith)]
      nlinarith [mul_nonneg (sub_nonneg.2 hmin2) ha, mul_nonneg hκ.le (sub_nonneg.2 h),
        mul_nonneg (lt_min hc hκ).le ha]
  have hucont : Continuous u := by
    simp only [hu]
    fun_prop
  have hunn : ∀ r, 0 ≤ u r := fun r => by simp only [hu]; positivity
  have hsub : Set.Icc (0 : ℝ) (a + T) ⊆ Set.Icc 0 a ∪ Set.Icc a (a + T) := by
    intro r hr
    rcases le_total r a with h | h
    · exact Or.inl ⟨hr.1, h⟩
    · exact Or.inr ⟨h, hr.2⟩
  calc ∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (Real.exp (-c * max (a - r) 0) * Real.exp (-κ * r))
      ≤ ∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (u r) :=
        setLIntegral_mono' measurableSet_Icc fun r hr => ENNReal.ofReal_le_ofReal (hpt r hr)
    _ ≤ ∫⁻ r in Set.Icc (0 : ℝ) a ∪ Set.Icc a (a + T), ENNReal.ofReal (u r) := lintegral_mono_set hsub
    _ ≤ (∫⁻ r in Set.Icc (0 : ℝ) a, ENNReal.ofReal (u r)) + ∫⁻ r in Set.Icc a (a + T), ENNReal.ofReal (u r) :=
        lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (Real.exp (-γ * a) / γ) + ENNReal.ofReal (Real.exp (-γ * a) * T) := by
        gcongr
        · -- first piece: explicit integral
          have h1 : ∫⁻ r in Set.Icc (0 : ℝ) a, ENNReal.ofReal (u r) =
              ∫⁻ r in Set.Icc (0 : ℝ) a, ENNReal.ofReal (Real.exp (-γ * a) * Real.exp (-γ * (a - r))) := by
            refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
            simp only [hu]
            rw [max_eq_left (by linarith [hr.2])]
          rw [h1, ← ofReal_integral_eq_lintegral_ofReal]
          · refine ENNReal.ofReal_le_ofReal ?_
            rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha,
              intervalIntegral.integral_const_mul]
            have hder : ∀ r ∈ Set.uIcc (0 : ℝ) a,
                HasDerivAt (fun r => Real.exp (-γ * (a - r)) / γ) (Real.exp (-γ * (a - r))) r := by
              intro r _
              have h1 : HasDerivAt (fun r => -γ * (a - r)) γ r := by
                have := ((hasDerivAt_id r).const_sub a).const_mul (-γ)
                simpa using this
              have := (h1.exp).div_const γ
              convert this using 1
              field_simp
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
              ((by fun_prop : Continuous fun r : ℝ => Real.exp (-γ * (a - r))).intervalIntegrable _ _)]
            simp only [sub_zero, sub_self, mul_zero, Real.exp_zero]
            have : 0 ≤ Real.exp (-γ * a) := (Real.exp_pos _).le
            have h2 : 0 ≤ Real.exp (-γ * a) / γ := by positivity
            have h3 : Real.exp (-γ * a) * (1 / γ - Real.exp (-γ * a) / γ) ≤ Real.exp (-γ * a) / γ := by
              have : 0 ≤ Real.exp (-γ * a) * (Real.exp (-γ * a) / γ) := by positivity
              nlinarith [this, show Real.exp (-γ * a) * (1 / γ) = Real.exp (-γ * a) / γ by ring]
            convert h3 using 2 <;> ring
          · exact (by fun_prop : Continuous fun r : ℝ => Real.exp (-γ * a) * Real.exp (-γ * (a - r))).integrableOn_Icc
          · exact Filter.Eventually.of_forall fun r => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
        · -- second piece
          calc ∫⁻ r in Set.Icc a (a + T), ENNReal.ofReal (u r)
              ≤ ∫⁻ r in Set.Icc a (a + T), ENNReal.ofReal (Real.exp (-γ * a)) := by
                refine setLIntegral_mono' measurableSet_Icc fun r hr => ENNReal.ofReal_le_ofReal ?_
                simp only [hu]
                rw [max_eq_right (by linarith [hr.1])]
                simp
            _ = ENNReal.ofReal (Real.exp (-γ * a) * T) := by
                rw [setLIntegral_const, Real.volume_Icc, ENNReal.ofReal_mul (Real.exp_pos _).le]
                congr 1
                rw [show a + T - a = T by ring]
    _ = ENNReal.ofReal ((1 / γ + T) * Real.exp (-γ * a)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end HRS.ThermLin.Plan2
