import HRS.MS.R2ChaosAux18

/-!
# HRS.MS.R2ChaosAux19 -- convergence of the second moments of the empirical fluctuations at a fixed time

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

theorem s94_lintegral_pow4_le {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f ν) {D : ℝ} (hD : 0 ≤ D)
    (h : eLpNorm f (ENNReal.ofReal 4) ν ≤ ENNReal.ofReal D) :
    ∫⁻ x, ENNReal.ofReal (f x ^ 4) ∂ν ≤ ENNReal.ofReal (D ^ 4) := by
  have h4 : ENNReal.ofReal 4 = 4 := by norm_num
  rw [h4] at h
  have e1 : ∫⁻ x, ENNReal.ofReal (f x ^ 4) ∂ν = ∫⁻ x, ‖f x‖ₑ ^ 4 ∂ν := by
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs]
    congr 1
    exact (Even.pow_abs ⟨2, by norm_num⟩ _).symm
  have e2 : ∫⁻ x, ‖f x‖ₑ ^ 4 ∂ν = eLpNorm f 4 ν ^ 4 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) hf]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [e1, e2, ENNReal.ofReal_pow hD]
  gcongr

section Expect

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

/-- The pair `(ξ_N^t(a), ξ_N^t(b))` converges in law to `(ξ^t(a), ξ^t(b))`. -/
theorem s94_pair_tid (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ)
    [IsProbabilityMeasure (Whole.withDensityReal ρ)] {a a' : Euc d → ℝ} (ha : IsR2Test a) (ha' : IsR2Test a')
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    TendstoInDistribution
      (fun N ζ => (r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t, r2EmpFluct (Whole.withDensityReal ρ) a' (X N) ζ t))
      atTop (fun ζ => (r2PathEval T (ξ a ζ) t, r2PathEval T (ξ a' ζ) t)) P P' := by
  have hc := hset.conv 2 ![a, a'] (fun i => by fin_cases i <;> simpa using ‹_›)
  have hcont : Continuous fun w : Fin 2 → C(Set.Icc (0 : ℝ) T, ℝ) => (w 0 ⟨t, ht⟩, w 1 ⟨t, ht⟩) :=
    ((continuous_eval_const _).comp (continuous_apply 0)).prodMk
      ((continuous_eval_const _).comp (continuous_apply 1))
  have h2 := hc.continuous_comp (g := fun w : Fin 2 → C(Set.Icc (0 : ℝ) T, ℝ) => (w 0 ⟨t, ht⟩, w 1 ⟨t, ht⟩)) hcont
  refine h2.congr (fun N => ?_) (ae_of_all _ fun ζ => ?_)
  · filter_upwards [hset.contX N] with ζ hζ
    simp only [Function.comp]
    have c1 := s94_empFluct_continuous (Whole.withDensityReal ρ) (X N) ha ζ hζ
    have c2 := s94_empFluct_continuous (Whole.withDensityReal ρ) (X N) ha' ζ hζ
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [s94_r2ContPath_eq (c1.comp continuous_subtype_val), s94_r2ContPath_eq (c2.comp continuous_subtype_val)]
    rfl
  · simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one, s94_pathEval_eq ht]

theorem s94_empFluct_section_measurable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {N : ℕ} {a : Euc d → ℝ} (ha : IsR2Test a)
    {Ω0 : Type*} [MeasurableSpace Ω0] (X0 : ℝ≥0 → Ω0 → EucConfig d N)
    (hX : Measurable fun q : ℝ≥0 × Ω0 => X0 q.1 q.2) (t : ℝ) :
    Measurable fun ζ => r2EmpFluct μ a X0 ζ t := by
  have h1 := s94_empFluct_measurable (μ := μ) (N := N) ha X0 hX
  have h2 : Measurable fun ζ : Ω0 => (t, ζ) := measurable_prodMk_left
  exact Measurable.comp (g := fun q : ℝ × Ω0 => r2EmpFluct μ a X0 q.2 q.1) (f := fun ζ : Ω0 => (t, ζ)) h1 h2

/-- Convergence of the second moments of the empirical fluctuations at a fixed time. -/
theorem s94_expect_tendsto (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {a a' : Euc d → ℝ}
    (ha : IsR2Test a) (ha' : IsR2Test a') {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Tendsto (fun N => ∫ ζ, r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t *
        r2EmpFluct (Whole.withDensityReal ρ) a' (X N) ζ t ∂(P N)) atTop
      (𝓝 (∫ ζ, r2PathEval T (ξ a ζ) t * r2PathEval T (ξ a' ζ) t ∂P')) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  have htid := s94_pair_tid hset ha ha' ht
  obtain ⟨C, hC⟩ := s94_linear_moment hd hs0 hs hb hp hρ hset (r := 4) (by norm_num)
  obtain ⟨Aa, hAa⟩ := s94_test_bounded ha
  obtain ⟨Aa', hAa'⟩ := s94_test_bounded ha'
  have hmx : ∀ N, Measurable fun ζ => r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t := fun N =>
    s94_empFluct_section_measurable ha (X N) (hset.measX N) t
  have hmy : ∀ N, Measurable fun ζ => r2EmpFluct (Whole.withDensityReal ρ) a' (X N) ζ t := fun N =>
    s94_empFluct_section_measurable ha' (X N) (hset.measX N) t
  have hCA : ∀ N : ℕ, 2 ≤ N → ∫⁻ ζ, ENNReal.ofReal (r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t ^ 4) ∂(P N) ≤
      ENNReal.ofReal ((|C * Aa|) ^ 4) := fun N hN => by
    have := hC N hN t ht a Aa (s94_test_continuous ha).measurable hAa
    exact s94_lintegral_pow4_le (hmx N).aestronglyMeasurable (abs_nonneg _)
      (this.trans (ENNReal.ofReal_le_ofReal (le_abs_self _)))
  have hCB : ∀ N : ℕ, 2 ≤ N → ∫⁻ ζ, ENNReal.ofReal (r2EmpFluct (Whole.withDensityReal ρ) a' (X N) ζ t ^ 4) ∂(P N) ≤
      ENNReal.ofReal ((|C * Aa'|) ^ 4) := fun N hN => by
    have := hC N hN t ht a' Aa' (s94_test_continuous ha').measurable hAa'
    exact s94_lintegral_pow4_le (hmy N).aestronglyMeasurable (abs_nonneg _)
      (this.trans (ENNReal.ofReal_le_ofReal (le_abs_self _)))
  set M0 : ℝ := 8 * ((|C * Aa|) ^ 4 + (|C * Aa'|) ^ 4) with hM0
  have hM00 : 0 ≤ M0 := by positivity
  have key : ∀ (σ : ℝ), σ = 1 ∨ σ = -1 →
      Integrable (fun ζ => (r2PathEval T (ξ a ζ) t + σ * r2PathEval T (ξ a' ζ) t) ^ 2) P' ∧
      Tendsto (fun N => ∫ ζ, (r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t +
          σ * r2EmpFluct (Whole.withDensityReal ρ) a' (X N) ζ t) ^ 2 ∂(P N)) atTop
        (𝓝 (∫ ζ, (r2PathEval T (ξ a ζ) t + σ * r2PathEval T (ξ a' ζ) t) ^ 2 ∂P')) := by
    intro σ hσ
    have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hres := s94_tid_integral_tendsto (g := fun q : ℝ × ℝ => (q.1 + σ * q.2) ^ 2) htid (by fun_prop)
      (fun q => sq_nonneg _) (q := 2) (by norm_num) (M := M0) hM00 (by
        filter_upwards [eventually_ge_atTop 2] with N hN
        have hpt : ∀ ζ, ENNReal.ofReal ((((r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t +
            σ * r2EmpFluct (Whole.withDensityReal ρ) a' (X N) ζ t) ^ 2) ^ (2 : ℝ))) ≤
            8 * ENNReal.ofReal (r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t ^ 4) +
              8 * ENNReal.ofReal (r2EmpFluct (Whole.withDensityReal ρ) a' (X N) ζ t ^ 4) := fun ζ => by
          set x := r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t
          set y := r2EmpFluct (Whole.withDensityReal ρ) a' (X N) ζ t
          have e : ((x + σ * y) ^ 2) ^ (2 : ℝ) = (x + σ * y) ^ 4 := by
            rw [Real.rpow_two]; ring
          rw [e]
          have h1 : (x + σ * y) ^ 4 ≤ 8 * x ^ 4 + 8 * y ^ 4 := by
            have h2 : (x + σ * y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
              nlinarith [sq_nonneg (x - σ * y), hσ2, sq_nonneg y]
            have h3 : 0 ≤ (x + σ * y) ^ 2 := sq_nonneg _
            nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg x, sq_nonneg y]
          calc ENNReal.ofReal ((x + σ * y) ^ 4) ≤ ENNReal.ofReal (8 * x ^ 4 + 8 * y ^ 4) :=
                ENNReal.ofReal_le_ofReal h1
            _ = _ := by
                rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
                  ENNReal.ofReal_mul (by norm_num)]
                simp
        calc ∫⁻ ζ, ENNReal.ofReal ((((r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t +
            σ * r2EmpFluct (Whole.withDensityReal ρ) a' (X N) ζ t) ^ 2) ^ (2 : ℝ))) ∂(P N)
            ≤ ∫⁻ ζ, (8 * ENNReal.ofReal (r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t ^ 4) +
              8 * ENNReal.ofReal (r2EmpFluct (Whole.withDensityReal ρ) a' (X N) ζ t ^ 4)) ∂(P N) :=
              lintegral_mono hpt
          _ = 8 * ∫⁻ ζ, ENNReal.ofReal (r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t ^ 4) ∂(P N) +
              8 * ∫⁻ ζ, ENNReal.ofReal (r2EmpFluct (Whole.withDensityReal ρ) a' (X N) ζ t ^ 4) ∂(P N) := by
              have hmf : Measurable (fun ζ => 8 * ENNReal.ofReal
                  (r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t ^ 4)) :=
                (ENNReal.measurable_ofReal.comp ((hmx N).pow_const 4)).const_mul 8
              rw [lintegral_add_left hmf, lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _ (by simp)]
          _ ≤ 8 * ENNReal.ofReal ((|C * Aa|) ^ 4) + 8 * ENNReal.ofReal ((|C * Aa'|) ^ 4) := by
              gcongr
              · exact hCA N hN
              · exact hCB N hN
          _ = ENNReal.ofReal M0 := by
              rw [hM0, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by positivity),
                mul_add]
              simp)
    exact ⟨hres.1, hres.2.1⟩
  obtain ⟨i1, t1⟩ := key 1 (Or.inl rfl)
  obtain ⟨i2, t2⟩ := key (-1) (Or.inr rfl)
  have hid : ∀ x y : ℝ, x * y = (1 / 4) * ((x + 1 * y) ^ 2 - (x + (-1) * y) ^ 2) := fun x y => by ring
  have hlim : ∫ ζ, r2PathEval T (ξ a ζ) t * r2PathEval T (ξ a' ζ) t ∂P' =
      (1 / 4) * (∫ ζ, (r2PathEval T (ξ a ζ) t + 1 * r2PathEval T (ξ a' ζ) t) ^ 2 ∂P' -
        ∫ ζ, (r2PathEval T (ξ a ζ) t + (-1) * r2PathEval T (ξ a' ζ) t) ^ 2 ∂P') := by
    simp_rw [hid (r2PathEval T (ξ a _) t) (r2PathEval T (ξ a' _) t)]
    rw [integral_const_mul, integral_sub i1 i2]
  rw [hlim]
  refine ((t1.sub t2).const_mul (1 / 4)).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN0 : 0 < N := by omega
  obtain ⟨Ca, hCa⟩ := s94_test_bounded ha
  obtain ⟨Ca', hCa'⟩ := s94_test_bounded ha'
  have hbd : ∀ σ : ℝ, Integrable (fun ζ => (r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t +
      σ * r2EmpFluct (Whole.withDensityReal ρ) a' (X N) ζ t) ^ 2) (P N) := fun σ => by
    refine Integrable.of_bound (((hmx N).add ((hmy N).const_mul σ)).pow_const 2).aestronglyMeasurable
      ((Real.sqrt N * (2 * Ca) + |σ| * (Real.sqrt N * (2 * Ca'))) ^ 2) (ae_of_all _ fun ζ => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    gcongr
    · exact s94_abs_empFluct_le hN0 (X N) hCa ζ t
    · exact s94_abs_empFluct_le hN0 (X N) hCa' ζ t
  have hid2 : ∫ ζ, r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t * r2EmpFluct (Whole.withDensityReal ρ) a' (X N) ζ t ∂(P N) =
      (1 / 4) * (∫ ζ, (r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t + 1 * r2EmpFluct (Whole.withDensityReal ρ) a' (X N) ζ t) ^ 2 ∂(P N) -
        ∫ ζ, (r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t + (-1) * r2EmpFluct (Whole.withDensityReal ρ) a' (X N) ζ t) ^ 2 ∂(P N)) := by
    simp_rw [hid (r2EmpFluct (Whole.withDensityReal ρ) a (X N) _ t) (r2EmpFluct (Whole.withDensityReal ρ) a' (X N) _ t)]
    rw [integral_const_mul, integral_sub (hbd 1) (hbd (-1))]
  exact hid2.symm

end Expect

end HRS.MS.R2Chaos
