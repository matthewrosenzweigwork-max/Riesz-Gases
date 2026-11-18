import HRS.MS.S82RN14
import HRS.MS.WrRefMargAux2

/-!
# S8.2 R02 (S82R), N15: the cavity correction for a `ShortRangePole` kernel
Port of `wr13e_cavD` (kernel `q_tau`) to an arbitrary `ShortRangePole` at the critical exponent: the level-set
row bounds `s82r_rows` replace the explicit `q_tau` envelope.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.External HRS.MS.Wr

variable {d : ℕ}

lemma s82r_delta_ge2 {N : ℕ} (hN : 1 ≤ N) : 1 / (N : ℝ) ≤ HRS.MS.Phase2S82.deltaN N := by
  unfold HRS.MS.Phase2S82.deltaN HRS.MS.Phase2S82.logN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine div_le_div_of_nonneg_right ?_ hN0.le
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h3 : Real.log (Real.exp 1 * N) = 1 + Real.log N := by
    rw [Real.log_mul (Real.exp_pos _).ne' hN0.ne', Real.log_exp]
  rw [h3]
  have := Real.log_nonneg h1
  linarith

/-- **Cavity correction**: `0 ≤ D(x) := log u(x) + λ n ∫ q(y,x) dν_n(y) ≤ C δ_N` for `n ≤ N`, `λ = β / N`. -/
theorem s82r_cavD (hd : 2 ≤ d) {q : Euc d → ℝ} (hq : ShortRangePole d q) (M : ℝ) {β : ℝ}
    (hβ : 0 < β) {Cν γ0 : ℝ} (hCν : 1 ≤ Cν) (hγ0 : 0 ≤ γ0) :
    ∃ CD : ℝ, 0 ≤ CD ∧ ∀ ρμ : Euc d → ℝ, HRS.Whole.IsProbDensity ρμ → (∀ x, ρμ x ≤ M) →
      ∀ V : WeakPotential (HRS.Whole.withDensityReal ρμ), (∀ x y, V.q x y = q (x - y)) →
      V.γ ≤ γ0 → Real.exp (V.M + V.M' + β * V.γ) ≤ Cν → weakKappa V β ≤ 1 / 2 →
      ∀ (N n : ℕ) [NeZero n], n ≤ N → ∀ x : Euc d,
        0 ≤ Real.log (RefMarg.cavU V (β / N) n (fun e : Empty => e.elim) x) +
          β / N * n * ∫ y, V.q y x ∂(RefMarg.cavMarg V (β / N) n) ∧
        Real.log (RefMarg.cavU V (β / N) n (fun e : Empty => e.elim) x) +
          β / N * n * ∫ y, V.q y x ∂(RefMarg.cavMarg V (β / N) n) ≤ CD * HRS.MS.Phase2S82.deltaN N := by
  obtain ⟨Ca, Cb, hCa, hCb, hrow⟩ := s82r_rows hd hq (max M 0)
  set P : ℝ := max β 1 with hP
  have hP1 : 1 ≤ P := le_max_right _ _
  have hP0 : 0 < P := by linarith
  have hCν0 : 0 ≤ Cν := by linarith
  set mb : ℝ := β * (Cν * γ0) with hmb
  refine ⟨Real.exp mb * Cν * Cb * P ^ 2 + Cν * Ca * P ^ 2, by positivity, ?_⟩
  intro ρμ hρ hM V hVq hVγ hVC hκ N n _ hn x
  haveI hprob := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hM' : ∀ y, ρμ y ≤ max M 0 := fun y => (hM y).trans (le_max_left _ _)
  have hN0 : 0 < N := lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne n)) hn
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
  set lam : ℝ := β / N with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hlamP : lam ≤ P / N := div_le_div_of_nonneg_right (le_max_left _ _) hNpos.le
  have hVqx : ∀ y, V.q y x = q (x - y) := fun y => by
    rw [hVq, ← hq.even (x - y), neg_sub]
  set ν := RefMarg.cavMarg V lam n with hν
  have hνle : ν ≤ ENNReal.ofReal Cν • (HRS.Whole.withDensityReal ρμ) := by
    have h1 := RefMarg.marginal_le_smul (B := Empty) V hβ.le hN0 (n := n) (by simpa using hn)
      (fun e : Empty => e.elim) 0
    refine h1.trans ?_
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
  have hqx : Measurable fun y : Euc d => q (x - y) :=
    hq.measurable.comp (measurable_const.sub measurable_id)
  have hq0 : ∀ y : Euc d, 0 ≤ q (x - y) := fun y => hq.nonneg _
  have hVm : Measurable fun y : Euc d => V.q y x := by
    simp_rw [hVqx]; exact hqx
  have hV0 : ∀ y, 0 ≤ V.q y x := fun y => V.q_nonneg _ _
  have hVi : Integrable (fun y => V.q y x) (HRS.Whole.withDensityReal ρμ) :=
    (V.integrable_q x).congr (Filter.Eventually.of_forall fun y => V.q_symm x y)
  have hI1 : ∫ y, V.q y x ∂ν ≤ Cν * γ0 := by
    calc ∫ y, V.q y x ∂ν ≤ Cν * ∫ y, V.q y x ∂(HRS.Whole.withDensityReal ρμ) :=
          wr13e_integral_le_of_le_smul hνle hCν0 hV0 hVi
      _ ≤ Cν * γ0 := by
          refine mul_le_mul_of_nonneg_left ?_ hCν0
          calc ∫ y, V.q y x ∂(HRS.Whole.withDensityReal ρμ) = ∫ y, V.q x y ∂(HRS.Whole.withDensityReal ρμ) :=
                integral_congr_ae (Filter.Eventually.of_forall fun y => V.q_symm y x)
            _ ≤ V.γ := V.row_le x
            _ ≤ γ0 := hVγ
  have hI0 : 0 ≤ ∫ y, V.q y x ∂ν := integral_nonneg hV0
  have hlamn : lam * n ≤ β := by
    calc lam * n ≤ lam * N := by gcongr
      _ = β := by rw [hlam]; field_simp
  have hm : lam * n * ∫ y, V.q y x ∂ν ≤ mb :=
    calc lam * n * ∫ y, V.q y x ∂ν ≤ β * (Cν * γ0) :=
          mul_le_mul hlamn hI1 hI0 hβ.le
      _ = mb := rfl
  obtain ⟨h1, h2⟩ := RefMarg.cavD_bounds V hβ.le hN0 hn hκ x hm
  refine ⟨h1, h2.trans ?_⟩
  obtain ⟨-, hrow2⟩ := (hrow ρμ hρ hM' x)
  obtain ⟨hrow1, -⟩ := (hrow ρμ hρ hM' x)
  have hδ0 : 0 ≤ HRS.MS.Phase2S82.deltaN N := s82r_deltaN_nonneg hN0
  have hδ1 : 1 / (N : ℝ) ≤ HRS.MS.Phase2S82.deltaN N := s82r_delta_ge2 hN0
  obtain ⟨hi2, hb2⟩ := hrow2 (N : ℝ) hN1
  have hf1 : ∀ y, (min (lam * V.q y x) 1) ^ 2 ≤ (P / N) ^ 2 * (min (q (x - y)) N) ^ 2 := by
    intro y
    rw [hVqx y, ← mul_pow]
    refine pow_le_pow_left₀ (le_min (mul_nonneg hlam0 (hq0 y)) zero_le_one) ?_ 2
    exact wr13e_min_le (hq0 y) hlamP hP1 hNpos
  have hf1i : Integrable (fun y => (min (lam * V.q y x) 1) ^ 2) (HRS.Whole.withDensityReal ρμ) := by
    refine Integrable.of_bound ((hVm.const_mul lam).min measurable_const |>.pow_const 2).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ min (lam * V.q y x) 1 := le_min (mul_nonneg hlam0 (hV0 y)) zero_le_one
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have : min (lam * V.q y x) 1 ≤ 1 := min_le_right _ _
    nlinarith
  have hA : ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν ≤
      Cν * ((P / N) ^ 2 * (Cb * Real.log (Real.exp 1 * N))) := by
    calc ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν
        ≤ Cν * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂(HRS.Whole.withDensityReal ρμ) :=
          wr13e_integral_le_of_le_smul hνle hCν0 (fun y => sq_nonneg _) hf1i
      _ ≤ Cν * ∫ y, (P / N) ^ 2 * (min (q (x - y)) N) ^ 2 ∂(HRS.Whole.withDensityReal ρμ) := by
          refine mul_le_mul_of_nonneg_left (integral_mono hf1i (hi2.const_mul _) hf1) hCν0
      _ = Cν * ((P / N) ^ 2 * ∫ y, (min (q (x - y)) N) ^ 2 ∂(HRS.Whole.withDensityReal ρμ)) := by
          rw [integral_const_mul]
      _ ≤ Cν * ((P / N) ^ 2 * (Cb * Real.log (Real.exp 1 * N))) := by
          gcongr
  have hLpos : 0 < (N : ℝ) / P := by positivity
  obtain ⟨hi1, hb1⟩ := hrow1 ((N : ℝ) / P) hLpos
  have hf2 : ∀ y, max (lam * V.q y x - 1) 0 ≤ P / N * max (q (x - y) - N / P) 0 := by
    intro y
    rw [hVqx y]
    exact wr13e_max_le (hq0 y) hlamP hP1 hNpos
  have hf2i : Integrable (fun y => max (lam * V.q y x - 1) 0) (HRS.Whole.withDensityReal ρμ) := by
    refine Integrable.mono' (hi1.const_mul (P / N))
      (((hVm.const_mul lam).sub_const 1).max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact hf2 y
  have hB : ∫ y, max (lam * V.q y x - 1) 0 ∂ν ≤ Cν * ((P / N) * (Ca / ((N : ℝ) / P))) := by
    calc ∫ y, max (lam * V.q y x - 1) 0 ∂ν
        ≤ Cν * ∫ y, max (lam * V.q y x - 1) 0 ∂(HRS.Whole.withDensityReal ρμ) :=
          wr13e_integral_le_of_le_smul hνle hCν0 (fun y => le_max_right _ _) hf2i
      _ ≤ Cν * ∫ y, P / N * max (q (x - y) - N / P) 0 ∂(HRS.Whole.withDensityReal ρμ) :=
          mul_le_mul_of_nonneg_left (integral_mono hf2i (hi1.const_mul _) hf2) hCν0
      _ = Cν * ((P / N) * ∫ y, max (q (x - y) - N / P) 0 ∂(HRS.Whole.withDensityReal ρμ)) := by
          rw [integral_const_mul]
      _ ≤ Cν * ((P / N) * (Ca / ((N : ℝ) / P))) := by
          gcongr
  have hlogδ : Real.log (Real.exp 1 * N) = N * HRS.MS.Phase2S82.deltaN N := by
    unfold HRS.MS.Phase2S82.deltaN HRS.MS.Phase2S82.logN; field_simp
  have hE1 : (n : ℝ) * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν ≤ Cν * Cb * P ^ 2 * HRS.MS.Phase2S82.deltaN N := by
    calc (n : ℝ) * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν
        ≤ n * (Cν * ((P / N) ^ 2 * (Cb * Real.log (Real.exp 1 * N)))) :=
          mul_le_mul_of_nonneg_left hA hn0
      _ = (Cν * Cb * P ^ 2 * HRS.MS.Phase2S82.deltaN N) * ((n : ℝ) / N) := by
          rw [hlogδ]; field_simp
      _ ≤ (Cν * Cb * P ^ 2 * HRS.MS.Phase2S82.deltaN N) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_one hNpos]; exact hnN
      _ = _ := mul_one _
  have hE2 : (n : ℝ) * ∫ y, max (lam * V.q y x - 1) 0 ∂ν ≤ Cν * Ca * P ^ 2 * HRS.MS.Phase2S82.deltaN N := by
    calc (n : ℝ) * ∫ y, max (lam * V.q y x - 1) 0 ∂ν
        ≤ n * (Cν * ((P / N) * (Ca / ((N : ℝ) / P)))) := mul_le_mul_of_nonneg_left hB hn0
      _ = (Cν * Ca * P ^ 2 * (1 / (N : ℝ))) * ((n : ℝ) / N) := by
          field_simp
      _ ≤ (Cν * Ca * P ^ 2 * HRS.MS.Phase2S82.deltaN N) * 1 := by
          rw [mul_one]
          calc (Cν * Ca * P ^ 2 * (1 / (N : ℝ))) * ((n : ℝ) / N)
              ≤ (Cν * Ca * P ^ 2 * (1 / (N : ℝ))) * 1 := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                rw [div_le_one hNpos]; exact hnN
            _ ≤ Cν * Ca * P ^ 2 * HRS.MS.Phase2S82.deltaN N := by
                rw [mul_one]
                exact mul_le_mul_of_nonneg_left hδ1 (by positivity)
      _ = _ := mul_one _
  have hexp : 0 < Real.exp mb := Real.exp_pos _
  calc Real.exp mb * (n * ∫ y, (min (lam * V.q y x) 1) ^ 2 ∂ν) + n * ∫ y, max (lam * V.q y x - 1) 0 ∂ν
      ≤ Real.exp mb * (Cν * Cb * P ^ 2 * HRS.MS.Phase2S82.deltaN N) + Cν * Ca * P ^ 2 * HRS.MS.Phase2S82.deltaN N :=
        add_le_add (mul_le_mul_of_nonneg_left hE1 hexp.le) hE2
    _ = _ := by ring

end HRS.MS.S82R

end
