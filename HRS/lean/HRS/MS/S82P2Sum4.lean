import HRS.MS.S82P2Sum3

/-!
# S8.2 (S82P2): simplified second moment of a centered sum (UNCOMPILED DRAFT, needs Sum3 compiled)
`∫⁻ S^2 ≤ ofReal (Cs * N * ∫ ψ^2)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

lemma s82p2_logN_sq_le {N : ℕ} (hN : 1 ≤ N) : (Phase2S82.logN N) ^ 2 ≤ 4 * N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have h1 := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hNpos.le] at h1
  have hL : Phase2S82.logN N = 1 + Real.log N := by
    unfold Phase2S82.logN
    rw [Real.log_mul (Real.exp_pos 1).ne' hNpos.ne', Real.log_exp]
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hL0 : 0 ≤ Phase2S82.logN N := by rw [hL]; linarith
  have hL1 : Phase2S82.logN N ≤ 2 * Real.sqrt N := by rw [hL]; linarith
  calc (Phase2S82.logN N) ^ 2 ≤ (2 * Real.sqrt N) ^ 2 := pow_le_pow_left₀ hL0 hL1 2
    _ = 4 * N := by rw [mul_pow, Real.sq_sqrt hNpos.le]; ring

lemma s82p2_deltaN_sq_le {N : ℕ} (hN : 1 ≤ N) : (Phase2S82.deltaN N) ^ 2 ≤ 4 / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold Phase2S82.deltaN
  rw [div_pow, div_le_div_iff₀ (by positivity) hNpos]
  have := s82p2_logN_sq_le hN
  nlinarith

theorem s82p2_centered_sum_sq_simple {d : ℕ} {a beta C0 C1 : ℝ} {rho : Euc d → ℝ}
    {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)] (hd : 2 ≤ d)
    (hW : WeakReferenceSetup d a beta rho q h C0) (hbeta : 0 < beta)
    (hP : PinComparison beta rho q h C1) (G c : ℝ) (hG : 0 < G) (hc : 0 < c)
    (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho)
    {N : ℕ} (hN : 2 ≤ N) {p n : ℕ} (hp : p ≤ 2)
    (hnp : n + p ≤ N) (hNn : N - (n + p) ≤ 2) (pins : Fin p → Euc d)
    (ψ : Euc d → ℝ) (hψm : Measurable ψ)
    (hψ2 : Integrable (fun z => ψ z ^ 2) (HRS.Whole.withDensityReal rho))
    (hψ0 : ∫ z, ψ z ∂HRS.Whole.withDensityReal rho = 0) :
    MemLp (fun X : EucConfig d n => ∑ j, ψ (X j)) 2
        (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins) ∧
      ∫⁻ X, ENNReal.ofReal ((∑ j, ψ (X j)) ^ 2)
          ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins ≤
        ENNReal.ofReal ((C0 ^ 2 * (2 + 2 * (1 + 2 * C1)) + (8 * C1 ^ 2 +
            2 * C1 ^ 2 * (1 + 2 * (1 / (1000 * beta))))) * N *
          ∫ z, ψ z ^ 2 ∂HRS.Whole.withDensityReal rho) := by
  set mu := HRS.Whole.withDensityReal rho with hmu
  have hC0 := hW.positive
  have hC1 := s82p2_pinCmp_nonneg hP
  have hq := hW.short
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδ0 := s82p2_deltaN_nonneg (N := N) (by omega)
  have hδ1 := s82p2_deltaN_le_one (N := N) (by omega)
  set B : ℝ := 1 / (1000 * beta) with hB
  have hB0 : 0 ≤ B := by positivity
  -- the weight
  set w : Euc d → ℝ := fun z => C1 * Phase2S82.deltaN N +
      C1 * min 1 ((1 + ∑ j, q (z - pins j)) / N) with hw
  have hwm : Measurable w := by
    refine measurable_const.add (measurable_const.mul ?_)
    refine measurable_const.min ?_
    refine (measurable_const.add (Finset.measurable_sum _ fun j _ =>
      hq.measurable.comp (measurable_id.sub_const _))).div_const _
  have hw0 : ∀ z, 0 ≤ w z := fun z => by
    have : 0 ≤ min 1 ((1 + ∑ j, q (z - pins j)) / (N : ℝ)) := by
      apply le_min zero_le_one
      exact div_nonneg (by have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hq.nonneg (z - pins j)); linarith) hNpos.le
    simp only [hw]
    exact add_nonneg (mul_nonneg hC1 hδ0) (mul_nonneg hC1 this)
  have hwb : ∀ z, w z ≤ C1 * Phase2S82.deltaN N + C1 := fun z => by
    simp only [hw]
    have : min 1 ((1 + ∑ j, q (z - pins j)) / (N : ℝ)) ≤ 1 := min_le_left _ _
    nlinarith
  have hw2int : Integrable (fun z => w z ^ 2) mu := by
    refine (integrable_const ((C1 * Phase2S82.deltaN N + C1) ^ 2)).mono'
      (hwm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hw0 z) (hwb z) 2
  have hψi : Integrable ψ mu :=
    ((memLp_two_iff_integrable_sq hψm.aestronglyMeasurable).2 hψ2).integrable one_le_two
  have hint : Integrable (fun z => |ψ z| * w z) mu := by
    refine (hψi.abs.const_mul (C1 * Phase2S82.deltaN N + C1)).mono'
      ((continuous_abs.measurable.comp hψm).mul hwm).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (hw0 z))]
    nlinarith [abs_nonneg (ψ z), hwb z]
  obtain ⟨hmem, hle⟩ := s82p2_centered_sum_sq hW hbeta hP hN hp hnp hNn pins ψ hψm hψ2 hψ0 hint
  refine ⟨hmem, hle.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  -- the real inequality
  set a2 : ℝ := ∫ z, ψ z ^ 2 ∂mu with ha2
  have ha20 : 0 ≤ a2 := integral_nonneg fun z => sq_nonneg _
  set E1 : ℝ := ∫ z, |ψ z| * w z ∂mu with hE1
  have hE10 : 0 ≤ E1 := integral_nonneg fun z => mul_nonneg (abs_nonneg _) (hw0 z)
  -- ∫ w² ≤ Cw / N
  have hu : Integrable (fun z => (1 + ∑ j, q (z - pins j)) / (N : ℝ)) mu := by
    refine Integrable.div_const (Integrable.add (integrable_const 1) ?_) _
    exact integrable_finset_sum _ fun j _ => s82p2_q_integrable hd hq G c hG hc rho hρ hρG (pins j)
  have hwint : ∫ z, w z ^ 2 ∂mu ≤ (8 * C1 ^ 2 + 2 * C1 ^ 2 * (1 + 2 * B)) / N := by
    have hpt : ∀ z, w z ^ 2 ≤ 2 * C1 ^ 2 * Phase2S82.deltaN N ^ 2 +
        2 * C1 ^ 2 * ((1 + ∑ j, q (z - pins j)) / N) := fun z => by
      simp only [hw]
      set u := (1 + ∑ j, q (z - pins j)) / (N : ℝ) with hu'
      have hu0 : 0 ≤ u := by
        exact div_nonneg (by have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hq.nonneg (z - pins j)); linarith) hNpos.le
      have hm0 : 0 ≤ min 1 u := le_min zero_le_one hu0
      have hm1 : min 1 u ≤ 1 := min_le_left _ _
      have hmu : min 1 u ≤ u := min_le_right _ _
      have hm2 : (min 1 u) ^ 2 ≤ u := by nlinarith
      have hb2 : (C1 * min 1 u) ^ 2 ≤ C1 ^ 2 * u := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_left hm2 (sq_nonneg C1)
      nlinarith [sq_nonneg (C1 * Phase2S82.deltaN N - C1 * min 1 u), hb2]
    have hint2 : Integrable (fun z => 2 * C1 ^ 2 * Phase2S82.deltaN N ^ 2 +
        2 * C1 ^ 2 * ((1 + ∑ j, q (z - pins j)) / (N : ℝ))) mu :=
      (integrable_const _).add (hu.const_mul _)
    refine (integral_mono hw2int hint2 hpt).trans ?_
    rw [integral_add (integrable_const _) (hu.const_mul _), integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hum : ∫ z, (1 + ∑ j, q (z - pins j)) / (N : ℝ) ∂mu ≤ (1 + 2 * B) / N := by
      rw [integral_div, integral_add (integrable_const _)
        (integrable_finset_sum _ fun j _ => s82p2_q_integrable hd hq G c hG hc rho hρ hρG (pins j)),
        integral_finset_sum _ fun j _ => s82p2_q_integrable hd hq G c hG hc rho hρ hρG (pins j)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      apply div_le_div_of_nonneg_right _ hNpos.le
      have hj : ∀ j : Fin p, ∫ z, q (z - pins j) ∂mu ≤ B := fun j => s82p2_q_mass hW hbeta (pins j)
      have : ∑ j : Fin p, ∫ z, q (z - pins j) ∂mu ≤ p * B := by
        calc _ ≤ ∑ j : Fin p, B := Finset.sum_le_sum fun j _ => hj j
          _ = p * B := by simp
      have hp2 : (p : ℝ) ≤ 2 := by exact_mod_cast hp
      nlinarith
    have hd2 := s82p2_deltaN_sq_le (N := N) (by omega)
    have hC1sq : 0 ≤ C1 ^ 2 := sq_nonneg _
    have hcm : ∫ a, 2 * C1 ^ 2 * ((1 + ∑ j, q (a - pins j)) / (N : ℝ)) ∂mu =
        2 * C1 ^ 2 * ∫ z, (1 + ∑ j, q (z - pins j)) / (N : ℝ) ∂mu := integral_const_mul _ _
    rw [hcm]
    calc 2 * C1 ^ 2 * Phase2S82.deltaN N ^ 2 + 2 * C1 ^ 2 * ∫ z, (1 + ∑ j, q (z - pins j)) / (N : ℝ) ∂mu
        ≤ 2 * C1 ^ 2 * (4 / N) + 2 * C1 ^ 2 * ((1 + 2 * B) / N) := by
          have := mul_le_mul_of_nonneg_left hd2 (by positivity : 0 ≤ 2 * C1 ^ 2)
          have := mul_le_mul_of_nonneg_left hum (by positivity : 0 ≤ 2 * C1 ^ 2)
          linarith
      _ = (8 * C1 ^ 2 + 2 * C1 ^ 2 * (1 + 2 * B)) / N := by field_simp; ring
  -- Cauchy-Schwarz
  have hcs := s82p2_cs (μ := mu) (continuous_abs.measurable.comp hψm) hwm (fun z => abs_nonneg _) hw0
    (by simpa [sq_abs] using hψ2) hw2int
  have hcs' : E1 ^ 2 ≤ a2 * ((8 * C1 ^ 2 + 2 * C1 ^ 2 * (1 + 2 * B)) / N) := by
    have h1 : E1 ≤ Real.sqrt a2 * Real.sqrt (∫ z, w z ^ 2 ∂mu) := by
      simpa [sq_abs] using hcs
    have h2 : E1 ^ 2 ≤ (Real.sqrt a2 * Real.sqrt (∫ z, w z ^ 2 ∂mu)) ^ 2 :=
      pow_le_pow_left₀ hE10 h1 2
    rw [mul_pow, Real.sq_sqrt ha20, Real.sq_sqrt (integral_nonneg fun z => sq_nonneg _)] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left hwint ha20)
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  set Cw : ℝ := 8 * C1 ^ 2 + 2 * C1 ^ 2 * (1 + 2 * B) with hCw
  have hCw0 : 0 ≤ Cw := by positivity
  have hK : 0 ≤ 2 + 2 * (1 + 2 * C1) := by linarith
  have h3 : (n * E1) ^ 2 ≤ N * Cw * a2 := by
    calc (n * E1) ^ 2 = n ^ 2 * E1 ^ 2 := by ring
      _ ≤ n ^ 2 * (a2 * (Cw / N)) := by gcongr
      _ ≤ N * (a2 * Cw) := by
        have : (n : ℝ) ^ 2 ≤ N * N := by nlinarith
        rw [show (n : ℝ) ^ 2 * (a2 * (Cw / N)) = (n : ℝ) ^ 2 / N * (a2 * Cw) by field_simp]
        have h5 : (n : ℝ) ^ 2 / N ≤ N := by rw [div_le_iff₀ hNpos]; nlinarith
        exact mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = N * Cw * a2 := by ring
  have h4 : C0 ^ 2 * (2 + 2 * (1 + 2 * C1)) * n * a2 ≤ C0 ^ 2 * (2 + 2 * (1 + 2 * C1)) * N * a2 := by
    gcongr
  nlinarith

end HRS.MS.S82P2
