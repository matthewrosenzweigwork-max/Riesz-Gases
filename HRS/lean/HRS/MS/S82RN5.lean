import HRS.MS.S82RN4

/-!
# S8.2 R02 (S82R), N5: a supersolution for one fractional pin
`A q(. - p) + B` with `A = 2K`, `B` depending only on `(q, M, beta, K, gamma)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

lemma s82r_row_integrable (hd : 2 ≤ d) {q : Euc d → ℝ} (hq : ShortRangePole d q) {M : ℝ}
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M) (w : Euc d) :
    Integrable (fun u => q (u - w)) (HRS.Whole.withDensityReal ρ) := by
  obtain ⟨Ca, Cb, hCa, hCb, H⟩ := s82r_rows hd hq M
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  obtain ⟨hi, -⟩ := (H ρ hρ hM w).1 1 one_pos
  have hev : ∀ u, q (u - w) = q (w - u) := fun u => by rw [← hq.even (w - u), neg_sub]
  have hm : Measurable (fun y => q (w - y)) := hq.measurable.comp (measurable_const.sub measurable_id)
  have hb : Integrable (fun y => min (q (w - y)) 1) (HRS.Whole.withDensityReal ρ) :=
    Integrable.of_bound (hm.min measurable_const).aestronglyMeasurable 1 (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hq.nonneg _) zero_le_one)]; exact min_le_right _ _)
  have e : (fun u => q (u - w)) = fun u => min (q (w - u)) 1 + max (q (w - u) - 1) 0 := by
    funext u
    rw [hev u]
    rcases le_total (q (w - u)) 1 with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  rw [e]
  exact hb.add hi

theorem s82r_super_pin (hd : 2 ≤ d) {q : Euc d → ℝ} (hq : ShortRangePole d q) (M : ℝ)
    {β K γ : ℝ} (hβ : 0 < β) (hK : 0 < K) (hγ : 0 ≤ γ) (hα : β * γ * (K + K ^ 2) < 1) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (∀ u : Euc d, ∫ z, q (z - u) ∂(HRS.Whole.withDensityReal ρ) ≤ γ) →
      ∀ (n : ℕ) (lam : ℝ), 1 ≤ n → 0 ≤ lam → ((n : ℝ) - 1) * lam ≤ β → ∀ p z : Euc d, z ≠ p →
        K * q (z - p) + K ^ 2 * γ + ((n : ℝ) - 1) * ∫ u, (A * q (u - p) + B) *
            (K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ))
              ∂(HRS.Whole.withDensityReal ρ) ≤ A * q (z - p) + B := by
  have hε : 0 < 1 / (2 * β * K) := by positivity
  obtain ⟨Cε, hCε, hconv⟩ := s82r_conv2_eps hd hq M hε
  set D : ℝ := 1 - β * γ * (K + K ^ 2) with hD
  have hDpos : 0 < D := by rw [hD]; linarith
  set B : ℝ := (K ^ 2 * γ + 2 * β * K ^ 2 * Cε + 2 * β * K ^ 3 * γ ^ 2) / D with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hBD : B * D = K ^ 2 * γ + 2 * β * K ^ 2 * Cε + 2 * β * K ^ 3 * γ ^ 2 := by
    rw [hB]; field_simp
  refine ⟨2 * K, B, by positivity, hB0, fun ρ hρ hM hrow n lam hn hlam hnl p z hzp => ?_⟩
  set μ := HRS.Whole.withDensityReal ρ with hμ
  haveI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hq0 := hq.nonneg
  have hqm : Measurable q := hq.measurable
  have hev : ∀ w, q (-w) = q w := hq.even
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hqi : ∀ w : Euc d, Integrable (fun u => q (u - w)) μ := fun w => s82r_row_integrable hd hq hρ hM w
  obtain ⟨hGi, hG⟩ := hconv ρ hρ hM z p hzp
  have hJp : ∫ u, q (u - p) ∂μ ≤ γ := hrow p
  have hJz : ∫ u, q (u - z) ∂μ ≤ γ := hrow z
  have hev' : ∀ u, q (z - u) = q (u - z) := fun u => by rw [← hev (u - z), neg_sub]
  set a : Euc d → ℝ := fun u => q (u - p) with ha
  set b : Euc d → ℝ := fun u => q (u - z) with hb
  set g : Euc d → ℝ := fun u => lam * (2 * K * K * (q (z - u) * q (u - p)) + 2 * K * K ^ 2 * γ * q (u - p) +
      B * K * q (u - z) + B * K ^ 2 * γ) with hg
  have hgi : Integrable g μ := by
    have h1 := hGi.const_mul (2 * K * K)
    have h2 := (hqi p).const_mul (2 * K * K ^ 2 * γ)
    have h3 := (hqi z).const_mul (B * K)
    have h4 : Integrable (fun _ : Euc d => B * K ^ 2 * γ) μ := integrable_const _
    exact (((h1.add h2).add h3).add h4).const_mul lam
  have hfm : Measurable (fun u => (2 * K * q (u - p) + B) *
      (K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ))) := by
    refine ((measurable_const.mul (hqm.comp (measurable_id.sub measurable_const))).add measurable_const).mul ?_
    exact (measurable_const.mul (measurable_const.sub (Real.measurable_exp.comp
      (measurable_const.mul (hqm.comp (measurable_id.sub measurable_const))).neg))).add measurable_const
  have hdle : ∀ u, 1 - Real.exp (-(lam * q (u - z))) ≤ lam * q (u - z) := fun u => by
    have := Real.add_one_le_exp (-(lam * q (u - z))); linarith
  have hd0 : ∀ u, 0 ≤ 1 - Real.exp (-(lam * q (u - z))) := fun u => by
    have : Real.exp (-(lam * q (u - z))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [hq0 (u - z)])
    linarith
  have hfg : ∀ u, (2 * K * q (u - p) + B) * (K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ)) ≤ g u := by
    intro u
    have hp0 := hq0 (u - p)
    have hz0 := hq0 (u - z)
    have h1 : K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ) ≤
        K * (lam * q (u - z)) + K ^ 2 * (lam * γ) := by
      have := mul_le_mul_of_nonneg_left (hdle u) hK.le; linarith
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * K * q (u - p) + B)
    refine this.trans (le_of_eq ?_)
    simp only [hg]; rw [hev' u]; ring
  have hfnn : ∀ u, 0 ≤ (2 * K * q (u - p) + B) * (K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ)) :=
    fun u => mul_nonneg (by have := hq0 (u - p); positivity)
      (add_nonneg (mul_nonneg hK.le (hd0 u)) (by positivity))
  have hIle : ∫ u, (2 * K * q (u - p) + B) * (K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ)) ∂μ ≤
      ∫ u, g u ∂μ := integral_mono_of_nonneg (ae_of_all _ hfnn) hgi (ae_of_all _ hfg)
  have hgint : ∫ u, g u ∂μ = lam * (2 * K * K * ∫ u, q (z - u) * q (u - p) ∂μ +
      2 * K * K ^ 2 * γ * ∫ u, q (u - p) ∂μ + B * K * ∫ u, q (u - z) ∂μ + B * K ^ 2 * γ) := by
    have h1 : Integrable (fun u => 2 * K * K * (q (z - u) * q (u - p))) μ := hGi.const_mul (2 * K * K)
    have h2 : Integrable (fun u => 2 * K * K ^ 2 * γ * q (u - p)) μ := (hqi p).const_mul _
    have h3 : Integrable (fun u => B * K * q (u - z)) μ := (hqi z).const_mul _
    have h4 : Integrable (fun _ : Euc d => B * K ^ 2 * γ) μ := integrable_const _
    have h12 : Integrable (fun u => 2 * K * K * (q (z - u) * q (u - p)) + 2 * K * K ^ 2 * γ * q (u - p)) μ :=
      h1.add h2
    have h123 : Integrable (fun u => 2 * K * K * (q (z - u) * q (u - p)) + 2 * K * K ^ 2 * γ * q (u - p) +
        B * K * q (u - z)) μ := h12.add h3
    simp only [hg]
    rw [integral_const_mul, integral_add h123 h4, integral_add h12 h3, integral_add h1 h2,
      integral_const_mul, integral_const_mul, integral_const_mul]
    simp
  set G : ℝ := ∫ u, q (z - u) * q (u - p) ∂μ with hGdef
  have hG0 : 0 ≤ G := integral_nonneg fun u => mul_nonneg (hq0 _) (hq0 _)
  have hJ0p : 0 ≤ ∫ u, q (u - p) ∂μ := integral_nonneg fun u => hq0 _
  have hJ0z : 0 ≤ ∫ u, q (u - z) ∂μ := integral_nonneg fun u => hq0 _
  set Q : ℝ := 2 * K * K * G + 2 * K * K ^ 2 * γ * ∫ u, q (u - p) ∂μ + B * K * ∫ u, q (u - z) ∂μ +
      B * K ^ 2 * γ with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hQle : Q ≤ 2 * K * K * G + 2 * K * K ^ 2 * γ * γ + B * K * γ + B * K ^ 2 * γ := by
    rw [hQ]
    have h1 := mul_le_mul_of_nonneg_left hJp (by positivity : 0 ≤ 2 * K * K ^ 2 * γ)
    have h2 := mul_le_mul_of_nonneg_left hJz (by positivity : 0 ≤ B * K)
    linarith
  have hnl' : ((n : ℝ) - 1) * ∫ u, g u ∂μ ≤ β * Q := by
    rw [hgint]
    calc ((n : ℝ) - 1) * (lam * Q) = (((n : ℝ) - 1) * lam) * Q := by ring
      _ ≤ β * Q := mul_le_mul_of_nonneg_right hnl hQ0
  have hmain : ((n : ℝ) - 1) * ∫ u, (2 * K * q (u - p) + B) *
      (K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ)) ∂μ ≤ β * Q :=
    (mul_le_mul_of_nonneg_left hIle hn1).trans hnl'
  have hGb : G ≤ 1 / (2 * β * K) * q (z - p) + Cε := hG
  have hQb : β * Q ≤ K * q (z - p) + 2 * β * K ^ 2 * Cε + 2 * β * K ^ 3 * γ ^ 2 +
      B * (β * γ * (K + K ^ 2)) := by
    have h1 := mul_le_mul_of_nonneg_left hQle hβ.le
    have h2 : β * (2 * K * K * G) ≤ β * (2 * K * K * (1 / (2 * β * K) * q (z - p) + Cε)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGb (by positivity)) hβ.le
    have h3 : β * (2 * K * K * (1 / (2 * β * K) * q (z - p) + Cε)) =
        K * q (z - p) + 2 * β * K ^ 2 * Cε := by field_simp
    nlinarith [h1, h2, h3]
  have : K * q (z - p) + K ^ 2 * γ + ((n : ℝ) - 1) * ∫ u, (2 * K * q (u - p) + B) *
      (K * (1 - Real.exp (-(lam * q (u - z)))) + K ^ 2 * (lam * γ)) ∂μ ≤
      K * q (z - p) + K ^ 2 * γ + (K * q (z - p) + 2 * β * K ^ 2 * Cε + 2 * β * K ^ 3 * γ ^ 2 +
      B * (β * γ * (K + K ^ 2))) := by linarith
  refine this.trans ?_
  have hBD' : B * (1 - β * γ * (K + K ^ 2)) = K ^ 2 * γ + 2 * β * K ^ 2 * Cε + 2 * β * K ^ 3 * γ ^ 2 := hBD
  nlinarith [hBD']

end HRS.MS.S82R

end
