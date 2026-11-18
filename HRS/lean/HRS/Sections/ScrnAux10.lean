import HRS.Sections.ScrnAux9

/-!
# Packet SCRN, part 10: the limiting covariance entry as an integral of `F_a conj F_c · scrnk`

`mesoCovMatrix` entries are `Re ∫ φ̂_a conj(φ̂_c) k_b(|t_a - t_c|, t_a + t_c, 2π|ξ|) dξ`
(`meso_entry_eq`), and the kernel `scrnk` is the radial profile of `ScrnAux6`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal FourierTransform ComplexConjugate

namespace HRS

variable {d : ℕ}

lemma scrnS_nonneg' {c q b ρ : ℝ} (hc : 0 < c) (hb : 0 < b) (hρ : 0 ≤ ρ) :
    0 ≤ scrnS c q b ρ := by
  unfold scrnS
  have h1 : 0 ≤ ρ ^ q := Real.rpow_nonneg hρ q
  have : 0 < b * c := mul_pos hb hc
  positivity

lemma scrnS_lt_one' {c q b ρ : ℝ} (hc : 0 < c) (hb : 0 < b) (hρ : 0 ≤ ρ) :
    scrnS c q b ρ < 1 := by
  unfold scrnS
  have h1 : 0 ≤ ρ ^ q := Real.rpow_nonneg hρ q
  have : 0 < b * c := mul_pos hb hc
  rw [div_lt_one (by positivity)]
  linarith

lemma scrnA_nonneg' {c q b ρ : ℝ} (hc : 0 < c) (hb : 0 < b) (hρ : 0 ≤ ρ) :
    0 ≤ scrnA c q b ρ := by
  unfold scrnA
  have h1 : 0 ≤ ρ ^ (2 - q) := Real.rpow_nonneg hρ _
  positivity

lemma scrnk_nonneg' {c q b ρ τ₁ τ₂ : ℝ} (hc : 0 < c) (hb : 0 < b) (hρ : 0 ≤ ρ) :
    0 ≤ scrnk c q b τ₁ τ₂ ρ := by
  have h1 := scrnS_nonneg' (q := q) hc hb hρ
  have h2 := scrnS_lt_one' (q := q) hc hb hρ
  unfold scrnk
  have := Real.exp_pos (-τ₁ * scrnA c q b ρ)
  have := Real.exp_pos (-τ₂ * scrnA c q b ρ)
  have : 0 ≤ 1 - scrnS c q b ρ := by linarith
  positivity

lemma scrnk_le_one' {c q b ρ τ₁ τ₂ : ℝ} (hc : 0 < c) (hb : 0 < b) (hρ : 0 ≤ ρ) (h1 : 0 ≤ τ₁)
    (h2 : 0 ≤ τ₂) : scrnk c q b τ₁ τ₂ ρ ≤ 1 := by
  have hS := scrnS_nonneg' (q := q) hc hb hρ
  have hS1 := scrnS_lt_one' (q := q) hc hb hρ
  have hA := scrnA_nonneg' (q := q) hc hb hρ
  unfold scrnk
  have e1 : Real.exp (-τ₁ * scrnA c q b ρ) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith)
  have e2 : Real.exp (-τ₂ * scrnA c q b ρ) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith)
  have : 0 ≤ 1 - scrnS c q b ρ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left e1 hS, mul_le_mul_of_nonneg_left e2 this]

lemma measurable_scrnk (c q b τ₁ τ₂ : ℝ) : Measurable (scrnk c q b τ₁ τ₂) := by
  unfold scrnk scrnS scrnA
  fun_prop

lemma meso_integrand_eq_scrnk (s b t u : ℝ) (ξ : Euc d) :
    Real.exp (-(t - u) * mesoRate d s b ξ) *
      (mesoSpectral d s b ξ + (1 - mesoSpectral d s b ξ) * Real.exp (-2 * u * mesoRate d s b ξ)) =
    scrnk (rieszConst d s) ((d : ℝ) - s) b (t - u) (t + u) (2 * Real.pi * ‖ξ‖) := by
  unfold scrnk mesoRate mesoSpectral scrnS scrnA
  have e : Real.exp (-(t + u) * (b⁻¹ * (2 * Real.pi * ‖ξ‖) ^ 2 +
        rieszConst d s * (2 * Real.pi * ‖ξ‖) ^ (2 - ((d : ℝ) - s)))) =
      Real.exp (-(t - u) * (b⁻¹ * (2 * Real.pi * ‖ξ‖) ^ 2 +
        rieszConst d s * (2 * Real.pi * ‖ξ‖) ^ (2 - ((d : ℝ) - s)))) *
        Real.exp (-2 * u * (b⁻¹ * (2 * Real.pi * ‖ξ‖) ^ 2 +
          rieszConst d s * (2 * Real.pi * ‖ξ‖) ^ (2 - ((d : ℝ) - s)))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  ring

/-- The kernel entry: `K_b^{ac}(ξ) = k_b(|t_a-t_c|, t_a+t_c, 2π|ξ|)`. -/
def scrnKab (d : ℕ) (s b : ℝ) {p : ℕ} (t : Fin p → ℝ) (a c : Fin p) (ξ : Euc d) : ℝ :=
  scrnk (rieszConst d s) ((d : ℝ) - s) b |t a - t c| (t a + t c) (2 * Real.pi * ‖ξ‖)

/-- The integrand of the limiting covariance entry. -/
def scrnGab (d : ℕ) (s b : ℝ) {p : ℕ} (t : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (a c : Fin p)
    (ξ : Euc d) : ℂ :=
  𝓕 (scrnPhiC (φ a)) ξ * (starRingEnd ℂ) (𝓕 (scrnPhiC (φ c)) ξ) * ((scrnKab d s b t a c ξ : ℝ) : ℂ)

lemma meso_entry_eq (s b : ℝ) {p : ℕ} (t : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (a c : Fin p) :
    mesoCovMatrix d s b t φ a c = (∫ ξ : Euc d, scrnGab d s b t φ a c ξ).re := by
  unfold mesoCovMatrix
  simp only [Matrix.of_apply]
  by_cases h : t c ≤ t a
  · rw [if_pos h]
    unfold mesoCovIntegral
    congr 2
    funext ξ
    unfold scrnGab scrnKab scrnPhiC
    rw [meso_integrand_eq_scrnk, abs_of_nonneg (by linarith)]
  · rw [if_neg h]
    have h' : t a ≤ t c := le_of_lt (not_le.1 h)
    unfold mesoCovIntegral
    have : ∀ ξ : Euc d,
        𝓕 (fun x => ((φ c x : ℝ) : ℂ)) ξ * (starRingEnd ℂ) (𝓕 (fun x => ((φ a x : ℝ) : ℂ)) ξ) *
          (((Real.exp (-(t c - t a) * mesoRate d s b ξ) *
            (mesoSpectral d s b ξ + (1 - mesoSpectral d s b ξ) *
              Real.exp (-2 * t a * mesoRate d s b ξ)) : ℝ) : ℂ)) =
        (starRingEnd ℂ) (scrnGab d s b t φ a c ξ) := by
      intro ξ
      unfold scrnGab scrnKab scrnPhiC
      rw [meso_integrand_eq_scrnk, abs_sub_comm, abs_of_nonneg (by linarith)]
      simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
      ring
    simp_rw [this]
    rw [integral_conj, Complex.conj_re]

end HRS
