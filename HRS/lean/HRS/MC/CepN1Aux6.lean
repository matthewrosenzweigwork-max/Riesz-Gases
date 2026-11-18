import HRS.MC.CepN1Aux5

/-!
# Packet CEPN1, part 6: the lower bound `q^M` for the `M`-piece event
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal Real

noncomputable section

namespace HRS.MC.CepN1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The one-piece probability bound. -/
def cepn1_q (h : ℝ≥0) (L ε ρ : ℝ) : ℝ :=
  2 * ε * ((√(2 * π * h))⁻¹ * Real.exp (-(L * h + ε) ^ 2 / (2 * h))) - h / ρ ^ 2

theorem cepn1_piece_lb [IsProbabilityMeasure P] {Z : ℝ≥0 → Ω → ℝ} (hZ : IsPreBrownianReal Z P)
    {h : ℝ≥0} (hh : 0 < h) {L ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) {a : ℝ} (ha : |a| ≤ L * h) :
    ENNReal.ofReal (cepn1_q h L ε ρ) ≤
      P {ω | |Z h ω - a| < ε ∧ ∀ n k : ℕ, k ≤ 2 ^ n → |Z (cepn1_dy h n k) ω| ≤ ρ} := by
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (cepn1_piece hZ h hh a hε hρ)
  unfold cepn1_q
  have hpos : (0 : ℝ) < h := by exact_mod_cast hh
  have h1 : (L * h + ε) ^ 2 ≥ (|a| + ε) ^ 2 := by
    have := abs_nonneg a
    nlinarith
  have h2 : Real.exp (-(L * h + ε) ^ 2 / (2 * h)) ≤ Real.exp (-(|a| + ε) ^ 2 / (2 * h)) := by
    apply Real.exp_le_exp.2
    exact div_le_div_of_nonneg_right (neg_le_neg h1) (by positivity)
  have h3 : 0 ≤ 2 * ε * (√(2 * π * h))⁻¹ := by positivity
  have := mul_le_mul_of_nonneg_left h2 h3
  linarith [this, mul_assoc (2 * ε) (√(2 * π * h))⁻¹ (Real.exp (-(L * h + ε) ^ 2 / (2 * h))),
    mul_assoc (2 * ε) (√(2 * π * h))⁻¹ (Real.exp (-(|a| + ε) ^ 2 / (2 * h)))]

theorem cepn1_good_prob [IsProbabilityMeasure P] {h : ℝ≥0} (hh : 0 < h) {L ε ρ : ℝ} (hε : 0 < ε)
    (hρ : 0 < ρ) :
    ∀ (M : ℕ) (g : ℝ≥0 → ℝ) (Z : ℝ≥0 → Ω → ℝ), IsPreBrownianReal Z P → g 0 = 0 →
      cepn1_LipOn h L M g →
      ENNReal.ofReal (cepn1_q h L ε ρ) ^ M ≤ P {ω | cepn1_Good h ε ρ M g (fun t => Z t ω)} := by
  intro M
  induction M with
  | zero =>
    intro g Z hZ _ _
    simp [cepn1_Good]
  | succ M ih =>
    intro g Z hZ hg0 hgL
    rw [cepn1_good_succ_prob hZ, pow_succ, mul_comm]
    have hZ' := hZ.shift h
    have h1 := ih (fun t => g (h + t) - g h) (fun t ω => Z (h + t) ω - Z h ω) hZ' (by simp)
      (cepn1_LipOn_shift hgL)
    have ha : |g h| ≤ L * h := by
      have := hgL h 0 (by push_cast; rw [add_mul, one_mul]; exact le_add_of_nonneg_left bot_le) bot_le
      simp only [hg0, sub_zero, NNReal.coe_zero] at this
      rw [abs_of_nonneg (NNReal.coe_nonneg h)] at this
      simpa using this
    have h2 := cepn1_piece_lb hZ hh hε hρ ha
    exact mul_le_mul' h2 h1

end HRS.MC.CepN1
