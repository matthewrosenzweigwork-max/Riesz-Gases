import HRS.MC.CepN1Aux7

/-!
# Packet CEPN1, part 8: the one-dimensional tube for a Lipschitz target
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal Real

noncomputable section

namespace HRS.MC.CepN1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem cepn1_oneD [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {g : ℝ≥0 → ℝ} (hg0 : g 0 = 0) {L : ℝ} (hL : 0 ≤ L)
    (hgL : ∀ s t : ℝ≥0, |g s - g t| ≤ L * |(s : ℝ) - t|) {T' η : ℝ} (hT' : 0 < T') (hη : 0 < η) :
    ∃ S : Set (ℝ≥0 → ℝ), MeasurableSet S ∧ 0 < P ((fun ω t => B t ω) ⁻¹' S) ∧
      ∀ z ∈ S, Continuous z → ∀ t : ℝ≥0, (t : ℝ) ≤ T' → |z t - g t| < η / 2 := by
  obtain ⟨M, hM, h, hhc, hhpos, hLh, hq⟩ := cepn1_param hT' hη hL
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hε : 0 < η / (8 * M) := by positivity
  have hρ : 0 < η / 8 := by positivity
  refine ⟨{z | z 0 = 0 ∧ cepn1_Good h (η / (8 * M)) (η / 8) M g z},
    ?_, ?_, ?_⟩
  · have h0 : MeasurableSet {z : ℝ≥0 → ℝ | z 0 = 0} :=
      measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
    exact h0.inter (cepn1_good_meas h _ _ M g)
  · have hlb := cepn1_good_prob (P := P) hhpos hε hρ M g B hB hg0 (fun s t _ _ => hgL s t)
    have hpos : 0 < ENNReal.ofReal (cepn1_q h L (η / (8 * M)) (η / 8)) ^ M := by
      apply ENNReal.pow_pos
      exact ENNReal.ofReal_pos.2 hq
    refine lt_of_lt_of_le hpos (hlb.trans (measure_mono_ae ?_))
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω hgood
    exact ⟨hω, hgood⟩
  · rintro z ⟨hz0, hzg⟩ hzc t ht
    have htM : t ≤ (M : ℝ≥0) * h := by
      have : (t : ℝ) ≤ ((M : ℝ≥0) * h : ℝ≥0) := by
        rw [NNReal.coe_mul, NNReal.coe_natCast, hhc]
        have : (M : ℝ) * (T' / M) = T' := by field_simp
        linarith
      exact_mod_cast this
    have := cepn1_good_bound hε.le hρ.le hL M g z hg0 (fun s t _ _ => hgL s t) hzc hz0 hzg t htM
    have e : (M : ℝ) * (η / (8 * M)) = η / 8 := by field_simp
    rw [e] at this
    have : L * (h : ℝ) ≤ η / 8 := hLh
    linarith

end HRS.MC.CepN1
