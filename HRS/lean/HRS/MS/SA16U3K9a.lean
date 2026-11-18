import HRS.MS.SA16CutK5
import HRS.MS.CzHlsAux2

/-!
# S.A.16 K9, part (a): `splice_screened_low` for `0 < θ < 1` (worker SA16U3)

No bridge to `pvOdd` is needed: the splice kernel is dominated everywhere by the Riesz kernel
`|z|^{(1-θ)-d}` (`sa16k5_ks_bound`), so `|spliceOdd (aW)| ≤ I_{1-θ}|aW|` pointwise, and the Hardy-Littlewood-Sobolev
bound `riesz_pot_Lp_of_le` (`L^q → L^p`, `1/q = 1/p + (1-θ)/d`) plus Hölder close the estimate.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Hls HRS.Commutator.Whole

section K9a
variable {d : ℕ}

/-- pointwise domination of the splice operator by the Riesz potential of `|h|` -/
lemma sa16u3_enorm_le {θ δ : ℝ} (hθ0 : 0 ≤ θ) (hδ : 0 < δ) (i : Fin d) (h : Euc d → ℝ) (x : Euc d) :
    ‖spliceOdd d θ δ i h x‖ₑ ≤ cmxHLS_I (1 - θ) (fun y => ‖h y‖ₑ) x := by
  rw [hlsg_pot_eq_z]
  unfold spliceOdd
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
  rw [enorm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [Real.enorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal ?_
  have := sa16k5_ks_bound hδ hθ0 i z (d := d)
  have e : (1 - θ) - (d : ℝ) = 1 - ((d : ℝ) + θ) := by ring
  rw [e]; exact this

lemma sa16u3_aesm {θ δ : ℝ} (i : Fin d) {h : Euc d → ℝ} (hh : AEStronglyMeasurable h volume) :
    AEStronglyMeasurable (spliceOdd d θ δ i h) volume :=
  hlsg_aesm_conv (sa16k5_ks_meas θ δ i) hh

/-- exponent bookkeeping for `1/q = 1/p + (1-θ)/d` -/
lemma sa16u3_exponents (hd : 1 ≤ d) {θ p : ℝ} (hθ1 : θ < 1) (hp : 0 < p)
    (hq : 1 / p + (1 - θ) / d < 1) :
    ∃ q : ℝ, 0 < q ∧ 1 < q ∧ q < p ∧ 1 / p = 1 / q - (1 - θ) / d ∧
      ((d : ℝ) / (1 - θ))⁻¹ + p⁻¹ = q⁻¹ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h1θ : 0 < 1 - θ := by linarith
  refine ⟨(1 / p + (1 - θ) / d)⁻¹, by positivity, ?_, ?_, ?_, ?_⟩
  · have h0 : 0 < 1 / p + (1 - θ) / d := by positivity
    exact (one_lt_inv₀ h0).2 hq
  · have hpos : 0 < (1 - θ) / d := by positivity
    have h0 : 0 < 1 / p + (1 - θ) / d := by positivity
    have : 1 / p < 1 / p + (1 - θ) / d := by linarith
    exact (inv_lt_comm₀ h0 hp).2 (by rwa [one_div] at this ⊢)
  · rw [one_div (1 / p + (1 - θ) / d)⁻¹, inv_inv]; ring
  · rw [inv_inv, inv_div, one_div]; ring

end K9a

/-- K9 for `0 < θ < 1` -/
theorem sa16u3_screened_lt_one (d : ℕ) (hd : 1 ≤ d) (θ p : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hp : 2 ≤ p) (hq : 1 / p + (1 - θ) / (d : ℝ) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ i : Fin d, ∀ a W : Euc d → ℝ,
      MemLp a (ENNReal.ofReal ((d : ℝ) / (1 - θ))) volume →
      MemLp W (ENNReal.ofReal p) volume →
      eLpNorm (spliceOdd d θ δ i (fun y => a y * W y)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm a (ENNReal.ofReal ((d : ℝ) / (1 - θ))) volume *
          eLpNorm W (ENNReal.ofReal p) volume := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hp0 : 0 < p := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hr0 : 0 < (d : ℝ) / (1 - θ) := by positivity
  obtain ⟨q, hq0, hq1, hqp, hrel, hrel'⟩ := sa16u3_exponents hd hθ1 hp0 hq
  obtain ⟨CH, hCH, hK⟩ := riesz_pot_Lp_of_le hd h1θ hq1 hqp hrel
  refine ⟨CH, hCH, fun δ hδ i a W ha hW => ?_⟩
  have hholder := hlsg_holder hr0 hp0 hq0 hrel' ha.aestronglyMeasurable hW.aestronglyMeasurable
  have hhm : AEStronglyMeasurable (fun y => a y * W y) volume :=
    ha.aestronglyMeasurable.mul hW.aestronglyMeasurable
  have h2 := hK (fun y => a y * W y) _ hhm (sa16u3_aesm i hhm)
    (Eventually.of_forall fun x => sa16u3_enorm_le hθ0.le hδ.1 i _ x)
  calc eLpNorm (spliceOdd d θ δ i (fun y => a y * W y)) (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal CH * eLpNorm (fun y => a y * W y) (ENNReal.ofReal q) volume := h2
    _ ≤ ENNReal.ofReal CH * (eLpNorm a (ENNReal.ofReal ((d : ℝ) / (1 - θ))) volume *
          eLpNorm W (ENNReal.ofReal p) volume) := by gcongr
    _ = _ := by ring

end HRS.Whole.AppendixA.Phase2SA16Cutoff
