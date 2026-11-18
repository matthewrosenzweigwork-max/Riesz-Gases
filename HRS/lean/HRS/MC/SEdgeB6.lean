import HRS.MC.SEdgeVocab
import HRS.MC.SEdgeB1
import HRS.MC.SEdgeB4b
import HRS.MC.SEdgeB5a

/-!
# Packet B6: mean bias (relocation of `sed_B6_mean_bias`)

B5a with `Psi = 1`, `dPsi = 0` gives `N (E mu_N(w) - mu(w)) = -beta E[N mE(h_v)]`, which is bounded by B4b.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B6

open HRS.Sec7
open HRS.MC.SEdge

variable {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
  {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
include hd hs0 hs hβ hρ

theorem sed_B6_mean_bias_proof {w : Torus d → ℝ} (hw : Torus.IsSmooth w) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∫ X, pair (empirical X) w ∂(sed_Q d s N β ρ) - pair (withDensityReal ρ) w| ≤ C / N := by
  obtain ⟨r, v, hr, hv, -, hresp, -, hdiv⟩ := HRS.MC.SEdge.B1.sed_B1_regular_proof hd hs0 hs hβ hρ hw
  obtain ⟨hint, C, hC⟩ := HRS.MC.SEdge.B4b.sed_B4b_energy_proof hd hs0 hs hβ hρ hv
  refine ⟨β * C, fun N hN => ?_⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  haveI hQ : IsProbabilityMeasure (sed_Q d s N β ρ) := B5a.b5a_Q_prob hd hs0 hs hβ hρ hN
  obtain ⟨hwm, Mw, hwb⟩ := B5a.b5a_w_facts hd hs0 hs hρ hr hresp
  have key := HRS.MC.SEdge.B5a.sed_B5a_stein_raw_proof hd hs0 hs hβ hρ hN hr hv hdiv hresp (hint N hN)
    (Ψ := fun _ => 1) (dΨ := fun _ _ _ => 0) measurable_const ⟨1, fun _ => by simp⟩
    (fun _ _ => measurable_const) ⟨0, fun _ _ _ => by simp⟩
    (fun i k Y _ => by simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ))
  simp only [one_mul, mul_zero, Finset.sum_const_zero, integral_zero] at key
  have hmeas : Measurable (fun X : Config d N => pair (empirical X) w) := by
    have : (fun X : Config d N => pair (empirical X) w) = fun X => (N : ℝ)⁻¹ * ∑ i, w (X i) :=
      funext fun X => pair_empirical (by omega) X w
    rw [this]
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hwm.comp (measurable_pi_apply i))
  have hI1 : Integrable (fun X : Config d N => pair (empirical X) w) (sed_Q d s N β ρ) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable Mw (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs]
    rw [pair_empirical (by omega) X w, abs_mul, abs_of_pos (inv_pos.2 hNp)]
    have h1 : |∑ i, w (X i)| ≤ N * Mw := by
      calc |∑ i, w (X i)| ≤ ∑ i, |w (X i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, Mw := Finset.sum_le_sum fun i _ => hwb _
        _ = N * Mw := by simp
    calc (N : ℝ)⁻¹ * |∑ i, w (X i)| ≤ (N : ℝ)⁻¹ * (N * Mw) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hNp.le)
      _ = Mw := by field_simp
  have hI2 : Integrable (fun X : Config d N =>
      (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)) (sed_Q d s N β ρ) :=
    (hint N hN).const_mul _
  have hsplit : ∫ X, ((N : ℝ) * (pair (empirical X) w - pair (withDensityReal ρ) w) +
        β * ((N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)))
      ∂(sed_Q d s N β ρ) =
      (N : ℝ) * (∫ X, pair (empirical X) w ∂(sed_Q d s N β ρ) - pair (withDensityReal ρ) w) +
        β * ∫ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)
          ∂(sed_Q d s N β ρ) := by
    have hA : Integrable (fun X : Config d N => (N : ℝ) *
        (pair (empirical X) w - pair (withDensityReal ρ) w)) (sed_Q d s N β ρ) :=
      (hI1.sub (integrable_const _)).const_mul _
    have hA2 : Integrable (fun X : Config d N => β * ((N : ℝ) *
        modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ))) (sed_Q d s N β ρ) :=
      hI2.const_mul _
    rw [integral_add hA hA2, integral_const_mul, integral_const_mul,
      integral_sub hI1 (integrable_const _)]
    simp
  rw [hsplit] at key
  have heq : ∫ X, pair (empirical X) w ∂(sed_Q d s N β ρ) - pair (withDensityReal ρ) w =
      -(β * ∫ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)
          ∂(sed_Q d s N β ρ)) / N := by
    field_simp
    linarith
  rw [heq, abs_div, abs_neg, abs_of_pos hNp, abs_mul, abs_of_nonneg hβ]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hC N hN).1 hβ) hNp.le

end HRS.MC.SEdge.B6

