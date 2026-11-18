import HRS.MC.CepH3B3
import HRS.Appendix.B15BAux1

/-!
# Packet CEPH3, part C1: the normalised relative entropy `F(ν, m) = H(ν | m/|m|) - log |m|`

For a probability measure `ν` and a finite nonzero measure `m`:
`F(ν,m) = ∫ log (dν/dm) dν` if `ν ≪ m` and the integrand is `ν`-integrable, and `+∞` otherwise.
-/

open MeasureTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH3

open HRS

variable {α : Type*} [MeasurableSpace α]

/-- `F(ν,m) = H(ν | |m|⁻¹ m) - log |m|`, the shape of `gibbsEntropy` and `cep_cylEntropy`. -/
def h3c_F (ν m : Measure α) : EReal :=
  ((klDiv ν ((m univ)⁻¹ • m) : ℝ≥0∞) : EReal) - ((Real.log (m univ).toReal : ℝ) : EReal)

/-- The integral form of `F`. -/
def h3c_Fu (ν m : Measure α) : EReal :=
  open Classical in
  if ν ≪ m ∧ Integrable (llr ν m) ν then ((∫ x, llr ν m x ∂ν : ℝ) : EReal) else ⊤

lemma h3c_normalised_isProb (m : Measure α) [IsFiniteMeasure m] (h0 : m univ ≠ 0) :
    IsProbabilityMeasure ((m univ)⁻¹ • m) :=
  ⟨by simp [ENNReal.inv_mul_cancel h0 (measure_ne_top m _)]⟩

lemma h3c_ac_smul_iff (ν m : Measure α) {c : ℝ≥0∞} (h0 : c ≠ 0) (htop : c ≠ ⊤) :
    ν ≪ c • m ↔ ν ≪ m := by
  refine ⟨fun h => ?_, fun h => h.smul_right h0⟩
  have := h.smul_right (ENNReal.inv_ne_zero.mpr htop)
  rwa [smul_smul, ENNReal.inv_mul_cancel h0 htop, one_smul] at this

theorem h3c_F_eq (ν m : Measure α) [IsProbabilityMeasure ν] [IsFiniteMeasure m] (h0 : m univ ≠ 0) :
    h3c_F ν m = h3c_Fu ν m := by
  classical
  set c : ℝ≥0∞ := m univ with hc
  have hctop : c ≠ ⊤ := measure_ne_top m _
  have hcinv0 : c⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hctop
  have hcinvtop : c⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr h0
  have : IsProbabilityMeasure (c⁻¹ • m) := h3c_normalised_isProb m h0
  have hac : ν ≪ c⁻¹ • m ↔ ν ≪ m := h3c_ac_smul_iff ν m hcinv0 hcinvtop
  by_cases hA : ν ≪ m
  · have hA' : ν ≪ c⁻¹ • m := hac.mpr hA
    have hllr := llr_smul_right hA c⁻¹ hcinv0 hcinvtop
    have hlog : Real.log (c⁻¹).toReal = - Real.log c.toReal := by
      rw [ENNReal.toReal_inv, Real.log_inv]
    by_cases hI : Integrable (llr ν m) ν
    · have hI' : Integrable (llr ν (c⁻¹ • m)) ν := by
        refine (integrable_congr ?_).mpr (hI.sub (integrable_const (Real.log (c⁻¹).toReal)))
        exact hllr
      have hnn := integral_llr_add_sub_measure_univ_nonneg hA' hI'
      have e1 : klDiv ν (c⁻¹ • m) = ENNReal.ofReal (∫ x, llr ν (c⁻¹ • m) x ∂ν) := by
        rw [klDiv_of_ac_of_integrable hA' hI']
        simp [measureReal_def]
      have e2 : ∫ x, llr ν (c⁻¹ • m) x ∂ν = ∫ x, llr ν m x ∂ν + Real.log c.toReal := by
        rw [integral_congr_ae hllr, integral_sub hI (integrable_const _)]
        simp [hlog]
      unfold h3c_F h3c_Fu
      rw [if_pos ⟨hA, hI⟩, e1, EReal.coe_ennreal_ofReal]
      have hnn' : 0 ≤ ∫ x, llr ν (c⁻¹ • m) x ∂ν := by
        simpa [measureReal_def] using hnn
      rw [max_eq_left hnn', e2]
      norm_cast
      rw [← hc]; ring
    · have hI' : ¬ Integrable (llr ν (c⁻¹ • m)) ν := by
        intro h
        apply hI
        have := h.sub (integrable_const (Real.log c.toReal))
        refine (integrable_congr ?_).mp this
        filter_upwards [hllr] with x hx
        simp only [Pi.sub_apply, hx, hlog]; ring
      unfold h3c_F h3c_Fu
      rw [if_neg (fun h => hI h.2), klDiv_of_not_integrable hI']
      simp
  · have hA' : ¬ ν ≪ c⁻¹ • m := fun h => hA (hac.mp h)
    unfold h3c_F h3c_Fu
    rw [if_neg (fun h => hA h.1), klDiv_of_not_ac hA']
    simp

end HRS.MC.CepH3
