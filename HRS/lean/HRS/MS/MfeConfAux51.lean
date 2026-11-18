import HRS.MS.MfeConfAux50
import HRS.MP.SelfSimP4Jensen
import HRS.MP.SelfSimP4MolLsc

/-!
# S.B.1, packet F6 (part 13): relative entropy of a density against a density reference

`sb1Dm ρ = ρ dx`.  `sb1_klDiv_density`: for probability densities `ρ`, `q > 0` with `ρ (log ρ - log q)` integrable,
`klDiv (ρ dx) (q dx) ≠ ⊤` and `(klDiv (ρ dx) (q dx)).toReal = ∫ ρ (log ρ - log q)` (the transplant of
`p4m_klDiv_density` from Gaussian-majorised Gibbs weights to an arbitrary positive probability density).
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- The measure `ρ dx`. -/
def sb1Dm (ρ : EucConfig d N → ℝ) : Measure (EucConfig d N) :=
  (volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (ρ x))

theorem sb1Dm_prob {ρ : EucConfig d N → ℝ} (h : ∫⁻ x, ENNReal.ofReal (ρ x) = 1) :
    IsProbabilityMeasure (sb1Dm ρ) :=
  ⟨by rw [sb1Dm, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact h⟩

theorem sb1_Dm_ac {ρ q : EucConfig d N → ℝ} (hρ : Measurable ρ) (hq : Measurable q) (hq0 : ∀ x, 0 < q x) :
    sb1Dm ρ = (sb1Dm q).withDensity (fun x => ENNReal.ofReal (ρ x) * (ENNReal.ofReal (q x))⁻¹) := by
  have hqm := hq.ennreal_ofReal
  have hρm := hρ.ennreal_ofReal
  unfold sb1Dm
  have key : ((volume : Measure (EucConfig d N)).withDensity (fun x => ENNReal.ofReal (q x))).withDensity
      (fun x => ENNReal.ofReal (ρ x) * (ENNReal.ofReal (q x))⁻¹) =
      (volume : Measure (EucConfig d N)).withDensity
        (fun x => ENNReal.ofReal (q x) * (ENNReal.ofReal (ρ x) * (ENNReal.ofReal (q x))⁻¹)) :=
    (withDensity_mul _ hqm (hρm.mul hqm.inv)).symm
  rw [key]
  congr 1
  funext x
  have h1 : ENNReal.ofReal (q x) ≠ 0 := (ENNReal.ofReal_pos.2 (hq0 x)).ne'
  have h2 : ENNReal.ofReal (q x) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ENNReal.ofReal (ρ x) = ENNReal.ofReal (ρ x) * (ENNReal.ofReal (q x) * (ENNReal.ofReal (q x))⁻¹) := by
        rw [ENNReal.mul_inv_cancel h1 h2, mul_one]
    _ = _ := by ring

theorem sb1_llr_density {ρ q : EucConfig d N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hq : Measurable q)
    (hq0 : ∀ x, 0 < q x) (hqp : IsProbabilityMeasure (sb1Dm q)) :
    ∀ᵐ x ∂(sb1Dm ρ), llr (sb1Dm ρ) (sb1Dm q) x = Real.log (ρ x) - Real.log (q x) := by
  have hac : sb1Dm ρ ≪ sb1Dm q := by
    rw [sb1_Dm_ac hρ hq hq0]
    exact withDensity_absolutelyContinuous _ _
  have hrn0 := Measure.rnDeriv_withDensity (sb1Dm q)
    (f := fun x => ENNReal.ofReal (ρ x) * (ENNReal.ofReal (q x))⁻¹)
    (hρ.ennreal_ofReal.mul hq.ennreal_ofReal.inv)
  rw [← sb1_Dm_ac hρ hq hq0] at hrn0
  have hrn' := hac.ae_le hrn0
  have hpos : ∀ᵐ x ∂(sb1Dm ρ), 0 < ρ x := by
    unfold sb1Dm
    rw [ae_withDensity_iff (f := fun x => ENNReal.ofReal (ρ x)) hρ.ennreal_ofReal]
    refine Eventually.of_forall fun x hx => ?_
    rcases (hρ0 x).lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [← h]; simp) hx
  filter_upwards [hrn', hpos] with x hx hpx
  unfold llr
  rw [hx]
  have e1 : (ENNReal.ofReal (ρ x) * (ENNReal.ofReal (q x))⁻¹).toReal = ρ x * (q x)⁻¹ := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (hρ0 x),
      ENNReal.toReal_ofReal (hq0 x).le]
  rw [e1, Real.log_mul hpx.ne' (inv_pos.2 (hq0 x)).ne', Real.log_inv]
  ring

theorem sb1_klDiv_density {ρ q : EucConfig d N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫⁻ x, ENNReal.ofReal (ρ x) = 1) (hq : Measurable q) (hq0 : ∀ x, 0 < q x)
    (hq1 : ∫⁻ x, ENNReal.ofReal (q x) = 1)
    (hΦ : Integrable (fun x => ρ x * (Real.log (ρ x) - Real.log (q x)))) :
    klDiv (sb1Dm ρ) (sb1Dm q) ≠ ⊤ ∧
      (klDiv (sb1Dm ρ) (sb1Dm q)).toReal = ∫ x, ρ x * (Real.log (ρ x) - Real.log (q x)) := by
  haveI := sb1Dm_prob hρ1
  haveI := sb1Dm_prob hq1
  have hac : sb1Dm ρ ≪ sb1Dm q := by
    rw [sb1_Dm_ac hρ hq hq0]
    exact withDensity_absolutelyContinuous _ _
  have hllr := sb1_llr_density hρ hρ0 hq hq0 inferInstance
  have hint : Integrable (llr (sb1Dm ρ) (sb1Dm q)) (sb1Dm ρ) := by
    have : Integrable (fun x => Real.log (ρ x) - Real.log (q x)) (sb1Dm ρ) :=
      (p4j_integrable_dMeas_iff hρ hρ0 _).2 hΦ
    exact this.congr (by filter_upwards [hllr] with x hx using hx.symm)
  refine ⟨?_, ?_⟩
  · rw [klDiv_of_ac_of_integrable hac hint]; exact ENNReal.ofReal_ne_top
  · rw [toReal_klDiv hac hint]
    simp only [probReal_univ, add_sub_cancel_right]
    rw [integral_congr_ae hllr]
    exact p4j_integral_dMeas hρ hρ0 _

end HRS.MS.MfeConf
