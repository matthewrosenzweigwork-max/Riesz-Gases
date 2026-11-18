import HRS.MS.R26T6CI09Aux

/-!
# I09: almost-sure square-summability of countably many L3 coordinates

Uses Tonelli and the summability of integrated L2 energies, without
requiring pointwise coordinate bounds or altering exceptional sets.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole

theorem r26t6c_coordinate_square_ae
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    {iota : Type*} [Countable iota]
    (f : iota → Omega → ℝ) (b : iota → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hb : Summable (fun i => b i ^ 2))
    (hf : ∀ i, MemLp (f i) 3 P)
    (hfb : ∀ i, eLpNorm (f i) 3 P ≤ ENNReal.ofReal (b i)) :
    ∀ᵐ w ∂P, Summable (fun i => f i w ^ 2) := by
  have hS := r26t6c_coordinate_square_integral_summable P f b hb0 hb hf hfb
  have h2 : ∀ i, MemLp (f i) 2 P :=
    fun i => (hf i).mono_exponent (by norm_num)
  have hmeas : ∀ i, AEMeasurable
      (fun w => ENNReal.ofReal (f i w ^ 2)) P := by
    intro i
    have hm : AEStronglyMeasurable (fun w => f i w ^ 2) P := by
      have heq : (fun w => f i w ^ 2) = f i * f i := by
        funext w
        simp only [Pi.mul_apply, pow_two]
      rw [heq]
      exact (h2 i).aestronglyMeasurable.mul (h2 i).aestronglyMeasurable
    exact hm.aemeasurable.ennreal_ofReal
  have hlin : (∫⁻ w, ∑' i, ENNReal.ofReal (f i w ^ 2) ∂P) =
      ENNReal.ofReal (∑' i, ∫ w, f i w ^ 2 ∂P) := by
    rw [lintegral_tsum hmeas]
    have he : ∀ i, (∫⁻ w, ENNReal.ofReal (f i w ^ 2) ∂P) =
        ENNReal.ofReal (∫ w, f i w ^ 2 ∂P) := by
      intro i
      exact (ofReal_integral_eq_lintegral_ofReal (h2 i).integrable_sq
        (ae_of_all _ fun _ => sq_nonneg _)).symm
    simp_rw [he]
    exact (ENNReal.ofReal_tsum_of_nonneg
      (fun i => integral_nonneg fun _ => sq_nonneg _)
      hS.1).symm
  have hfin : (∫⁻ w, ∑' i, ENNReal.ofReal (f i w ^ 2) ∂P) < ∞ := by
    rw [hlin]
    exact ENNReal.ofReal_lt_top
  have hMeas : AEMeasurable
      (fun w => ∑' i, ENNReal.ofReal (f i w ^ 2)) P :=
    AEMeasurable.ennreal_tsum hmeas
  have haefin := ae_lt_top' hMeas hfin.ne
  filter_upwards [haefin] with w hw
  have ht := ENNReal.summable_toReal hw.ne
  simpa [ENNReal.toReal_ofReal (sq_nonneg _)] using ht

end HRS.MS.R26T6C
