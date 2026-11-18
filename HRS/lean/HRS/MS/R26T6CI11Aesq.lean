import HRS.MS.R26T6CI11ProdLp
import HRS.MS.R26T6CI09Summable

/-!
# I11: Tonelli square-summability for arbitrary σ-finite measures.

No probability normalization is required. The conclusion is exact a.e.
summability of coordinate squares, hence an ℓ²-valued random variable.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole

theorem r26t6c_square_ae_of_integrated_sum
    {Omega iota : Type*} [MeasurableSpace Omega]
    [Countable iota] (P : Measure Omega) [SFinite P]
    (f : iota → Omega → ℝ)
    (h2 : ∀ i, MemLp (f i) 2 P)
    (hS : Summable (fun i => ∫ w, (f i w) ^ 2 ∂P)) :
    ∀ᵐ w ∂P, Summable (fun i => f i w ^ 2) := by
  have hm : ∀ i, AEMeasurable
      (fun w => ENNReal.ofReal (f i w ^ 2)) P := by
    intro i
    have hmeas : AEStronglyMeasurable (fun w => f i w ^ 2) P := by
      have hEq : (fun w => f i w ^ 2) = (f i) * (f i) := by
        funext w
        simp [Pi.mul_apply, pow_two]
      rw [hEq]
      exact (h2 i).aestronglyMeasurable.mul (h2 i).aestronglyMeasurable
    exact hmeas.aemeasurable.ennreal_ofReal
  have hlin : (∫⁻ w, ∑' i, ENNReal.ofReal (f i w ^ 2) ∂P) =
      ENNReal.ofReal (∑' i, ∫ w, f i w ^ 2 ∂P) := by
    rw [lintegral_tsum hm]
    have hi : ∀ i, (∫⁻ w, ENNReal.ofReal (f i w ^ 2) ∂P) =
        ENNReal.ofReal (∫ w, f i w ^ 2 ∂P) := by
      intro i
      exact (ofReal_integral_eq_lintegral_ofReal (h2 i).integrable_sq
        (ae_of_all _ fun _ => sq_nonneg _)).symm
    simp_rw [hi]
    exact (ENNReal.ofReal_tsum_of_nonneg
      (fun i => integral_nonneg fun _ => sq_nonneg _) hS).symm
  have hfinite : (∫⁻ w, ∑' i, ENNReal.ofReal (f i w ^ 2) ∂P) < ∞ := by
    rw [hlin]
    exact ENNReal.ofReal_lt_top
  have hmeas : AEMeasurable
      (fun w => ∑' i, ENNReal.ofReal (f i w ^ 2)) P :=
    AEMeasurable.ennreal_tsum hm
  have haefinite := ae_lt_top' hmeas hfinite.ne
  filter_upwards [haefinite] with w hw
  simpa [ENNReal.toReal_ofReal (sq_nonneg _)] using
    (ENNReal.summable_toReal hw.ne)

end HRS.MS.R26T6C
