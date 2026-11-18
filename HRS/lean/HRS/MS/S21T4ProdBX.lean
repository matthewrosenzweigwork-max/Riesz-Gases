import HRS.MS.S21T4ProdBW
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# S13: lower semicontinuity of the second moment under weak convergence

This works with varying probability spaces. In particular, the particle
configurations for each particle number need not live on a common space.
The integrability hypotheses prevent the zero-valued Bochner integral
of a nonintegrable function from being mistaken for a moment bound.
-/
set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T3

theorem s21t4_weak_limit_second_moment
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (ν : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (ν n)]
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : Measure Ω') [IsProbabilityMeasure P]
    (Y : (n : ℕ) → Ω n → ℝ) (Z : Ω' → ℝ)
    (hweak : TendstoInDistribution Y atTop Z ν P)
    (C : ℝ) (hC : 0 ≤ C)
    (hYi : ∀ᶠ n in atTop, Integrable (fun ω => (Y n ω) ^ 2) (ν n))
    (hYb : ∀ᶠ n in atTop, (∫ ω, (Y n ω) ^ 2 ∂(ν n)) ≤ C)
    (hZi : Integrable (fun ω => (Z ω) ^ 2) P) :
    (∫ ω, (Z ω) ^ 2 ∂P) ≤ C := by
  have hOpen : ∀ G : Set ℝ, IsOpen G →
      (P.map Z) G ≤ atTop.liminf (fun n => (ν n).map (Y n) G) := by
    intro G hG
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak.tendsto hG
  have hport : (∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂(P.map Z)) ≤
      atTop.liminf (fun n => ∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂((ν n).map (Y n))) :=
    lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
      (f := fun x : ℝ => x ^ 2) (by fun_prop) (fun x => sq_nonneg x) hOpen
  have hport' : (∫⁻ ω, ENNReal.ofReal ((Z ω) ^ 2) ∂P) ≤
      atTop.liminf (fun n => ∫⁻ ω, ENNReal.ofReal ((Y n ω) ^ 2) ∂(ν n)) := by
    have hAf (ν' : Measure ℝ) : AEMeasurable
        (fun x : ℝ => ENNReal.ofReal (x ^ 2)) ν' := by fun_prop
    rw [lintegral_map' (hAf _) hweak.aemeasurable_limit] at hport
    simp_rw [lintegral_map' (hAf _) (hweak.forall_aemeasurable _)] at hport
    exact hport
  have hBound : ∀ᶠ n in atTop,
      (∫⁻ ω, ENNReal.ofReal ((Y n ω) ^ 2) ∂(ν n)) ≤ ENNReal.ofReal C := by
    filter_upwards [hYi, hYb] with n hi hb
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall fun ω => sq_nonneg (Y n ω))]
    exact ENNReal.ofReal_le_ofReal hb
  have hliminf : atTop.liminf
      (fun n => ∫⁻ ω, ENNReal.ofReal ((Y n ω) ^ 2) ∂(ν n)) ≤
      ENNReal.ofReal C := by
    calc
      _ ≤ atTop.liminf (fun _ : ℕ => ENNReal.ofReal C) :=
        Filter.liminf_le_liminf hBound
      _ = _ := Filter.liminf_const _
  have hEN : ENNReal.ofReal (∫ ω, (Z ω) ^ 2 ∂P) ≤ ENNReal.ofReal C := by
    rw [ofReal_integral_eq_lintegral_ofReal hZi
      (Eventually.of_forall fun ω => sq_nonneg (Z ω))]
    exact hport'.trans hliminf
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hEN

end HRS.MS.R26T3
