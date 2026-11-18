import HRS.MS.Fp81S21HilbertMart2
import HRS.Prob.MRepAux3

/-!
# HRS S2.1(iii), B6-i: a progressive Hilbert--Schmidt integral estimate

A finite-coordinate progressive integrand with a uniform expected trace bound
on a nonnegative time interval has the required finite integrated
Hilbert--Schmidt norm.  The proof makes the time/probability Tonelli exchange
explicit.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace BigOperators

namespace HRS.Fp81.S21

/-- Tonelli's estimate for the finite-coordinate Hilbert--Schmidt norm. -/
theorem fp81s21_hsSqIntegralOn_le_of_uniform_moment
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ}
    {H : Type*} [NormedAddCommGroup H]
      [TopologicalSpace.PseudoMetrizableSpace H] [MeasurableSpace H] [BorelSpace H]
      [OpensMeasurableSpace H]
    {κ : Type*} [Fintype κ]
    (Z : ℝ → Ω → κ → H) (T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hp : ∀ k, IsProgressive ℱ (fun u ω => Z u ω k))
    (hsec : ∀ u ∈ Set.Icc 0 T,
      Integrable (fun ω => ∑ k, ‖Z u ω k‖ ^ 2) P ∧
        (∫ ω, ∑ k, ‖Z u ω k‖ ^ 2 ∂P) ≤ C) :
    hsSqIntegralOn P Z T ≤ ENNReal.ofReal (C * T) := by
  have hsum (u : ℝ) (ω : Ω) :
      (∑' k : κ, ‖Z u ω k‖ₑ ^ 2) =
        ENNReal.ofReal (∑ k : κ, ‖Z u ω k‖ ^ 2) := by
    calc
      (∑' k : κ, ‖Z u ω k‖ₑ ^ 2) =
          ∑ k : κ, ENNReal.ofReal (‖Z u ω k‖ ^ 2) := by
            rw [tsum_fintype]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ = ENNReal.ofReal (∑ k : κ, ‖Z u ω k‖ ^ 2) :=
            (ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _).symm
  have htraceMeas : Measurable (fun p : ℝ × Ω =>
      ∑ k : κ, ‖Z p.1 p.2 k‖ ^ 2) := by
    refine Finset.measurable_sum _ fun k _ => ?_
    exact (measurable_norm.comp
      (HRS.MRep.isProgressive_measurable_uncurry (hp k))).pow_const 2
  have hswapMeas : AEMeasurable
      (fun p : Ω × ℝ => ENNReal.ofReal (∑ k : κ, ‖Z p.2 p.1 k‖ ^ 2))
      (P.prod (volume.restrict (Set.Icc 0 T))) := by
    exact (ENNReal.measurable_ofReal.comp (htraceMeas.comp measurable_swap)).aemeasurable
  have hsection : ∀ u ∈ Set.Icc 0 T,
      (∫⁻ ω, ENNReal.ofReal (∑ k : κ, ‖Z u ω k‖ ^ 2) ∂P) ≤ ENNReal.ofReal C := by
    intro u hu
    rw [← ofReal_integral_eq_lintegral_ofReal (hsec u hu).1
      (ae_of_all P fun ω => Finset.sum_nonneg fun k _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hsec u hu).2
  unfold hsSqIntegralOn
  simp_rw [hsum]
  rw [lintegral_lintegral_swap (μ := P)
    (ν := volume.restrict (Set.Icc 0 T)) (f := fun ω u =>
      ENNReal.ofReal (∑ k : κ, ‖Z u ω k‖ ^ 2)) hswapMeas]
  calc
    (∫⁻ u in Set.Icc 0 T,
        ∫⁻ ω, ENNReal.ofReal (∑ k : κ, ‖Z u ω k‖ ^ 2) ∂P) ≤
        ∫⁻ u in Set.Icc 0 T, ENNReal.ofReal C :=
      setLIntegral_mono' measurableSet_Icc hsection
    _ = ENNReal.ofReal C * ENNReal.ofReal T := by
      rw [setLIntegral_const, Real.volume_Icc, sub_zero]
    _ = ENNReal.ofReal (C * T) := (ENNReal.ofReal_mul hC).symm

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_hsSqIntegralOn_le_of_uniform_moment
