import HRS.MS.ProClosureS111CoeffL2

/-!
From actual sectional second-moment bounds to a jointly measurable Hilbert
coefficient field on a finite time slab. The product L2 membership is
proved by Fubini, rather than postulated for the chosen scalar versions.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.ProClosureS111

variable {Time Omega : Type*} [MeasurableSpace Time] [MeasurableSpace Omega]

theorem scalar_memLp_prod_of_section_bound (dt : Measure Time) [IsFiniteMeasure dt]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (f : Time × Omega → ℝ) (hf : Measurable f) (B : ℝ)
    (hsec : ∀ᵐ t ∂dt, MemLp (fun w => f (t,w)) 2 P ∧ (∫ w, f (t,w)^2 ∂P) ≤ B) :
    MemLp f 2 (dt.prod P) ∧
      (∫ p, f p^2 ∂dt.prod P) ≤ (dt univ).toReal * B := by
  have hm : AEStronglyMeasurable (fun p => f p^2) (dt.prod P) :=
    (hf.pow_const 2).aestronglyMeasurable
  have hnorm : Integrable (fun t => ∫ w, ‖f (t,w)^2‖ ∂P) dt := by
    refine (integrable_const B).mono' hm.norm.integral_prod_right' ?_
    filter_upwards [hsec] with t ht
    have he : (∫ w, ‖f (t,w)^2‖ ∂P) = ∫ w, f (t,w)^2 ∂P :=
      integral_congr_ae (ae_of_all P fun w => Real.norm_of_nonneg (sq_nonneg (f (t,w))))
    have hn : (0 : ℝ) ≤ ∫ w, f (t,w)^2 ∂P :=
      integral_nonneg fun w => sq_nonneg (f (t,w))
    rw [he, Real.norm_of_nonneg hn]
    exact ht.2
  have hi : Integrable (fun p => f p^2) (dt.prod P) :=
    (integrable_prod_iff hm).2 ⟨hsec.mono (fun t ht => ht.1.integrable_sq), hnorm⟩
  refine ⟨(memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hi, ?_⟩
  calc
    _ = ∫ t, ∫ w, f (t,w)^2 ∂P ∂dt := integral_prod _ hi
    _ ≤ ∫ t, B ∂dt := integral_mono_ae hi.integral_prod_left
      (integrable_const B) (hsec.mono (fun _ ht => ht.2))
    _ = (dt univ).toReal * B := by rw [integral_const]; simp [Measure.real]

variable [MeasurableSpace NatCoeffL2] [BorelSpace NatCoeffL2]

/-- A quantitative joint coefficient field, with all product membership
and representative choices produced from scalar sectional bounds. -/
theorem joint_coeff_field_from_section_bounds
    (dt : Measure Time) [IsFiniteMeasure dt]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (f : ℕ → Time × Omega → ℝ) (hf : ∀ j, Measurable (f j))
    (b : ℕ → ℝ) (hb0 : ∀ j, 0 ≤ b j) (hb : Summable b)
    (hsec : ∀ j, ∀ᵐ t ∂dt,
      MemLp (fun w => f j (t,w)) 2 P ∧ (∫ w, f j (t,w)^2 ∂P) ≤ b j) :
    ∃ q : Time × Omega → NatCoeffL2, Measurable q ∧ MemLp q 2 (dt.prod P) ∧
      (∀ᵐ p ∂dt.prod P, ∀ j, q p j = f j p) ∧
      (∫ p, ‖q p‖^2 ∂dt.prod P) ≤ (dt univ).toReal * ∑' j, b j := by
  have hprod := fun j => scalar_memLp_prod_of_section_bound dt P (f j) (hf j) (b j) (hsec j)
  have hS : Summable (fun j => ∫ p, f j p^2 ∂dt.prod P) :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => sq_nonneg _)
      (fun j => (hprod j).2) (hb.mul_left _)
  obtain ⟨q, hqm, hq2, hcoord, hnorm⟩ := exists_joint_coeffL2 (dt.prod P) f
    (fun j => (hprod j).1) hS
  refine ⟨q, hqm, hq2, hcoord, ?_⟩
  rw [hnorm, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun j => (hprod j).2) hS (hb.mul_left _)

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.scalar_memLp_prod_of_section_bound
#print axioms HRS.MS.ProClosureS111.joint_coeff_field_from_section_bounds
