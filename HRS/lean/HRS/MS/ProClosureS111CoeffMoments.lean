import HRS.MS.ProClosureS111CoeffL2

/-!
Exact second-moment trace and its domination bound for an existing
coefficient field. The result applies to any representatives with the
specified scalar L2 coordinates, including pointwise mass-normalized
versions of the physical fields.
-/
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.ProClosureS111

variable {Omega : Type*} [MeasurableSpace Omega]
variable [MeasurableSpace NatCoeffL2] [BorelSpace NatCoeffL2]

theorem coeff_second_moment_trace (P : Measure Omega) (q : Omega → NatCoeffL2)
    (hq : ∀ j, MemLp (fun w => q w j) 2 P)
    (hS : Summable (fun j => ∫ w, q w j ^ 2 ∂P)) :
    MemLp q 2 P ∧ (∫ w, ‖q w‖^2 ∂P) = ∑' j, ∫ w, q w j^2 ∂P := by
  obtain ⟨q', hq'm, hq'2, hcoord, hnorm⟩ := exists_joint_coeffL2 P (fun j w => q w j) hq hS
  have he : q' =ᵐ[P] q := by
    filter_upwards [hcoord] with w hw
    ext j
    exact hw j
  exact ⟨(memLp_congr_ae he).1 hq'2,
    (integral_congr_ae (he.symm.fun_comp (fun z : NatCoeffL2 => ‖z‖^2))).trans hnorm⟩

/-- A trace bound for arbitrary actual representatives; measurability of
the vector need not be added as a separate premise. -/
theorem coeff_second_moment_bound (P : Measure Omega) (q : Omega → NatCoeffL2)
    (hq : ∀ j, MemLp (fun w => q w j) 2 P)
    (b : ℕ → ℝ) (hb : Summable b)
    (hbound : ∀ j, (∫ w, q w j^2 ∂P) ≤ b j) :
    MemLp q 2 P ∧ (∫ w, ‖q w‖^2 ∂P) ≤ ∑' j, b j := by
  have hS : Summable (fun j => ∫ w, q w j^2 ∂P) :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => sq_nonneg _) hbound hb
  obtain ⟨hLp, he⟩ := coeff_second_moment_trace P q hq hS
  exact ⟨hLp, he.trans_le (Summable.tsum_le_tsum hbound hS hb)⟩

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.coeff_second_moment_trace
#print axioms HRS.MS.ProClosureS111.coeff_second_moment_bound
