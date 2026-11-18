import HRS.MS.Fp81S21RealizeAll2
import HRS.MS.Fp81S21RealizePatch3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set

namespace HRS.Fp81.S21

open HRS.Whole

/-- Glue the local continuous modifications on their rational overlaps to get
one jointly measurable, every-sample continuous process on the same space. -/
theorem fp81s21_realize_patched_process
    {d : ℕ} {m : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℝ → Ω → OscDual d m)
    (Y : ∀ n : ℕ, Ω → OscPath d m ((n : ℝ) + 1))
    (hYmeas : ∀ n, Measurable (Y n))
    (hmod : ∀ (n : ℕ) (t : ℝ)
      (ht : t ∈ Icc (0 : ℝ) ((n : ℝ) + 1)),
      (fun ω => OscPath.at' (Y n ω) ⟨t, ht⟩) =ᵐ[P] X t) :
    ∃ Z : ℝ → Ω → OscDual d m,
      Measurable (Function.uncurry Z) ∧
      (∀ ω, Continuous (fun t => Z t ω)) ∧
      ∀ t, 0 ≤ t → Z t =ᵐ[P] X t :=
  fp81s21_patch_nat_modifications X Y hYmeas hmod

#print axioms fp81s21_realize_patched_process

end HRS.Fp81.S21

end
