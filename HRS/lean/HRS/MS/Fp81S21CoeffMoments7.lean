import HRS.MS.Fp81S21CoeffMoments6
import HRS.MS.Fp81S21EmbedIdent

/-! Identify the embedded new coefficient choices with existing physical-chart representatives. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- A newly constructed strong-chart representative and an existing physical
`MomentRep` for the same field agree almost everywhere at each fixed
nonnegative time after embedding. This is the C2 identification used for
consumers that already chose a physical-chart representative. -/
theorem fp81s21_coeffMoments_embedField_eq_existing
    {d q : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (P : Measure Ω)
    (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (qs qsExisting : ℝ → Ω → r26t6_Coeff)
    (M2 M2Existing M6 : ℝ)
    (hNew : fp81s21_MomentRep Es P Q qs M2 ∧
      fp81s21_Six P qs M6)
    (hExisting : fp81s21_MomentRep E P Q qsExisting M2Existing) :
    ∀ u, 0 ≤ u →
      (fun ω => fp81s21_embedField hP hPs Es E (qs u ω)) =ᵐ[P]
        (fun ω => qsExisting u ω) := by
  exact fp81s21_embedField_eq_MomentRep hP hPs Es E P Q qs qsExisting
    M2 M2Existing hNew.1 hExisting

#print axioms HRS.Fp81.S21.fp81s21_coeffMoments_embedField_eq_existing

end HRS.Fp81.S21

end
