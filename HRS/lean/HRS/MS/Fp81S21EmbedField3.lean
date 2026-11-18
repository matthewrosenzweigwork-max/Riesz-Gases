import HRS.MS.Fp81S21EmbedField2
import HRS.MS.ProClosureS111WeightedCompletion

/-! Linear encodings of the common compact smooth test core. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111
  HRS.MS.FixEq

/-- Encode compact smooth tests in the stronger chart. -/
def fp81s21_embedField_strongTestEncode
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d (q + 2) Pw) :
    compactSmoothSubmodule d →ₗ[ℝ] r26t6_Coeff where
  toFun f := E.encode f
  map_add' f g := by
    apply E.add
    · exact weightedTestSubmodule_iff.1
        (weighted_test_of_compact_smooth (r := q + 2) (Pw := Pw) hP f.property)
    · exact weightedTestSubmodule_iff.1
        (weighted_test_of_compact_smooth (r := q + 2) (Pw := Pw) hP g.property)
  map_smul' c f := by
    apply E.smul
    exact weightedTestSubmodule_iff.1
      (weighted_test_of_compact_smooth (r := q + 2) (Pw := Pw) hP f.property)

/-- Encode the same compact smooth tests in the weaker chart. -/
def fp81s21_embedField_weakTestEncode
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q (Pw + 2)) :
    compactSmoothSubmodule d →ₗ[ℝ] r26t6_Coeff where
  toFun f := Es.encode f
  map_add' f g := by
    apply Es.add
    · exact weightedTestSubmodule_iff.1
        (weighted_test_of_compact_smooth (r := q) (Pw := Pw + 2) hP f.property)
    · exact weightedTestSubmodule_iff.1
        (weighted_test_of_compact_smooth (r := q) (Pw := Pw + 2) hP g.property)
  map_smul' c f := by
    apply Es.smul
    exact weightedTestSubmodule_iff.1
      (weighted_test_of_compact_smooth (r := q) (Pw := Pw + 2) hP f.property)

/-- The strong chart encoding separates compact smooth tests. -/
theorem fp81s21_embedField_strongTestEncode_injective
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d (q + 2) Pw) :
    Function.Injective (fp81s21_embedField_strongTestEncode hP E) := by
  intro f g hfg
  have hmap : fp81s21_embedField_strongTestEncode hP E (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hencode : E.encode ((f - g : compactSmoothSubmodule d) : Euc d → ℝ) = 0 := by
    simpa [fp81s21_embedField_strongTestEncode] using hmap
  have hwt : IsR2WeightedTest (q + 2) Pw
      ((f - g : compactSmoothSubmodule d) : Euc d → ℝ) :=
    weightedTestSubmodule_iff.1
      (weighted_test_of_compact_smooth (r := q + 2) (Pw := Pw) hP (f - g).property)
  have hreal : (weightedSobolevE (q + 2) Pw
      ((f - g : compactSmoothSubmodule d) : Euc d → ℝ)).toReal = 0 := by
    have hnorm := E.norm ((f - g : compactSmoothSubmodule d) : Euc d → ℝ) hwt
    rw [hencode] at hnorm
    simpa using hnorm.symm
  have hzero : weightedSobolevE (q + 2) Pw
      ((f - g : compactSmoothSubmodule d) : Euc d → ℝ) = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1 hreal with hz | hz
    · exact hz
    · exact (hwt.2.ne hz).elim
  have horder : (q : WithTop ℕ∞) + 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.2 (le_top : ((q + 2 : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞))
  have hreg : ContDiff ℝ (q + 2)
      ((f - g : compactSmoothSubmodule d) : Euc d → ℝ) :=
    (f - g).property.1.of_le horder
  have hfun := s57p_E_zero (r := q + 2) (P := Pw) hreg hzero
  apply Subtype.ext
  exact sub_eq_zero.1 hfun

#print axioms HRS.Fp81.S21.fp81s21_embedField_strongTestEncode_injective

end HRS.Fp81.S21
