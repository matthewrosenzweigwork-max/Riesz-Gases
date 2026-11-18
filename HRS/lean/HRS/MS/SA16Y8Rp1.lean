import HRS.MS.SA16Y8Hd1
import HRS.MS.SA16RExt3

/-!
# S.A.16 (SA16Y8) Rp1: sup and Hölder bounds of `D^jφ`, `j ≤ 2`, by `‖Jcc φ‖` (classical clause, K3, part 1)

`sa16y8_bounds`: for `m > 2 + d/p` there are `C, α > 0` such that for `φ ∈ C_c^∞` (`ccSub`):
`‖φ x‖, ‖fderiv φ x‖, ‖D2 φ x‖ ≤ C‖Jcc φ‖` and `‖D2 φ (x+h) - D2 φ x‖ ≤ C ‖h‖^α ‖Jcc φ‖` for `‖h‖ ≤ 1`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16 HRS.Whole.AppendixA.Phase2SA16R
open Phase2SA16Transfer Phase2SA16Evolution

section Rp1
variable {d : ℕ}

lemma sa16y8_wNormE_cc (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (φ : ccSub d) :
    wNormE m p φ.1 = ENNReal.ofReal ‖sa16r_Jcc d m p φ‖ := by
  refine wNormE_eq_lift_norm d m p (sa16r_Jcc d m p φ) φ.1 ?_
  rw [sa16r_Jcc_eq]
  exact sa16r_cc_elt_wrep φ.2 m

theorem sa16y8_bounds (d m : ℕ) (hd : 1 ≤ d) (p : ℝ) [Fact (2 ≤ p)] (hmp : 2 + (d : ℝ) / p < m) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ φ : ccSub d,
      (∀ x, ‖φ.1 x‖ ≤ C * ‖sa16r_Jcc d m p φ‖) ∧ (∀ x, ‖fderiv ℝ φ.1 x‖ ≤ C * ‖sa16r_Jcc d m p φ‖) ∧
      (∀ x, ‖sa16y8_D2 φ.1 x‖ ≤ C * ‖sa16r_Jcc d m p φ‖) ∧
      ∀ x h : Euc d, ‖h‖ ≤ 1 → ‖sa16y8_D2 φ.1 (x + h) - sa16y8_D2 φ.1 x‖ ≤ C * ‖h‖ ^ α * ‖sa16r_Jcc d m p φ‖ := by
  obtain ⟨C1, hC1, hcb⟩ := compact_cb2_bound d m hd p hmp
  obtain ⟨C2, α, hC2, hα, hH⟩ := sa16y8_holder_cc d m hd p hmp
  refine ⟨max C1 C2, α, lt_max_of_lt_left hC1, hα, fun φ => ?_⟩
  have hJ0 : 0 ≤ ‖sa16r_Jcc d m p φ‖ := norm_nonneg _
  have hw : wNormE m p φ.1 = ENNReal.ofReal ‖sa16r_Jcc d m p φ‖ := sa16y8_wNormE_cc m p φ
  obtain ⟨hmem, hnorm⟩ := hcb φ.1 φ.2
  rw [hw, ← ENNReal.ofReal_mul hC1.le] at hnorm
  have hcb' : cbNorm 2 φ.1 ≤ C1 * ‖sa16r_Jcc d m p φ‖ :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hnorm
  have hsup : ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j φ.1 x‖ ≤ cbNorm 2 φ.1 := by
    intro j hj x
    unfold cbNorm
    have hb : ∀ i ∈ Finset.range 3, 0 ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ i φ.1 z‖ := fun i _ =>
      Real.iSup_nonneg fun _ => norm_nonneg _
    have hjm : j ∈ Finset.range 3 := Finset.mem_range.2 (by omega)
    calc ‖iteratedFDeriv ℝ j φ.1 x‖ ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ j φ.1 z‖ :=
          le_ciSup (hmem.2 j hj) x
      _ ≤ ∑ i ∈ Finset.range 3, ⨆ z : Euc d, ‖iteratedFDeriv ℝ i φ.1 z‖ :=
          Finset.single_le_sum hb hjm
  have hmax1 : C1 ≤ max C1 C2 := le_max_left _ _
  have hmax2 : C2 ≤ max C1 C2 := le_max_right _ _
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x h hh => ?_⟩
  · have := hsup 0 (by omega) x
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (hcb'.trans (mul_le_mul_of_nonneg_right hmax1 hJ0))
  · have := hsup 1 (by omega) x
    rw [norm_iteratedFDeriv_one] at this
    exact this.trans (hcb'.trans (mul_le_mul_of_nonneg_right hmax1 hJ0))
  · have := hsup 2 (by omega) x
    have e : ‖iteratedFDeriv ℝ 2 φ.1 x‖ = ‖sa16y8_D2 φ.1 x‖ := by
      have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := φ.1) (n := 1) (x := x)
      rw [norm_iteratedFDeriv_one] at h1
      exact h1.symm
    rw [e] at this
    exact this.trans (hcb'.trans (mul_le_mul_of_nonneg_right hmax1 hJ0))
  · have hh2 := hH φ.1 φ.2 x h hh
    rw [hw, ENNReal.toReal_ofReal hJ0] at hh2
    refine hh2.trans ?_
    have hρ : 0 ≤ ‖h‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
    calc C2 * ‖h‖ ^ α * ‖sa16r_Jcc d m p φ‖ ≤ max C1 C2 * ‖h‖ ^ α * ‖sa16r_Jcc d m p φ‖ := by
          gcongr
      _ = _ := by ring

end Rp1

end HRS.Whole.AppendixA.Phase2SA16Q
