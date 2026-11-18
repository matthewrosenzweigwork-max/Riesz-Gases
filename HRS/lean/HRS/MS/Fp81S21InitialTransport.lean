import HRS.MS.Fp81S21InitialWindow
import HRS.MS.Fp81S21InitGauss
import HRS.MS.S21G2_M16
import HRS.MS.S21F_I05
import HRS.MC.E213U6

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21E

/-- Pulling the zero-cutoff heat test back along the initial Gaussian
synthesis preserves `C^5`; its order-`j` derivative bound has the expected
`‖S‖^j` factor.  The pullback normalized by `1 + ‖S‖^5` belongs to the static
sequence-space unit ball. -/
theorem fp81s21_initial_heat_pullback
    {p : Parameters}
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d) H))
    (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ)
    (hΦ : Φ ∈ CbUnitBall (Window p) 5)
    [IsProbabilityMeasure (windowFuture future a ha 0)] :
    ContDiff ℝ 5
        (fun z : SeqL2 => initialHeat future a ha Φ 0
          (fp81s21_initGauss_synthesis p z)) ∧
      (∀ j ≤ 5, ∀ z,
        ‖iteratedFDeriv ℝ j
          (fun y : SeqL2 => initialHeat future a ha Φ 0
            (fp81s21_initGauss_synthesis p y)) z‖ ≤
          ‖fp81s21_initGauss_synthesis p‖ ^ j) ∧
      (fun z : SeqL2 =>
        (1 + ‖fp81s21_initGauss_synthesis p‖ ^ 5)⁻¹ *
          initialHeat future a ha Φ 0 (fp81s21_initGauss_synthesis p z))
        ∈ CbUnitBall SeqL2 5 := by
  let S : SeqL2 →L[ℝ] Window p := fp81s21_initGauss_synthesis p
  let H : Window p → ℝ := fun y => initialHeat future a ha Φ 0 y
  let F : SeqL2 → ℝ := fun z => H (S z)
  let A : ℝ := 1 + ‖S‖ ^ 5
  have hHeat := r26t3_heat_bounds
    (P := windowFuture future a ha 0) (Γ := id)
    (hΓ := aestronglyMeasurable_id) Φ hΦ
  have hHeatEq : r26t3_heat (windowFuture future a ha 0) id Φ = H := by
    funext y
    rfl
  have hH : H ∈ CbUnitBall (Window p) 5 := by
    exact hHeatEq ▸ hHeat.1
  have hHcd : ContDiff ℝ 5 H := hH.1
  have hFcd : ContDiff ℝ 5 F := hHcd.comp S.contDiff
  have hcomp : ∀ j ≤ 5, ∀ z,
      iteratedFDeriv ℝ j F z =
        (iteratedFDeriv ℝ j H (S z)).compContinuousLinearMap (fun _ => S) := by
    intro j hj z
    exact S.iteratedFDeriv_comp_right hHcd z (by exact_mod_cast hj)
  have hFbound : ∀ j ≤ 5, ∀ z,
      ‖iteratedFDeriv ℝ j F z‖ ≤ ‖S‖ ^ j := by
    intro j hj z
    rw [hcomp j hj z]
    calc
      ‖(iteratedFDeriv ℝ j H (S z)).compContinuousLinearMap (fun _ => S)‖ ≤
          ‖iteratedFDeriv ℝ j H (S z)‖ * ‖S‖ ^ j := by
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        simp [Finset.prod_const]
      _ ≤ 1 * ‖S‖ ^ j := by
        exact mul_le_mul_of_nonneg_right
          (HRS.MC.E213U6.u6_norm_iteratedFDeriv_le hH hj (S z)) (by positivity)
      _ = ‖S‖ ^ j := one_mul _
  have hApos : 0 < A := by dsimp [A]; positivity
  have hAj : ∀ j : ℕ, j ≤ 5 → ‖S‖ ^ j ≤ A := by
    intro j hj
    rcases le_total ‖S‖ 1 with h | h
    · have hp := pow_le_one₀ (norm_nonneg S) h (n := j)
      rw [show A = 1 + ‖S‖ ^ 5 from rfl]
      have hp5 : 0 ≤ ‖S‖ ^ 5 := by positivity
      linarith
    · have hp := pow_le_pow_right₀ h hj
      rw [show A = 1 + ‖S‖ ^ 5 from rfl]
      linarith
  let β : ℕ → ℝ := fun j => ⨆ y : Window p, ‖iteratedFDeriv ℝ j H y‖
  have hβnonneg : ∀ j, 0 ≤ β j := fun j => Real.iSup_nonneg fun _ => norm_nonneg _
  have hFβ : ∀ j ≤ 5, ∀ z, ‖iteratedFDeriv ℝ j F z‖ ≤ β j * ‖S‖ ^ j := by
    intro j hj z
    rw [hcomp j hj z]
    calc
      ‖(iteratedFDeriv ℝ j H (S z)).compContinuousLinearMap (fun _ => S)‖ ≤
          ‖iteratedFDeriv ℝ j H (S z)‖ * ‖S‖ ^ j := by
        refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
        simp [Finset.prod_const]
      _ ≤ β j * ‖S‖ ^ j := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact le_ciSup (hH.2.1 j hj) (S z)
  have hFscaledCD : ContDiff ℝ 5 (fun z => A⁻¹ * F z) :=
    contDiff_const.mul hFcd
  have hFscaledDeriv : ∀ j ≤ 5, ∀ z,
      iteratedFDeriv ℝ j (fun y => A⁻¹ * F y) z =
        A⁻¹ • iteratedFDeriv ℝ j F z := by
    intro j hj z
    have hs := iteratedFDeriv_const_smul_apply'
      (𝕜 := ℝ) (a := A⁻¹) (f := F) (i := j) (x := z)
      (hFcd.contDiffAt.of_le (by exact_mod_cast hj))
    simpa [smul_eq_mul] using hs
  have hFscaledBound : ∀ j ≤ 5, ∀ z,
      ‖iteratedFDeriv ℝ j (fun y => A⁻¹ * F y) z‖ ≤ β j := by
    intro j hj z
    rw [hFscaledDeriv j hj z, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 hApos.le)]
    calc
      A⁻¹ * ‖iteratedFDeriv ℝ j F z‖ ≤ A⁻¹ * (β j * ‖S‖ ^ j) :=
        mul_le_mul_of_nonneg_left (hFβ j hj z) (inv_nonneg.2 hApos.le)
      _ = (A⁻¹ * ‖S‖ ^ j) * β j := by ring
      _ ≤ 1 * β j := by
        apply mul_le_mul_of_nonneg_right _ (hβnonneg j)
        rw [inv_mul_le_iff₀ hApos]
        simpa [mul_one] using hAj j hj
      _ = β j := one_mul _
  have hFscaled : (fun z => A⁻¹ * F z) ∈ CbUnitBall SeqL2 5 := by
    refine ⟨hFscaledCD, ?_, ?_⟩
    · intro j hj
      refine ⟨β j, ?_⟩
      rintro _ ⟨z, rfl⟩
      exact hFscaledBound j hj z
    · unfold cbNorm
      calc
        (∑ j ∈ Finset.range 6, ⨆ z : SeqL2,
            ‖iteratedFDeriv ℝ j (fun z => A⁻¹ * F z) z‖) ≤
          ∑ j ∈ Finset.range 6, β j := by
            refine Finset.sum_le_sum fun j hj => ?_
            apply ciSup_le
            intro z
            exact hFscaledBound j (by
              have hj' := Finset.mem_range.mp hj
              omega) z
        _ = cbNorm 5 H := by simp [β, cbNorm]
        _ ≤ 1 := hH.2.2
  refine ⟨?_, ?_, ?_⟩
  · simpa [F, H, S] using hFcd
  · intro j hj z
    simpa [F, H, S] using hFbound j hj z
  · simpa [A, F, H, S] using hFscaled

#print axioms fp81s21_initial_heat_pullback

end HRS.Fp81.S21

end
