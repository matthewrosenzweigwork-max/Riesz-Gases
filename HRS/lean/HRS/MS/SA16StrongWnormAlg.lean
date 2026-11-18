import HRS.MS.SA16StrongWnorm

/-!
# S.A.16: triangle inequality and homogeneity of the weak norm `wNormE`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

section WnormAlg
variable {d : ℕ}

/-- the zeroth component of `G + H` is the sum of the zeroth components, almost everywhere -/
lemma sa16y_zero_add (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (G H : WmpSpace d m p) :
    ∀ᵐ x ∂(volume : Measure (Euc d)),
      (((G + H : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) =
        ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) +
          ((H : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) := by
  have h := Lp.coeFn_add (G : WLp d m p) (H : WLp d m p)
  filter_upwards [h] with x hx
  have : (((G + H : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x =
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x + ((H : WLp d m p) : Euc d → (WIndex d m → ℝ)) x := hx
  rw [this]
  rfl

theorem sa16y_wNormE_add_le (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (f g : Euc d → ℝ) :
    wNormE m p (fun x => f x + g x) ≤ wNormE m p f + wNormE m p g := by
  unfold wNormE
  simp only [ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf fun G1 => le_iInf fun h1 => le_iInf fun G2 => le_iInf fun h2 => ?_
  refine iInf₂_le_of_le (G2 + G1) ?_ ?_
  · filter_upwards [sa16y_zero_add m p G2 G1, h1, h2] with x hx hx1 hx2
    rw [hx, hx1, hx2]
  · rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)

theorem sa16y_wNormE_smul_le (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (c : ℝ) (f : Euc d → ℝ) :
    wNormE m p (fun x => c * f x) ≤ ENNReal.ofReal |c| * wNormE m p f := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul, abs_zero, ENNReal.ofReal_zero]
    unfold wNormE
    refine le_trans (iInf₂_le_of_le (0 : WmpSpace d m p) ?_ le_rfl) (by simp)
    filter_upwards [(Lp.coeFn_zero (WIndex d m → ℝ) (ENNReal.ofReal p) (volume : Measure (Euc d)))]
      with x hx
    have : (((0 : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x = 0 := hx
    rw [this]; rfl
  · unfold wNormE
    rw [ENNReal.mul_iInf_of_ne (by simpa using hc) ENNReal.ofReal_ne_top]
    refine le_iInf fun G => ?_
    rw [ENNReal.mul_iInf_of_ne (by simpa using hc) ENNReal.ofReal_ne_top]
    refine le_iInf fun hG => ?_
    refine iInf₂_le_of_le (c • G) ?_ ?_
    · have h := Lp.coeFn_smul c (G : WLp d m p)
      filter_upwards [h, hG] with x hx hx1
      have : (((c • G : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x =
          c • ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x := hx
      rw [this]
      simp [hx1]
    · rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [norm_smul, Real.norm_eq_abs]

theorem sa16y_wNormE_sum_le (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] {ι : Type*} (s : Finset ι)
    (f : ι → Euc d → ℝ) :
    wNormE m p (fun x => ∑ i ∈ s, f i x) ≤ ∑ i ∈ s, wNormE m p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := sa16y_wNormE_smul_le (d := d) m p 0 (fun _ => 0)
    simpa using this
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    refine (sa16y_wNormE_add_le m p _ _).trans ?_
    exact add_le_add le_rfl ih

end WnormAlg

end HRS.Whole.AppendixA.Phase2SA16
