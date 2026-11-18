import HRS.MC.Q714GTCoreThm
import HRS.MC.Q714AsmBase

/-!
# E214P4 (L4): `L ∘ D³Φ` is a bounded `C²` function

For `Φ` in the `C_b^5` unit ball and a bounded linear functional `L` on trilinear forms (an element of
`TensorDual B 3`), the function `f = L ∘ D³Φ` is `C²`, and `|f|, ‖Df‖, ‖D²f‖ ≤ ‖L‖`.
-/

open MeasureTheory ProbabilityTheory
open HRS

noncomputable section

namespace HRS.MC.E214P

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

theorem p4_contDiff {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 5) (L : (B [×3]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    ContDiff ℝ 2 (fun x => L (iteratedFDeriv ℝ 3 Φ x)) :=
  L.contDiff.comp (hΦ.1.iteratedFDeriv_right (i := 3) (m := 2) (by norm_num))

theorem p4_cont {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 5) :
    Continuous (iteratedFDeriv ℝ 3 Φ) :=
  hΦ.1.continuous_iteratedFDeriv (m := 3) (by norm_num)

theorem p4_bound {Φ : B → ℝ} (hΦ : Φ ∈ CbUnitBall B 5) (L : (B [×3]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    (∀ w, |L (iteratedFDeriv ℝ 3 Φ w)| ≤ ‖L‖) ∧
    (∀ w, ‖iteratedFDeriv ℝ 1 (fun x => L (iteratedFDeriv ℝ 3 Φ x)) w‖ ≤ ‖L‖) ∧
    (∀ w, ‖iteratedFDeriv ℝ 2 (fun x => L (iteratedFDeriv ℝ 3 Φ x)) w‖ ≤ ‖L‖) := by
  have hD3 : ContDiff ℝ 2 (iteratedFDeriv ℝ 3 Φ) :=
    hΦ.1.iteratedFDeriv_right (i := 3) (m := 2) (by norm_num)
  have hj : ∀ j : ℕ, j ≤ 2 → ∀ w, ‖iteratedFDeriv ℝ j (fun x => L (iteratedFDeriv ℝ 3 Φ x)) w‖ ≤ ‖L‖ := by
    intro j hj w
    have h1 : iteratedFDeriv ℝ j (L ∘ iteratedFDeriv ℝ 3 Φ) w =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ j (iteratedFDeriv ℝ 3 Φ) w) :=
      L.iteratedFDeriv_comp_left (hD3.contDiffAt) (by exact_mod_cast hj)
    have h2 : iteratedFDeriv ℝ j (fun x => L (iteratedFDeriv ℝ 3 Φ x)) w =
        iteratedFDeriv ℝ j (L ∘ iteratedFDeriv ℝ 3 Φ) w := rfl
    rw [h2, h1]
    refine (L.norm_compContinuousMultilinearMap_le _).trans ?_
    rw [HRS.MC.Q714.GT.gt_norm_iter_iter]
    have : ‖iteratedFDeriv ℝ (3 + j) Φ w‖ ≤ 1 :=
      iteratedFDeriv_norm_le_of_mem hΦ (by omega) w
    nlinarith [norm_nonneg L]
  refine ⟨fun w => ?_, fun w => hj 1 (by norm_num) w, fun w => hj 2 le_rfl w⟩
  have := hj 0 (by norm_num) w
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

end HRS.MC.E214P

end
