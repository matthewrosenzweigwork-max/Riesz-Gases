import HRS.MS.Fp81S21JointP
import HRS.MS.Fp81S21WickApprox38
import HRS.MS.Fp81S21WickApprox26

/-! The linear chart-coordinate bridge for the fixed Gaussian selector. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The canonical embedded linear field has exactly the raw oscillator
coordinates used by the joint polynomial map, on the time-product measure. -/
theorem fp81s21_jointG_linear_coordinates
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (εG εB : ℕ → ℝ) (S : fp81s21_GaussianPhysical31 p R Es E εG εB)
    (G : GaussianRealization R) (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H) :
    ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) H)).prod G.P),
      ∀ j : ℕ,
        fp81s21_gaussian_embedFamily p Es E (S.qsηG G) (a + z.1) z.2 j =
          OscDual.eval (G.Z (a + z.1) z.2) (E.test j) := by
  filter_upwards [((S.gaussian_linear G).coefficients.compact_agreement a ha H hH)] with z hz j
  rw [← fp81s21_chartAction_test_coordinate2 E]
  exact hz (E.test j) (E.test_smooth j)

#print axioms fp81s21_jointG_linear_coordinates
end HRS.Fp81.S21
end
