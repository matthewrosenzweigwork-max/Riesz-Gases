import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD41

/-!
# S6.7 nonlinear, packet S6.7nl.54: singular exponential convolution with strict rate gaps

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4838-4840, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definitions: none.
The integrand factors as `exp(-c tau) * k_{c1-c}(w) * exp(-(c2-c)(tau-w))` with
`k_kappa = s67bd_kernel 1 kappa`; the last factor is at most one on `[0,tau]`, and the beta bound
of packet 41 (`s67bd_kernel_integral_le` at `r = 0`) gives the constant `mndBeta (1/2) (c1-c)`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

theorem s67bd_exponential_convolution (c1 c2 c : ℝ)
    (hc1 : 0 < c1) (hc2 : 0 < c2) (hc : 0 < c) (hcmin : c < min c1 c2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ →
      IntegrableOn (fun w => s67bd_kernel 1 c1 w * Real.exp (-c2 * (τ - w)))
        (Icc (0 : ℝ) τ) volume ∧
      (∫ w in Icc (0 : ℝ) τ, s67bd_kernel 1 c1 w * Real.exp (-c2 * (τ - w))) ≤
        C * Real.exp (-c * τ) := by
  have hc1' : c < c1 := lt_of_lt_of_le hcmin (min_le_left _ _)
  have hc2' : c < c2 := lt_of_lt_of_le hcmin (min_le_right _ _)
  have hκ : 0 < c1 - c := sub_pos.2 hc1'
  have ha : (1 : ℝ) < 2 := by norm_num
  refine ⟨mndBeta (1 - 1 / 2) (c1 - c), mnd_beta_nonneg _ _, fun τ hτ => ?_⟩
  set k : ℝ → ℝ := fun w => s67bd_kernel 1 (c1 - c) w with hk
  have hkint : IntegrableOn k (Icc (0 : ℝ) τ) volume := by
    have := s67bd_kernel_integrableOn (a := 1) (κ := c1 - c) ha hκ hτ
    simpa [hk] using this
  have hkle : ∫ w in Icc (0 : ℝ) τ, k w ≤ mndBeta (1 - 1 / 2) (c1 - c) := by
    have := s67bd_kernel_integral_le (a := 1) (κ := c1 - c) ha hκ hτ
    simpa [hk] using this
  have hfac : ∀ w : ℝ, s67bd_kernel 1 c1 w * Real.exp (-c2 * (τ - w)) =
      (Real.exp (-c * τ) * k w) * Real.exp (-(c2 - c) * (τ - w)) := by
    intro w
    have h : Real.exp (-c1 * w) * Real.exp (-c2 * (τ - w)) =
        Real.exp (-c * τ) * Real.exp (-(c1 - c) * w) * Real.exp (-(c2 - c) * (τ - w)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    unfold s67bd_kernel at *
    simp only [hk, s67bd_kernel]
    calc (1 + w ^ (-(1 : ℝ) / 2)) * Real.exp (-c1 * w) * Real.exp (-c2 * (τ - w))
        = (1 + w ^ (-(1 : ℝ) / 2)) * (Real.exp (-c1 * w) * Real.exp (-c2 * (τ - w))) := by ring
      _ = _ := by rw [h]; ring
  have hE : Continuous fun w : ℝ => Real.exp (-(c2 - c) * (τ - w)) := by fun_prop
  have hEb : ∀ᵐ w ∂(volume.restrict (Icc (0 : ℝ) τ)),
      ‖Real.exp (-(c2 - c) * (τ - w))‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by nlinarith [hw.2, sub_pos.2 hc2'])
  have hint : IntegrableOn (fun w => (Real.exp (-c * τ) * k w) * Real.exp (-(c2 - c) * (τ - w)))
      (Icc (0 : ℝ) τ) volume :=
    Integrable.mul_bdd (c := 1) (hkint.const_mul _) hE.aestronglyMeasurable hEb
  simp_rw [hfac]
  refine ⟨hint, ?_⟩
  calc ∫ w in Icc (0 : ℝ) τ, (Real.exp (-c * τ) * k w) * Real.exp (-(c2 - c) * (τ - w))
      ≤ ∫ w in Icc (0 : ℝ) τ, Real.exp (-c * τ) * k w := by
        refine setIntegral_mono_on hint (hkint.const_mul _) measurableSet_Icc (fun w hw => ?_)
        have hk0 : 0 ≤ k w := s67bd_kernel_nonneg 1 _ hw.1
        have hE1 : Real.exp (-(c2 - c) * (τ - w)) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [hw.2, sub_pos.2 hc2'])
        have : 0 ≤ Real.exp (-c * τ) * k w := mul_nonneg (Real.exp_pos _).le hk0
        nlinarith
    _ = Real.exp (-c * τ) * ∫ w in Icc (0 : ℝ) τ, k w := integral_const_mul _ _
    _ ≤ Real.exp (-c * τ) * mndBeta (1 - 1 / 2) (c1 - c) :=
        mul_le_mul_of_nonneg_left hkle (Real.exp_pos _).le
    _ = mndBeta (1 - 1 / 2) (c1 - c) * Real.exp (-c * τ) := mul_comm _ _

end HRS.MS.BreakdownS67
