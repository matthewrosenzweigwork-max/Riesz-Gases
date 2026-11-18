import HRS.MS.Fp81S21PredMap4

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas

/-- The chart operator gives the same propagated oscillator distribution as
any weighted-continuous physical functional agreeing on compact tests. -/
theorem fp81s21_chartVprop_physical
    {d r : ℕ} {Pw : ℝ} {C : WholeCoeff d} {m T : ℝ}
    {c : MultiIndex d → ℝ} (hP : (d : ℝ) < 2 * Pw)
    (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (E : r26t6_WeightedChart d r Pw) (z : r26t6_Coeff)
    (Q : (Euc d → ℝ) → ℝ) (hQ : S102Z r Pw Q)
    (hagree : ∀ f, IsR2Test f → fp81s21_chartAction E z f = Q f)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) {t : ℝ} (ht : t ∈ Icc u T) :
    fp81s21_chartVprop hP hD hlin E hu ht z = r2Vprop C m t u Q := by
  change r2Vprop C m t u (fp81s21_chartAction E z) = r2Vprop C m t u Q
  apply s102_ext
  intro α
  rw [s102_Vprop_coord hP hD (fp81s21_chartAction_S102Z E z) hlin hu ht,
    s102_Vprop_coord hP hD hQ hlin hu ht]
  exact (fp81s21_chartAction_propagated_test hP hD E z Q hQ hagree hu ht α).1

/-- Quantitative terminal-time continuity, with one constant for the given
summable orbit envelope. -/
theorem fp81s21_chartVprop_terminal_lipschitz
    {d r : ℕ} {Pw : ℝ} {C : WholeCoeff d} {m T : ℝ}
    {c : MultiIndex d → ℝ} (hP : (d : ℝ) < 2 * Pw)
    (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (E : r26t6_WeightedChart d r Pw) (z : r26t6_Coeff)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T)
    {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Icc u T) (ht₂ : t₂ ∈ Icc u T) (htt : t₁ ≤ t₂) :
    ‖fp81s21_chartVprop hP hD hlin E hu ht₂ z -
      fp81s21_chartVprop hP hD hlin E hu ht₁ z‖ ≤
      ‖z‖ * s102_KV d r Pw c * (t₂ - t₁) := by
  change ‖r2Vprop C m t₂ u (fp81s21_chartAction E z) -
    r2Vprop C m t₁ u (fp81s21_chartAction E z)‖ ≤ _
  simpa only [abs_norm] using
    s102_Vprop_lip_M hP hD (fp81s21_chartAction_S102Z E z) hlin
      (fp81s21_chartAction_weighted_bound E z) hu ht₁ ht₂ htt

#print axioms HRS.Fp81.S21.fp81s21_chartVprop_physical
#print axioms HRS.Fp81.S21.fp81s21_chartVprop_terminal_lipschitz

end HRS.Fp81.S21
