import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD01
import HRS.MS.S67NlBD41
import HRS.MS.S67NlBD42
import HRS.MS.S67NlBD65
import HRS.MS.S67NlBD66C
import HRS.MS.S67NlBD66D

/-!
# S6.7nl.66: the two-rate gradient Volterra inequality
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Assembly: the weighted decay (packet 42) and the raw differentiated Duhamel inequality (66C) are fed
into the two-rate scalar absorption (66D); radius and constants are chosen before the trajectory.
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

theorem s67bd_gradient_volterra (H : Mov2dTh d s β q ρ₀)
    (j M j' m : ℕ) (hM : (d : ℝ) / 2 + j + 5 < M) (hj' : 1 ≤ j')
    (hm : (d : ℝ) / 2 + j' + 6 < m) (hmM : (M : ℝ) + 4 < m) :
    ∃ Rstar C c1 lam : ℝ,
      0 < Rstar ∧ Rstar ≤ 1 ∧ 1 ≤ C ∧ 0 < c1 ∧ c1 ≤ lam ∧
      ∀ R0 c0 : ℝ, 0 ≤ R0 → R0 ≤ Rstar → 0 ≤ c0 →
      ∀ (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ →
      ∀ (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ), 0 ≤ T →
      IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f →
      ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) φ →
      MemOsc (M : ℝ) (s67psi ρ₀ φ) →
      cbNormVecE j (fun x => gradient φ x) < ⊤ →
      ∀ r ∈ Icc (0 : ℝ) T,
        IntegrableOn (fun v => s67bd_kernel 1 lam (v - r) * s67bd_Y j f v)
          (Icc r T) volume ∧
        s67bd_Y j f r ≤ C * Real.exp (-c1 * (T - r)) *
          ((cbNormVecE j (fun x => gradient φ x)).toReal + oscNorm (M : ℝ) (s67psi ρ₀ φ)) +
          C * R0 * ∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * s67bd_Y j f v := by
  obtain ⟨ha1, ha2, ha0, ha1', hM2, hm7, hrest⟩ :=
    s67bd_indices H.hd H.hs0 H.hsd j M j' m hM hj' hm hmM
  obtain ⟨Rw, Cw, cw, hRw, hCw, hcw, hw⟩ := s67bd_weighted_decay H M m hM2 hm7 hmM
  obtain ⟨Cr, lam, hCr, hlam, hraw⟩ := s67bd_gradient_duhamel_inequality H j M m hM hm7 hmM
  obtain ⟨C, c1, hC, hc1, hc1lam, hs⟩ :=
    s67bd_two_rate_scalar Cr Cw lam cw hCr (zero_le_one.trans hCw) hlam hcw
  refine ⟨min Rw 1, C, c1, lam, lt_min hRw zero_lt_one, min_le_right _ _, hC, hc1, hc1lam, ?_⟩
  intro R0 c0 hR0 hRstar hc0 f0 ρ hρ T φ f hT hf hφreg hφ hφfin
  have hR1 : R0 ≤ 1 := hRstar.trans (min_le_right _ _)
  have hRRw : R0 ≤ Rw := hRstar.trans (min_le_left _ _)
  have hweights := hw R0 c0 hR0 hRRw hc0 f0 ρ hρ T φ f hT hf hφ
  have hineq := hraw R0 c0 hR0 hR1 hc0 f0 ρ hρ T φ f hT hf hφreg hφ hφfin
  have hfinal := hs T R0 (cbNormVecE j (fun x => gradient φ x)).toReal
    (oscNorm (M : ℝ) (s67psi ρ₀ φ)) hT hR0 ENNReal.toReal_nonneg (Real.sqrt_nonneg _)
    (fun v => oscNorm (M : ℝ) (s67psi ρ₀ (f v))) (s67bd_Y j f)
    (fun v hv => Real.sqrt_nonneg _) (fun v hv => ENNReal.toReal_nonneg)
    (fun v hv => (hweights v hv).2) (fun r hr => (hineq r hr).2.1)
    (fun r hr => (hineq r hr).1) (fun r hr => (hineq r hr).2.2)
  exact fun r hr => ⟨(hineq r hr).1, hfinal r hr⟩

end HRS.MS.BreakdownS67
