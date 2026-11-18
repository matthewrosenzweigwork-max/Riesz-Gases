import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovAdjAux20
import HRS.MS.S67NlBD01
import HRS.MS.S67NlBD39
import HRS.MS.S67NlBD40
import HRS.MS.S67NlBD41
import HRS.MS.S67NlBD64
import HRS.MS.S67NlBD65
import HRS.MS.S67NlBD66
import HRS.MS.S67NlBD66C
import HRS.MS.S67NlBD67

/-!
# S6.7nl.68: finite-horizon gradient bound with uniform decay
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Route: the two-rate Volterra inequality (packet 66) is absorbed by packet 41 after comparing the
feedback kernel at `lam` with the larger kernel at `c1`; the common radius and output rate come from
packet 67, and the preliminary finite bound (packet 64), measurability (packet 65) and regularity
(packet 40) are used only to justify the absorption and the displayed regularity.
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

set_option maxHeartbeats 3200000 in
theorem s67bd_gradient_finite_decay (H : Mov2dTh d s β q ρ₀)
    (j M j' m : ℕ) (hM : (d : ℝ) / 2 + j + 5 < M) (hj' : 1 ≤ j')
    (hm : (d : ℝ) / 2 + j' + 6 < m) (hmM : (M : ℝ) + 4 < m) :
    ∃ Rstar C c : ℝ, 0 < Rstar ∧ Rstar ≤ 1 ∧ 1 ≤ C ∧ 0 < c ∧
      ∀ R0 c0 : ℝ, 0 ≤ R0 → R0 ≤ Rstar → 0 ≤ c0 →
      ∀ (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ →
      ∀ (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ), 0 ≤ T →
      IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f →
      ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) φ →
      MemOsc (M : ℝ) (s67psi ρ₀ φ) →
      cbNormVecE j (fun x => gradient φ x) < ⊤ →
      ∀ r ∈ Icc (0 : ℝ) T,
        ContDiff ℝ (j : WithTop ℕ∞) (fun x => gradient (f r) x) ∧
        cbNormVecE j (fun x => gradient (f r) x) < ⊤ ∧
        s67bd_Y j f r ≤ C * Real.exp (-c * (T - r)) *
          ((cbNormVecE j (fun x => gradient φ x)).toReal + oscNorm (M : ℝ) (s67psi ρ₀ φ)) := by
  obtain ⟨ha1, ha2, ha0, ha1', hM2, hm7, hrest⟩ :=
    s67bd_indices H.hd H.hs0 H.hsd j M j' m hM hj' hm hmM
  obtain ⟨Rbar, Cr, c1, lam, hRbar, hRbar1, hCr, hc1, hc1lam, h66⟩ :=
    s67bd_gradient_volterra H j M j' m hM hj' hm hmM
  obtain ⟨R, c, hR, hRRbar, hR1, hc, hcc1, hclam, hsm⟩ :=
    s67bd_common_radius Rbar Cr c1 lam hRbar hCr hc1 hc1lam
  refine ⟨R, 2 * Cr, c, hR, hR1, by linarith, hc, ?_⟩
  intro R0 c0 hR0 hR0R hc0 f0 ρ hρ T φ f hT hf hφreg hφ hφfin
  have hR01 : R0 ≤ 1 := hR0R.trans hR1
  have hR0bar : R0 ≤ Rbar := hR0R.trans hRRbar
  obtain ⟨Bf, hBf0, hBf⟩ := s67bd_bootstrap_finite H M m hM2 hm7 hmM R0 c0 hR0 hc0 f0 ρ hρ T φ f
    hT hf hφ
  obtain ⟨By, hBy0, hBy⟩ := s67bd_classical_cb_finite H j M m hM hm7 hmM R0 c0 hR0 hR01 hc0 f0 ρ hρ
    T φ f hT hf hφreg hφ hφfin
  have hreg : ∀ r ∈ Icc (0 : ℝ) T, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (f r) := fun r hr =>
    ((s67bd_qualitative_regular H j M hM (f r) (hf.c2 r hr) (hBf r hr).1).1).of_le
      (by exact_mod_cast (by omega : j + 1 ≤ j + 5))
  have hfc : ContinuousOn (fun p : ℝ × Euc d => f p.1 p.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := by
    rw [continuousOn_iff_continuous_restrict]
    have h1 : Continuous fun p : ↥(Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) =>
        ((⟨p.1.1, p.2.1⟩ : Icc (0 : ℝ) T), p.1.2) :=
      (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _).prodMk
        (continuous_snd.comp continuous_subtype_val)
    exact (s67_cont_val hf).comp h1
  obtain ⟨-, hYm⟩ := s67bd_gradient_norm_measurable d j T hT f hfc hreg (fun r hr => (hBy r hr).1)
  have hYnn : ∀ v, 0 ≤ s67bd_Y j f v := fun v => ENNReal.toReal_nonneg
  have hYb : ∀ v ∈ Icc (0 : ℝ) T, |s67bd_Y j f v| ≤ By := fun v hv => by
    rw [abs_of_nonneg (hYnn v)]; exact (hBy v hv).2
  have h66' := h66 R0 c0 hR0 hR0bar hc0 f0 ρ hρ T φ f hT hf hφreg hφ hφfin
  obtain ⟨Aφ, hAφ⟩ : ∃ Aφ : ℝ, Aφ = (cbNormVecE j (fun x => gradient φ x)).toReal +
      oscNorm (M : ℝ) (s67psi ρ₀ φ) := ⟨_, rfl⟩
  have hAφ0 : 0 ≤ Aφ := by
    rw [hAφ]; exact add_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _)
  have hvol : ∀ r ∈ Icc (0 : ℝ) T, s67bd_Y j f r ≤ Cr * Aφ * Real.exp (-c1 * (T - r)) +
      (Cr * R0) * ∫ v in Icc r T, s67bd_kernel 1 c1 (v - r) * s67bd_Y j f v := by
    intro r hr
    obtain ⟨hI, hY⟩ := h66' r hr
    have hI1 := s67bd66C_int (a := 1) (by norm_num) hc1 hr hYm hYb
    have hmono : ∫ v in Icc r T, s67bd_kernel 1 lam (v - r) * s67bd_Y j f v ≤
        ∫ v in Icc r T, s67bd_kernel 1 c1 (v - r) * s67bd_Y j f v := by
      refine setIntegral_mono_on hI hI1 measurableSet_Icc (fun v hv => ?_)
      have ht : 0 ≤ v - r := sub_nonneg.2 hv.1
      unfold s67bd_kernel
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (by nlinarith)) ?_) (hYnn v)
      have := Real.rpow_nonneg ht (-1 / 2 : ℝ)
      linarith
    rw [← hAφ] at hY
    have hCR : 0 ≤ Cr * R0 := mul_nonneg (by linarith) hR0
    nlinarith [mul_le_mul_of_nonneg_left hmono hCR]
  have hsmall : (Cr * R0) * mndBeta (1 - 1 / 2) (c1 - c) ≤ 1 / 2 := by
    have : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [this]
    refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR0R (by linarith))
      (mnd_beta_nonneg _ _)) hsm
  obtain ⟨-, habs⟩ := s67bd_volterra_absorb T (Cr * Aφ) (Cr * R0) 1 c1 c hT
    (mul_nonneg (by linarith) hAφ0) (mul_nonneg (by linarith) hR0) (by norm_num) (by norm_num) hc
    hcc1 (s67bd_Y j f) hYm (fun r _ => hYnn r) ⟨By, fun r hr => (hBy r hr).2⟩ hvol
    (by simpa using hsmall)
  intro r hr
  refine ⟨(s67bd_qualitative_regular H j M hM (f r) (hf.c2 r hr) (hBf r hr).1).2.2,
    (hBy r hr).1, ?_⟩
  have := habs r hr
  rw [hAφ] at this
  nlinarith [this]

end HRS.MS.BreakdownS67
