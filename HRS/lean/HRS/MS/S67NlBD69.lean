import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD01
import HRS.MS.S67NlBD39
import HRS.MS.S67NlBD40
import HRS.MS.S67NlBD68

/-!
# S6.7nl.69: extended-norm uniform gradient estimate
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Route: split on finiteness of the terminal gradient `cb` norm.  Finite branch: packet 68, converted
back to `ℝ≥0∞`.  Infinite branch: regularity of the output gradient from packets 39 and 40, and the
right side is `⊤` because `ofReal (C * exp ..) > 0` (`C ≥ 1`).
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

theorem s67bd_uniform_gradient (H : Mov2dTh d s β q ρ₀)
    (j M : ℕ) (hM : (d : ℝ) / 2 + j + 5 < M) (j' m : ℕ) (hj' : 1 ≤ j')
    (hm : (d : ℝ) / 2 + j' + 6 < m) (hmM : (M : ℝ) + 4 < m) :
    ∃ Rstar C c : ℝ, 0 < Rstar ∧ 1 ≤ C ∧ 0 < c ∧
      ∀ R0 c0 : ℝ, 0 ≤ R0 → R0 ≤ Rstar → 0 ≤ c0 →
      ∀ (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ →
      ∀ (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ), 0 ≤ T →
      IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f →
      ContDiff ℝ (j + 1) φ → MemOsc (M : ℝ) (s67psi ρ₀ φ) →
      ∀ r ∈ Icc (0 : ℝ) T,
        ContDiff ℝ j (fun x => gradient (f r) x) ∧
        cbNormVecE j (fun x => gradient (f r) x) ≤
          ENNReal.ofReal (C * Real.exp (-c * (T - r))) *
            (cbNormVecE j (fun x => gradient φ x) + ENNReal.ofReal (oscNorm (M : ℝ) (s67psi ρ₀ φ))) := by
  obtain ⟨ha1, ha2, ha0, ha1', hM2, hm7, hrest⟩ :=
    s67bd_indices H.hd H.hs0 H.hsd j M j' m hM hj' hm hmM
  obtain ⟨Rs, C, c, hRs, hRs1, hC, hc, h68⟩ := s67bd_gradient_finite_decay H j M j' m hM hj' hm hmM
  refine ⟨Rs, C, c, hRs, hC, hc, ?_⟩
  intro R0 c0 hR0 hR0R hc0 f0 ρ hρ T φ f hT hf hφreg hφ r hr
  have hφreg' : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) φ := by exact_mod_cast hφreg
  obtain ⟨Bf, hBf0, hBf⟩ := s67bd_bootstrap_finite H M m hM2 hm7 hmM R0 c0 hR0 hc0 f0 ρ hρ T φ f
    hT hf hφ
  have hgreg := (s67bd_qualitative_regular H j M hM (f r) (hf.c2 r hr) (hBf r hr).1).2.2
  refine ⟨hgreg, ?_⟩
  have hpos : 0 < C * Real.exp (-c * (T - r)) := mul_pos (by linarith) (Real.exp_pos _)
  by_cases hfin : cbNormVecE j (fun x => gradient φ x) < ⊤
  · obtain ⟨-, hfr, hY⟩ := h68 R0 c0 hR0 hR0R hc0 f0 ρ hρ T φ f hT hf hφreg' hφ hfin r hr
    have e1 : cbNormVecE j (fun x => gradient (f r) x) =
        ENNReal.ofReal (s67bd_Y j f r) := (ENNReal.ofReal_toReal hfr.ne).symm
    have e2 : cbNormVecE j (fun x => gradient φ x) =
        ENNReal.ofReal (cbNormVecE j (fun x => gradient φ x)).toReal :=
      (ENNReal.ofReal_toReal hfin.ne).symm
    rw [e1]
    refine (ENNReal.ofReal_le_ofReal hY).trans ?_
    rw [ENNReal.ofReal_mul (mul_nonneg (by linarith) (Real.exp_pos _).le),
      ENNReal.ofReal_add ENNReal.toReal_nonneg
        (HRS.MS.MovC1.movc1_osc_nonneg (M : ℝ) (s67psi ρ₀ φ)),
      ← e2]
  · have htop : cbNormVecE j (fun x => gradient φ x) = ⊤ := not_lt_top_iff.1 hfin
    rw [htop, top_add, ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
    exact le_top

end HRS.MS.BreakdownS67
