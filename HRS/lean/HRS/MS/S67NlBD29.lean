import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovAdjAux10
import HRS.MS.S67NlBD06
import HRS.MS.S67NlBD24
import HRS.MS.S67NlBD25
import HRS.MS.S67NlBD28

/-!
# S6.7nl.29: paths representing the actual `f` and its projected source
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Route: at each `r ∈ [0,T]` packet 06 gives `ψ_r ∈ Σ²` (hence `L²`), `s67_psi_orth` its zero pairing,
packet 25 (σ = 2) gives `R_r ∈ L²` with zero pairing; packet 28 supplies the `MovL2Zero`
representatives; the paths are chosen on the whole line (zero off `[0,T]`).
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

theorem s67bd_classical_realizations (H : Mov2dTh d s β q ρ₀)
    (m : ℕ) (hm : (d : ℝ) / 2 + 7 < m) (R0 c0 : ℝ)
    (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hρ : MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ)
    (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (hT : 0 ≤ T)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f) :
    ∃ Ψ R : ℝ → MovL2Zero ρ₀, ∀ r ∈ Icc (0 : ℝ) T,
      (∀ᵐ x ∂(volume : Measure (Euc d)), movFun (Ψ r) x = s67psi ρ₀ (f r) x) ∧
      (∀ᵐ x ∂(volume : Measure (Euc d)), movFun (R r) x =
        s67bd_R d s ρ₀ (movV ρ₀ ρ r) (s67psi ρ₀ (f r)) x) := by
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  have hsqc : Continuous (fun x => Real.sqrt (ρ₀ x)) := by
    rw [← hψs]; exact ψs.continuous
  obtain ⟨B, -, hB⟩ := s67bd_classical_sigma2 H ρ T φ f hT hf
  have hm6 : (2 : ℝ) + 4 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨C, -, hC⟩ := s67bd_projected_source_bound (ρ₀ := ρ₀) H m 2 hm le_rfl hm6
  obtain ⟨Bf, hBf⟩ := hf.bdd 0 (by norm_num)
  have key : ∀ r : ℝ, ∃ z1 z2 : MovL2Zero ρ₀, r ∈ Icc (0 : ℝ) T →
      (∀ᵐ x ∂(volume : Measure (Euc d)), movFun z1 x = s67psi ρ₀ (f r) x) ∧
      (∀ᵐ x ∂(volume : Measure (Euc d)), movFun z2 x =
        s67bd_R d s ρ₀ (movV ρ₀ ρ r) (s67psi ρ₀ (f r)) x) := by
    intro r
    by_cases hr : r ∈ Icc (0 : ℝ) T
    · obtain ⟨hmem, -, hc2, hD⟩ := hB r hr
      -- the centered path value
      have hzero : (∫ x, Real.sqrt (ρ₀ x) * s67psi ρ₀ (f r) x) = 0 :=
        s67_psi_orth H (hf.c2 r hr).continuous.aestronglyMeasurable
          (B := Bf) (fun x => by
            have := hBf r hr x
            rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this)
      obtain ⟨z1, hz1, -⟩ := s67bd_zero_realization H _ hmem.1 hzero
      -- the projected source
      have hvc : Continuous (movV ρ₀ ρ r) := by
        show Continuous (fun x => (ρ r x - ρ₀ x) / Real.sqrt (ρ₀ x))
        exact ((hρ.regular r hr.1).sub hρsm.continuous).div hsqc
          (fun x => (Real.sqrt_pos.2 (hρpos x)).ne')
      obtain ⟨hRm, -, hRz, -⟩ := hC (movV ρ₀ ρ r) (s67psi ρ₀ (f r)) hvc
        (hρ.weighted r hr.1).1 hc2 hmem hD
      obtain ⟨z2, hz2, -⟩ := s67bd_zero_realization H _ hRm.1 hRz
      exact ⟨z1, z2, fun _ => ⟨hz1, hz2⟩⟩
    · exact ⟨0, 0, fun h => absurd h hr⟩
  choose Ψ R hΨR using key
  exact ⟨Ψ, R, fun r hr => hΨR r hr⟩

end HRS.MS.BreakdownS67
