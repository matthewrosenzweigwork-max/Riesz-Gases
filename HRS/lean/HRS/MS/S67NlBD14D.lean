import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovForceAux6
import HRS.MS.S67NlBD03
import HRS.MS.S67NlBD14A
import HRS.MS.S67NlBD14B
import HRS.MS.S67NlBD14C

/-!
# S6.7 nonlinear, packet S6.7nl.14D: algebraic recombination of near, tail and cutoff correction

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4221-4245, 4751-4763, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). No owned definitions. The analytic inputs
(integrability of the near and tail terms, the data integrability, and the near-integral identity
with the annular correction) are explicit hypotheses. The proof is pointwise recombination:
the full conditional integrand is `near + tail`; `kfar` vanishes on the ball `|z| < 1`, so
`cutoffCorrection + tail_i = kfar * h` pointwise; coordinate evaluation commutes with the integral.
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

theorem s67bd_force_recombine (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (h : Euc d → ℝ) (x : Euc d)
    (hnear : Integrable (s67bd_near d s h x) volume)
    (htail : Integrable (s67bd_tail d s h x) volume)
    (hdata : ∀ i : Fin d,
      Integrable (fun y => movb2_gloc d s (x - y) * s67bd_D i h y) volume ∧
      Integrable (fun y => movb2_kfar d s i (x - y) * h y) volume)
    (hibp : ∀ i : Fin d,
      Integrable (fun y => s67bd_cutoffCorrection d s i (x - y) * h y) volume ∧
      (∫ y, s67bd_near d s h x y) i = s67bd_local d s h i x +
        ∫ y, s67bd_cutoffCorrection d s i (x - y) * h y) :
    Integrable (fun y => if ‖x - y‖ ≤ 1 / 4 then
      (h y - h x) • rieszKernelGrad d s (x - y) else
      h y • rieszKernelGrad d s (x - y)) volume ∧
    ∀ i : Fin d,
      Integrable (fun y => movb2_gloc d s (x - y) * s67bd_D i h y) volume ∧
      Integrable (fun y => movb2_kfar d s i (x - y) * h y) volume ∧
      movForce d s h x i = s67bd_local d s h i x + s67bd_far d s h i x := by
  have hfun : (fun y => if ‖x - y‖ ≤ 1 / 4 then
      (h y - h x) • rieszKernelGrad d s (x - y) else
      h y • rieszKernelGrad d s (x - y)) =
      fun y => s67bd_near d s h x y + s67bd_tail d s h x y := by
    funext y
    unfold s67bd_near s67bd_tail
    split_ifs <;> simp
  have hF : movForce d s h x =
      (∫ y, s67bd_near d s h x y) + ∫ y, s67bd_tail d s h x y := by
    rw [← integral_add hnear htail]
    unfold movForce convGradConvW
    congr 1
  refine ⟨?_, fun i => ⟨(hdata i).1, (hdata i).2, ?_⟩⟩
  · rw [hfun]
    exact hnear.add htail
  · have hcorr : ∀ y, s67bd_cutoffCorrection d s i (x - y) * h y +
        s67bd_tail d s h x y i = movb2_kfar d s i (x - y) * h y := by
      intro y
      unfold s67bd_tail s67bd_cutoffCorrection
      by_cases hz : ‖x - y‖ ≤ 1 / 4
      · have hk := s67bd14c_kfar_near s i (z := x - y) (by linarith)
        simp only [if_pos hz, hk]
        simp
      · simp only [if_neg hz, PiLp.smul_apply, smul_eq_mul]
        ring
    have hcorrI := (hibp i).1
    have htailI : Integrable (fun y => s67bd_tail d s h x y i) volume :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp htail
    have hT : (∫ y, s67bd_tail d s h x y) i = ∫ y, s67bd_tail d s h x y i := by
      have hc := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj (𝕜 := ℝ) i) htail
      simpa using hc.symm
    have hfar : s67bd_far d s h i x =
        (∫ y, s67bd_cutoffCorrection d s i (x - y) * h y) +
          ∫ y, s67bd_tail d s h x y i := by
      rw [← integral_add hcorrI htailI]
      unfold s67bd_far
      congr 1
      funext y
      exact (hcorr y).symm
    rw [hF, PiLp.add_apply, (hibp i).2, hT, hfar]
    ring
