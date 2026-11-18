import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD41
import HRS.MS.S67NlBD52
import HRS.MS.S67NlBD53
import HRS.MS.S67NlBD55
import HRS.MS.S67NlBD58
import HRS.MS.S67NlBD59A
import HRS.MS.S67NlBD59C
import HRS.MS.S67NlBD65
import HRS.MS.S67NlBD59B

/-!
# S6.7 nonlinear, packet S6.7nl.59: short-slab absorption independent of spatial difference steps

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4835-4851, nonlinear part of
`S:W:lem:r2mov-global-adjoint`. No owned definitions. The proof is the integration of the existing
producer glue (Brownian realization, slab gradient inequality, short-kernel absorption, OU Duhamel),
preserved as written.
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

theorem s67bd_short_slab (d : ℕ) (ν q Mb : ℝ)
    (hν : 0 < ν) (hq : 0 < q) (hMb : 0 ≤ Mb) :
    ∃ τstar C : ℝ, 0 < τstar ∧ 1 ≤ C ∧
      ∀ (T D MJ : ℝ), 0 ≤ T → T ≤ τstar → 0 ≤ D → 0 ≤ MJ →
      ∀ (u a : ℝ → Euc d → ℝ) (B : ℝ → Euc d → Euc d) (J : ℝ → Euc d → ℝ),
      s67bd_ParabolicData ν q T u a B J →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖B t x‖ ≤ Mb) →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x, |J t x| ≤ MJ) →
      (∀ x, ‖gradient (u 0) x‖ ≤ D) →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖gradient (u t) x‖ ≤ C * (D + MJ) := by
  obtain ⟨Ω, mΩ, P, hP, ℱ, W, hW⟩ := exists_isBrownianFiltration_type (Fin d)
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  obtain ⟨Cg, hCg, hg⟩ := s67bd_slab_gradient_inequality P ℱ W hW ν q hν hq
  obtain ⟨τstar, C, hτstar, hC, habs⟩ := s67bd_short_kernel_absorb Cg Mb hCg hMb
  refine ⟨τstar, C, hτstar, hC, ?_⟩
  intro T D MJ hT hTτ hD hMJ u a B J hu hB hJ hinit
  have hduh := s67bd_parabolic_ou_duhamel P ℱ W hW ν q T Mb MJ hν hq hT hMb hMJ
    u a B J hu hB hJ
  obtain ⟨hmeas, hfin, hnonneg, hbdd, hpoint, hvol⟩ :=
    hg T Mb MJ D hT hMb hMJ hD u a B J hu hduh hB hJ hinit
  have hy := habs T D MJ hT hTτ hD hMJ (s67bd_Y 0 u) hmeas hnonneg hbdd
    (fun t ht => (hvol t ht).2)
  exact fun t ht x => (hpoint t ht x).trans (hy t ht)

end HRS.MS.BreakdownS67
