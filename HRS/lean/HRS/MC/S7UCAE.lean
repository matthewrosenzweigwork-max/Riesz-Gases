import HRS.MC.S7FCW12D
import HRS.MC.S7FCW12G
import HRS.MC.S7FCF5EA
import HRS.MC.S7UCDefs

/-!
# S7UCAE: measurability of the finite-rank pairs at window `a` (UC-E3, UC-E4)

* `s7_UC_E3_finite_rank_measurable_proof`: `s7_FC_E3_finite_rank_measurable_proof` (`S7FCW12D.lean`) with the window start `a`;
  the `zetaWin` component is `S7FCF5E_aemeasurable_zetaWin` (every `a`), the `L²` component is
  `s7fcw12_toL2_fcPart_aemeasurable` (already for every `a ≥ 0`).
* `s7_UC_E4_limit_measurable_proof`: `s7_FC_E4_limit_measurable_proof` (`S7FCW12G.lean`) with the window start `a`,
  from the a.s. continuity of `η` on `[0, a+T]`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7UCA

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCH4

variable {d : ℕ}

theorem s7_UC_E3_finite_rank_measurable_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {N : ℕ} (hN : 1 ≤ N)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization R.D P
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)
    (a : ℝ) (ha : 0 ≤ a) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) :
    AEMeasurable (fun ω => (zetaWin r T a P X ω,
      toL2 r T (fun t => fcPartAt r S K (fun t => withDensityReal (R.ρ t)) P X (a + t) ω))) P := by
  have hS := hreal.solution T
  have hm : (d : ℝ) < 2 * r := by
    rw [hr]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hN0 : 0 < N := by omega
  refine AEMeasurable.prodMk
    (HRS.MC.Sec7.S7FCF5E.S7FCF5E_aemeasurable_zetaWin r T a hT hm P X hS.adapted hS.cont hN0) ?_
  exact HRS.MC.Sec7.S7FCW12.s7fcw12_toL2_fcPart_aemeasurable R r T hT a ha S K P X hS.adapted hS.cont

theorem s7_UC_E4_limit_measurable_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η)
    (B : ℝ → Ω' → NegSobolev d r) (hBm : Measurable (Function.uncurry B))
    (a : ℝ) (ha : 0 ≤ a) (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) :
    AEMeasurable (pairLim r T a η B) P' ∧
    AEMeasurable (fun ω => (procWin r T a η ω,
      toL2 r T (fun t => fcGaussAt r S K P' η (a + t) ω))) P' := by
  obtain ⟨Y₀, -, hsol⟩ := hη
  have hL := hsol (a + T)
  have hf : ContinuousOn (fun t : ℝ => a + t) (Set.Icc 0 T) :=
    (by fun_prop : Continuous fun t : ℝ => a + t).continuousOn
  have hcont : ∀ᵐ ω ∂P', ContinuousOn (fun t => η (a + t) ω) (Set.Icc 0 T) :=
    hL.cont.mono fun ω hω => hω.comp hf fun t ht =>
      Set.mem_Icc.2 ⟨by linarith [(Set.mem_Icc.1 ht).1], by linarith [(Set.mem_Icc.1 ht).2]⟩
  have hfun : (fun t ω => η (a + t) ω) = (fun t ω => η (a + (0 + t)) ω) := by
    funext t ω
    rw [zero_add]
  have hW : procWin r T a η = HRS.Uniform.windowPath 0 T (fun t ω => η (a + t) ω) := by
    funext ω
    exact congrArg (fun Z : ℝ → Ω' → NegSobolev d r => HRS.toPath r T Z ω) hfun
  have hproc : AEMeasurable (procWin r T a η) P' := by
    rw [hW]
    exact HRS.Uniform.Q45.aemeasurable_windowPath' P' hT (fun t ω => η (a + t) ω)
      (fun t _ => (hL.meas (a + t)).aemeasurable) hcont
  have hBt : Measurable fun ω => HRS.Sec7.toL2 r T (fun t => B (a + t) ω) :=
    HRS.MC.Sec7.S7FCW12.s7fcw12_toL2_measurable T (fun t ω => B (a + t) ω)
      (hBm.comp ((measurable_const.add measurable_fst).prodMk measurable_snd))
  constructor
  · unfold pairLim
    exact AEMeasurable.prodMk hproc hBt.aemeasurable
  · refine AEMeasurable.prodMk hproc ?_
    exact HRS.MC.Sec7.S7FCW12.s7fcw12_coord_aemeasurable hT P' (fun t ω => η (a + t) ω)
      (fun t => hL.meas (a + t)) hcont 0
      (HRS.MC.Sec7.S7FCW12.s7fcw12_gaussPsi r S K) (HRS.MC.Sec7.S7FCW12.s7fcw12_gaussPsi_meas r S K)
      (fun t ω => fcGaussAt r S K P' η (a + t) ω)
      (fun t _ ω => HRS.MC.Sec7.S7FCW12.s7fcw12_fcGauss_eq r S K P' η (a + t) ω)

end HRS.MC.Sec7.S7UCA

end
