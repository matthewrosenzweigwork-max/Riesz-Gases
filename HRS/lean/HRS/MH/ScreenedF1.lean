import HRS.MH.ScreenedDefs
import HRS.MS.FlowA
import HRS.MS.FlowD

/-! Packet F1 of `B:lem:screened` (S.B.4): proof of `flow_lip_sep` in `ScreenedSpec.lean`.
Adaptors `IsAdvectingDrift -> IsDriftBounds`, `IsNegDriftFlow (BKernel) -> IsNegDriftFlow (AppendixA)`;
Lipschitz bounds from `HRS.MS.FlowA.flow_lipschitz` and `flow_invertible`; separation from
`HRS.MS.FlowD.flow_covering_separation` (constant `CF = C + max Cb 0`). -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- Adaptor: `IsAdvectingDrift` (BKernel) gives the drift bounds `IsDriftBounds` (AppendixA). -/
theorem f1a_drift {m : ℕ} {Cb T : ℝ} {b : ℝ → Euc d → Euc d} (hb : IsAdvectingDrift m Cb T b) :
    HRS.Whole.AppendixALemmas.IsDriftBounds T m Cb b where
  cont := hb.cont
  smooth τ hτ := by
    have h := hb.smooth τ hτ
    push_cast
    exact h
  deriv_bound := hb.deriv_bdd
  growth := hb.growth

/-- Adaptor: `IsNegDriftFlow` (BKernel, with `bij`) gives `IsNegDriftFlow` (AppendixA, without `bij`). -/
theorem f1a_flow {T : ℝ} {b : ℝ → Euc d → Euc d} {Ψ : ℝ → Euc d → Euc d} (hΨ : IsNegDriftFlow T b Ψ) :
    HRS.Whole.AppendixALemmas.IsNegDriftFlow T b Ψ :=
  ⟨hΨ.init, hΨ.ode⟩

theorem flow_lip_sep_proof (hd : 1 ≤ d) (m : ℕ) (Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ → ∀ τ ∈ Icc (0 : ℝ) T,
        (∀ x y, ‖Ψ τ x - Ψ τ y‖ ≤ Real.exp (CF * τ) * ‖x - y‖) ∧
        (∀ x y, ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ ≤ Real.exp (CF * τ) * ‖x - y‖) ∧
        (∀ z : Euc d, ∀ x y : Euc d, x ∈ tsupport (advCutoff χ Ψ τ z) →
          y ∈ tsupport (fun y => 1 - advCutoff χh Ψ τ z y) → 4 * Real.exp (-(CF * τ)) ≤ ‖x - y‖) := by
  have hU : HRS.Whole.AppendixA.IsUlocCutoff χ := hχ.1
  have hR : HRS.Whole.AppendixALemmas.IsCutoffRad 6 8 χh :=
    ⟨hχ.2.1, hχ.2.2.1, hχ.2.2.2.1, fun x => ⟨(hχ.2.2.2.2.1 x).1, (hχ.2.2.2.2.1 x).2⟩, hχ.2.2.2.2.2⟩
  obtain ⟨C, hC, hsep⟩ := HRS.MS.FlowD.flow_covering_separation d (max Cb 0) (le_max_right _ _) χ χh hU hR
  refine ⟨C + max Cb 0, add_nonneg hC.le (le_max_right _ _), ?_⟩
  intro b Ψ hb hΨ τ hτ
  have hτ0 : 0 ≤ τ := hτ.1
  have hT : 0 ≤ T := hτ0.trans hτ.2
  have hbD := f1a_drift hb
  have hΨA := f1a_flow hΨ
  have hbij := hΨ.bij τ hτ
  obtain ⟨Φ, hΦ1, hΦ2, hΦL⟩ := HRS.MS.FlowA.flow_invertible hT hbD hΨA τ hτ
  have hinv : ∀ y, Function.invFun (Ψ τ) y = Φ y := fun y => by
    have h := Function.leftInverse_invFun hbij.1 (Φ y)
    rwa [hΦ2 y] at h
  have hE : ∀ K : ℝ, Cb ≤ K → Real.exp (Cb * τ) ≤ Real.exp (K * τ) := fun K hK' =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hK' hτ0)
  have hEC : Real.exp (Cb * τ) ≤ Real.exp ((C + max Cb 0) * τ) := hE _ (by linarith [le_max_left Cb 0])
  have hEM : Real.exp (Cb * τ) ≤ Real.exp (max Cb 0 * τ) := hE _ (le_max_left Cb 0)
  have hLip : ∀ x y, ‖Ψ τ x - Ψ τ y‖ ≤ Real.exp (Cb * τ) * ‖x - y‖ := fun x y =>
    HRS.MS.FlowA.flow_lipschitz hT hbD hΨA τ hτ x y
  have hLipI : ∀ x y, ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ ≤ Real.exp (Cb * τ) * ‖x - y‖ := by
    intro x y
    rw [hinv x, hinv y]
    exact hΦL x y
  have hLipM : ∀ x y, ‖Ψ τ x - Ψ τ y‖ ≤ Real.exp (max Cb 0 * τ) * ‖x - y‖ := fun x y =>
    (hLip x y).trans (mul_le_mul_of_nonneg_right hEM (norm_nonneg _))
  have hLipIM : ∀ x y, ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ ≤ Real.exp (max Cb 0 * τ) * ‖x - y‖ :=
    fun x y => (hLipI x y).trans (mul_le_mul_of_nonneg_right hEM (norm_nonneg _))
  obtain ⟨hsepIII, -⟩ := hsep Ψ (fun τ' => Function.invFun (Ψ τ')) τ hτ0
    (fun x => Function.leftInverse_invFun hbij.1 x)
    (fun y => Function.rightInverse_invFun hbij.2 y) hLipIM hLipM
  refine ⟨fun x y => (hLip x y).trans (mul_le_mul_of_nonneg_right hEC (norm_nonneg _)),
    fun x y => (hLipI x y).trans (mul_le_mul_of_nonneg_right hEC (norm_nonneg _)), ?_⟩
  intro z x y hx hy
  have h := hsepIII z x y hx hy
  have hm : Real.exp (-((C + max Cb 0) * τ)) ≤ Real.exp (-(C * τ)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (le_max_right Cb 0) hτ0])
  linarith

end HRS.MH.Screened
