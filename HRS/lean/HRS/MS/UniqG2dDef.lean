import HRS.MS.UniqG2eB
import HRS.MS.UniqG2cB
import HRS.MS.UniqC2c
import HRS.MS.UniqC3e
import HRS.MS.FlowA
import HRS.MS.UniqM1Fin
import HRS.MH.ScreenedF1

/-!
# G2d, part 1: the auxiliary data (second cutoff, flow) for the final assembly

* `g2d_cutoffPair`: every `IsUlocCutoff χ` is the first half of an `IsCutoffPair χ χh`
  (`χh` a `ContDiffBump` with `rIn = 6`, `rOut = 7`).
* `g2d_flow`: for an `IsAdvectingDrift` on `[0,t]` there is a flow `Ψ` of `-b` with `bij`
  (`IsNegDriftFlow` of `AppendixBKernel`), from `FlowA.flow_exists` and `FlowA.flow_invertible`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff

namespace HRS.MS.UniqG2d

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-- The second cutoff `χh ∈ C_c^∞(B(0,8);[0,1])`, `= 1` on `B̄(0,6)`. -/
theorem g2d_cutoffPair {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) : ∃ χh : Euc d → ℝ, IsCutoffPair χ χh := by
  let f : ContDiffBump (0 : Euc d) := ⟨6, 7, by norm_num, by norm_num⟩
  refine ⟨fun x => f x, hχ, f.contDiff, f.hasCompactSupport, ?_, fun x => ⟨f.nonneg, f.le_one⟩,
    fun x hx => f.one_of_mem_closedBall (by simpa [f] using hx)⟩
  rw [show (fun x => f x) = (f : Euc d → ℝ) from rfl, f.tsupport_eq]
  intro x hx
  have : ‖x‖ ≤ 7 := by simpa [f] using hx
  simp only [mem_ball, dist_zero_right]
  linarith

/-- A flow of `-b` with the bijectivity clause, for an advecting drift on `[0,t]`. -/
theorem g2d_flow {m : ℕ} {Cb t : ℝ} (ht : 0 ≤ t) {b : ℝ → Euc d → Euc d}
    (hb : IsAdvectingDrift m Cb t b) : ∃ Ψ : ℝ → Euc d → Euc d, IsNegDriftFlow t b Ψ := by
  have hbD := HRS.MH.Screened.f1a_drift hb
  obtain ⟨Ψ, hΨ⟩ := HRS.MS.FlowA.flow_exists ht hbD
  refine ⟨Ψ, hΨ.init, hΨ.eqn, fun τ hτ => ?_⟩
  obtain ⟨Φ, h1, h2, -⟩ := HRS.MS.FlowA.flow_invertible ht hbD hΨ τ hτ
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

end HRS.MS.UniqG2d
