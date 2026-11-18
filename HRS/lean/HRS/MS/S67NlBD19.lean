import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovBridgeAux6
import HRS.MS.MovBridgeAux7
import HRS.MS.MovOscAux2
import HRS.MS.S67NlBD03
import HRS.MS.S67NlBD04
import HRS.MS.S67NlBD13
import HRS.MS.S67NlBD14B
import HRS.MS.S67NlBD17

/-!
# S6.7nl.19: far transport through a genuine bounded smooth multiplier
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
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

/-- S6.7nl.19: the far transport `far(sqrt(rho0) v) * W_i psi` lowers the index to `σ - movA`. -/
theorem s67bd_transport_far (H : Mov2dTh d s β q ρ₀) (m : ℕ) (σ : ℝ)
    (hσ : 2 ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ψ : Euc d → ℝ,
      MemOsc (m : ℝ) v → ContDiff ℝ 1 ψ → MemOsc σ ψ →
      (∀ i : Fin d, MemLp (s67bd_D i ψ) 2 volume) → ∀ i : Fin d,
      MemOsc (σ - movA d s) (fun x =>
        s67bd_far d s (fun y => Real.sqrt (ρ₀ y) * v y) i x * s67bd_W ρ₀ i ψ x) ∧
      oscNorm (σ - movA d s) (fun x =>
        s67bd_far d s (fun y => Real.sqrt (ρ₀ y) * v y) i x * s67bd_W ρ₀ i ψ x) ≤
        C * oscNorm (m : ℝ) v * oscNorm σ ψ := by
  obtain ⟨CW, hCW0, hW⟩ := s67bd_weighted_derivative H σ hσ
  obtain ⟨CB, hCB0, hCB⟩ := mo_mult_cb (d := d) (σ - 1) ⌈|σ - 1|⌉₊ (Nat.le_ceil _)
  choose Cf hCf0 hCf using fun n : ℕ => s67bd_far_force_coefficients H m n
  refine ⟨CB * Cf ⌈|σ - 1|⌉₊ * CW,
    mul_nonneg (mul_nonneg hCB0 (hCf0 _)) hCW0, fun v ψ hv hψ1 hψ hD i => ?_⟩
  obtain ⟨hWm, hWn⟩ := hW ψ hψ1 hψ hD i
  obtain ⟨hFc, hFb, -⟩ := hCf ⌈|σ - 1|⌉₊ v hv i
  have hA0 : 0 ≤ Cf ⌈|σ - 1|⌉₊ * oscNorm (m : ℝ) v :=
    mul_nonneg (hCf0 _) (by unfold oscNorm; exact Real.sqrt_nonneg _)
  have hFQ : mova3b2_Q ⌈|σ - 1|⌉₊ 0 (Cf ⌈|σ - 1|⌉₊ * oscNorm (m : ℝ) v)
      (fun z => s67bd_far d s (fun y => Real.sqrt (ρ₀ y) * v y) i z) := by
    refine mova3b2_Q_of_iter hFc fun k hk x => ?_
    rw [pow_zero, mul_one]
    exact hFb k hk x
  have hFtg : (fun z => s67bd_far d s (fun y => Real.sqrt (ρ₀ y) * v y) i z).HasTemperateGrowth := by
    refine ⟨hFc, fun n => ?_⟩
    obtain ⟨-, hbn, -⟩ := hCf n v hv i
    refine ⟨0, Cf n * oscNorm (m : ℝ) v, fun x => ?_⟩
    rw [pow_zero, mul_one]
    exact hbn n le_rfl x
  obtain ⟨hM1, hM2⟩ := hCB _ hA0 (fun z => s67bd_far d s (fun y => Real.sqrt (ρ₀ y) * v y) i z)
    hFtg hFQ (s67bd_W ρ₀ i ψ) hWm
  have hmov : σ - movA d s ≤ σ - 1 := by
    have h1 : (1 : ℝ) ≤ movA d s := le_max_left _ _
    linarith
  obtain ⟨hO1, hO2⟩ := mo_mono hmov hM1
  refine ⟨hO1, hO2.trans ?_⟩
  calc oscNorm (σ - 1) (fun x => s67bd_far d s (fun y => Real.sqrt (ρ₀ y) * v y) i x *
        s67bd_W ρ₀ i ψ x)
      ≤ CB * (Cf ⌈|σ - 1|⌉₊ * oscNorm (m : ℝ) v) * oscNorm (σ - 1) (s67bd_W ρ₀ i ψ) := hM2
    _ ≤ CB * (Cf ⌈|σ - 1|⌉₊ * oscNorm (m : ℝ) v) * (CW * oscNorm σ ψ) :=
        mul_le_mul_of_nonneg_left hWn (mul_nonneg hCB0 hA0)
    _ = CB * Cf ⌈|σ - 1|⌉₊ * CW * oscNorm (m : ℝ) v * oscNorm σ ψ := by ring

end HRS.MS.BreakdownS67
