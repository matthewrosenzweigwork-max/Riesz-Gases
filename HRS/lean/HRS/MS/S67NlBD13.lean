import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovAdjAux12
import HRS.MS.MovOscAux5
import HRS.MS.MovBridgeAux7
import HRS.MS.MovThermAux2
import HRS.MS.S67NlBD03

/-!
# S6.7 nonlinear breakdown, packet 13: weighted first derivative at one lower oscillator level

`s67bd_weighted_derivative`: `W_i ψ = ∂_i ψ + (βq/2) x_i ψ - (1/2) B_i ψ` with `∇ log ρ₀ = -(βq) x + B`,
`B ∈ C_b^∞`.  The three terms are bounded `Σ^σ → Σ^{σ-1}` by `s67_partial_osc`, `s67_xmul_osc` and `mo_mult_cb`.
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

/-- Conjugated gradient component W_i ψ. -/
def s67bd_W (ρ₀ : Euc d → ℝ) (i : Fin d) (ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  s67bd_D i ψ x - s67bd_D i (fun y => Real.log (ρ₀ y)) x * ψ x / 2

theorem s67bd_weighted_derivative (H : Mov2dTh d s β q ρ₀) (σ : ℝ) (hσ : 2 ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ : Euc d → ℝ, ContDiff ℝ 1 ψ → MemOsc σ ψ →
      (∀ i : Fin d, MemLp (s67bd_D i ψ) 2 volume) → ∀ i : Fin d,
      MemOsc (σ - 1) (s67bd_W ρ₀ i ψ) ∧
      oscNorm (σ - 1) (s67bd_W ρ₀ i ψ) ≤ C * oscNorm σ ψ := by
  obtain ⟨B, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  set q' : ℝ := β * q with hq'
  set r : ℝ := σ - 1 with hr
  have hr1 : r + 1 = σ := by rw [hr]; ring
  -- the bounded multiplier `B_i`
  set N : ℕ := ⌈|r|⌉₊ with hN
  have hrN : |r| ≤ N := Nat.le_ceil _
  obtain ⟨CB, hCB0, hCB⟩ := mo_mult_cb (d := d) r N hrN
  obtain ⟨Mb, hMb⟩ := hR.cb N
  have hBtg : B.HasTemperateGrowth := HRS.MS.Mov0.mov0_B_tg hR
  set A : ℝ := max Mb 0 with hA
  have hA0 : 0 ≤ A := le_max_right _ _
  have hbtg : ∀ i : Fin d, (fun x => B x i).HasTemperateGrowth := by
    intro i
    exact (ContinuousLinearMap.hasTemperateGrowth (EuclideanSpace.proj (𝕜 := ℝ) i : Euc d →L[ℝ] ℝ)).comp hBtg
  have hbQ : ∀ i : Fin d, mova3b2_Q N 0 A (fun x => B x i) := by
    intro i
    have hbs : ContDiff ℝ ∞ (fun x => B x i) := (hbtg i).1
    refine mova3b2_Q_of_iter hbs fun k hk x => ?_
    have hBk : ContDiffAt ℝ k B x := (hMb.1.of_le (by exact_mod_cast hk)).contDiffAt
    have h1 := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
      (EuclideanSpace.proj (𝕜 := ℝ) i : Euc d →L[ℝ] ℝ) hBk (x := x) (n := k) (by exact_mod_cast le_rfl)
    have h2 : ‖(EuclideanSpace.proj (𝕜 := ℝ) i : Euc d →L[ℝ] ℝ)‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
      simpa using PiLp.norm_apply_le v i
    have h3 : ‖iteratedFDeriv ℝ k (fun x => B x i) x‖ ≤ ‖iteratedFDeriv ℝ k B x‖ := by
      have e : (fun x => B x i) = (EuclideanSpace.proj (𝕜 := ℝ) i : Euc d →L[ℝ] ℝ) ∘ B := rfl
      rw [e]
      exact h1.trans (by
        calc _ ≤ 1 * ‖iteratedFDeriv ℝ k B x‖ :=
              mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
          _ = _ := one_mul _)
    have h4 := hMb.2 k hk x
    simp only [pow_zero, mul_one]
    exact h3.trans (h4.trans (le_max_left _ _))
  refine ⟨Real.sqrt (2 ^ |σ|) + |q' / 2| * Real.sqrt (2 ^ |σ|) + |(-1 : ℝ) / 2| * (CB * A),
    by positivity, fun ψ hψ1 hψ hD i => ?_⟩
  have hψ' : MemOsc (r + 1) ψ := by rw [hr1]; exact hψ
  have hψr : MemOsc r ψ ∧ oscNorm r ψ ≤ oscNorm σ ψ := mo_mono (by rw [hr]; linarith) hψ
  have hψ1' : MemOsc 1 ψ := (mo_mono (by linarith) hψ).1
  -- the three pieces
  obtain ⟨hP1, hP2⟩ := s67_partial_osc i r hψ' hψ1 (hD i)
  have hxL := mo_xmul_ext_memLp hψ1' i
  obtain ⟨hX1, hX2⟩ := s67_xmul_osc i r hψ' hxL
  obtain ⟨hM1, hM2⟩ := hCB A hA0 (fun x => B x i) (hbtg i) (hbQ i) ψ hψr.1
  -- identity for `W_i ψ`
  have hgrad : ∀ x, s67bd_D i (fun y => Real.log (ρ₀ y)) x = -q' * x i + B x i := by
    intro x
    unfold s67bd_D
    have h1 : fderiv ℝ (fun y => Real.log (ρ₀ y)) x (EuclideanSpace.single i (1 : ℝ)) =
        inner ℝ (gradient (fun y => Real.log (ρ₀ y)) x) (EuclideanSpace.single i (1 : ℝ)) := by
      rw [gradient, InnerProductSpace.toDual_symm_apply]
    rw [h1, HRS.MS.Mov0.mov0_grad_log hR x]
    simp [EuclideanSpace.inner_single_right]
  have hW : s67bd_W ρ₀ i ψ = fun x => (fun x => fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) x +
      ((fun x => (q' / 2) * (x i * ψ x)) x + (fun x => (-1 / 2) * (B x i * ψ x)) x) := by
    funext x
    unfold s67bd_W
    rw [hgrad x]
    unfold s67bd_D
    ring
  obtain ⟨hS1, hS2⟩ := HRS.MS.MovC1.movc1_osc_smul r (q' / 2) hX1
  obtain ⟨hT1, hT2⟩ := HRS.MS.MovC1.movc1_osc_smul r (-1 / 2) hM1
  obtain ⟨hU1, hU2⟩ := HRS.MS.MovC1.movc1_osc_add r hS1 hT1
  obtain ⟨hV1, hV2⟩ := HRS.MS.MovC1.movc1_osc_add r hP1 hU1
  rw [hW]
  refine ⟨hV1, hV2.trans ?_⟩
  have e1 : oscNorm r (fun x => fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) ≤
      Real.sqrt (2 ^ |σ|) * oscNorm σ ψ := by rw [hr1] at hP2; exact hP2
  have e2 : oscNorm r (fun x => x i * ψ x) ≤ Real.sqrt (2 ^ |σ|) * oscNorm σ ψ := by
    rw [hr1] at hX2; exact hX2
  have e3 : oscNorm r (fun x => B x i * ψ x) ≤ CB * A * oscNorm σ ψ :=
    hM2.trans (mul_le_mul_of_nonneg_left hψr.2 (mul_nonneg hCB0 hA0))
  have hU : oscNorm r (fun x => (q' / 2) * (x i * ψ x) + (-1 / 2) * (B x i * ψ x)) ≤
      |q' / 2| * (Real.sqrt (2 ^ |σ|) * oscNorm σ ψ) +
        |(-1 : ℝ) / 2| * (CB * A * oscNorm σ ψ) := by
    refine hU2.trans ?_
    rw [hS2, hT2]
    exact add_le_add (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
      (mul_le_mul_of_nonneg_left e3 (abs_nonneg _))
  calc _ ≤ oscNorm r (fun x => fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ))) +
        oscNorm r (fun x => (q' / 2) * (x i * ψ x) + (-1 / 2) * (B x i * ψ x)) := le_rfl
    _ ≤ _ := by nlinarith [hU, e1]

end HRS.MS.BreakdownS67
