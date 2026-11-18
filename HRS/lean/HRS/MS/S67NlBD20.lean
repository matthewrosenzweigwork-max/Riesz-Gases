import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD03
import HRS.MS.S67NlBD08
import HRS.MS.S67NlBD12
import HRS.MS.S67NlBD13

/-!
# S6.7nl.20: nonlocal product source in `L¹` and `H^{σ-1}`

`s67bd_product_source`.  Route: packet 13 puts `W_i ψ` in `Σ^{σ-1}`; packet 12 (`b = m`, `r = σ-1`) puts
`v W_i ψ` in `Σ^{σ-1}`; packet 08 converts to `H^{σ-1}`; the `L¹` part is `L²` Cauchy-Schwarz with
`‖·‖_{L²} = ‖·‖_{Σ^0} ≤ ‖·‖_{Σ^t}`, independent of the Sobolev estimate.
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

/-- `L²` Cauchy-Schwarz in the form `∫ |f g| ≤ ‖f‖_{Σ^0} ‖g‖_{Σ^0}`. -/
theorem s67bd20_l1 {f g : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (hg : MemLp g 2 (volume : Measure (Euc d))) :
    Integrable (fun x => f x * g x) volume ∧ ∫ x, |f x * g x| ≤ oscNorm 0 f * oscNorm 0 g := by
  refine ⟨hf.integrable_mul hg, ?_⟩
  have e2 : ENNReal.ofReal 2 = 2 := by simp
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := (volume : Measure (Euc d))) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (by rw [e2]; exact hf) (by rw [e2]; exact hg)
  have e1 : ∫ x, |f x * g x| = ∫ x, ‖f x‖ * ‖g x‖ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [abs_mul]
  have e3 : ∀ h : Euc d → ℝ, (∫ x, ‖h x‖ ^ (2 : ℝ)) = ∫ x, h x ^ 2 := fun h =>
    integral_congr_ae (Eventually.of_forall fun x => by simp [Real.rpow_two, sq_abs])
  rw [e1, oscNorm_zero f hf, oscNorm_zero g hg, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [e3, e3] at h
  simpa using h

theorem s67bd_product_source (H : Mov2dTh d s β q ρ₀) (m : ℕ) (σ : ℝ)
    (hm : (d : ℝ) / 2 + 7 < m) (hσ : 2 ≤ σ) (hσm : σ + 4 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ψ : Euc d → ℝ,
      MemOsc (m : ℝ) v → ContDiff ℝ 1 ψ → MemOsc σ ψ →
      (∀ i : Fin d, MemLp (s67bd_D i ψ) 2 volume) → ∀ i : Fin d,
      Integrable (fun x => v x * s67bd_W ρ₀ i ψ x) volume ∧
      HRS.PDE.ToolboxRd.MemSobolev (σ - 1) (fun x => v x * s67bd_W ρ₀ i ψ x) ∧
      (∫ x, |v x * s67bd_W ρ₀ i ψ x|) +
        s67bd_Hnorm (σ - 1) (fun x => v x * s67bd_W ρ₀ i ψ x) ≤
          C * oscNorm (m : ℝ) v * oscNorm σ ψ := by
  have hr0 : 0 ≤ σ - 1 := by linarith
  have hdm : (d : ℝ) / 2 < (m : ℝ) := by linarith [show (0 : ℝ) ≤ 7 by norm_num]
  obtain ⟨C13, hC13, h13⟩ := s67bd_weighted_derivative H σ hσ
  obtain ⟨C12, hC12, h12⟩ := s67bd_product_real d (m : ℝ) (σ - 1) hdm hr0 (by linarith)
  obtain ⟨C8, hC8, h8⟩ := s67bd_osc_sobolev d (σ - 1) hr0
  refine ⟨(1 + C8 * C12) * C13, by positivity, fun v ψ hv hψ1 hψ hD i => ?_⟩
  obtain ⟨hW, hWn⟩ := h13 ψ hψ1 hψ hD i
  obtain ⟨hP, hPn⟩ := h12 v (s67bd_W ρ₀ i ψ) hv hW
  obtain ⟨hS, hSn⟩ := h8 _ hP
  have hv0 := mo_mono (Nat.cast_nonneg m) hv
  have hW0 := mo_mono hr0 hW
  obtain ⟨hI, hIn⟩ := s67bd20_l1 hv.1 hW.1
  have ov : 0 ≤ oscNorm (m : ℝ) v := Real.sqrt_nonneg _
  have oW : 0 ≤ oscNorm (σ - 1) (s67bd_W ρ₀ i ψ) := Real.sqrt_nonneg _
  have oψ : 0 ≤ oscNorm σ ψ := Real.sqrt_nonneg _
  have hL1 : ∫ x, |v x * s67bd_W ρ₀ i ψ x| ≤
      oscNorm (m : ℝ) v * oscNorm (σ - 1) (s67bd_W ρ₀ i ψ) :=
    hIn.trans (mul_le_mul hv0.2 hW0.2 (Real.sqrt_nonneg _) ov)
  refine ⟨hI, hS, ?_⟩
  have hH : s67bd_Hnorm (σ - 1) (fun x => v x * s67bd_W ρ₀ i ψ x) ≤
      C8 * (C12 * oscNorm (m : ℝ) v * oscNorm (σ - 1) (s67bd_W ρ₀ i ψ)) :=
    hSn.trans (mul_le_mul_of_nonneg_left hPn hC8)
  have hWb : oscNorm (σ - 1) (s67bd_W ρ₀ i ψ) ≤ C13 * oscNorm σ ψ := hWn
  have hprod : oscNorm (m : ℝ) v * oscNorm (σ - 1) (s67bd_W ρ₀ i ψ) ≤
      oscNorm (m : ℝ) v * (C13 * oscNorm σ ψ) := mul_le_mul_of_nonneg_left hWb ov
  have hpos : 0 ≤ oscNorm (m : ℝ) v * oscNorm (σ - 1) (s67bd_W ρ₀ i ψ) := mul_nonneg ov oW
  calc (∫ x, |v x * s67bd_W ρ₀ i ψ x|) +
        s67bd_Hnorm (σ - 1) (fun x => v x * s67bd_W ρ₀ i ψ x)
      ≤ oscNorm (m : ℝ) v * oscNorm (σ - 1) (s67bd_W ρ₀ i ψ) +
        C8 * C12 * (oscNorm (m : ℝ) v * oscNorm (σ - 1) (s67bd_W ρ₀ i ψ)) := by
        refine add_le_add hL1 (hH.trans (le_of_eq ?_)); ring
    _ = (1 + C8 * C12) * (oscNorm (m : ℝ) v * oscNorm (σ - 1) (s67bd_W ρ₀ i ψ)) := by ring
    _ ≤ (1 + C8 * C12) * (oscNorm (m : ℝ) v * (C13 * oscNorm σ ψ)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by ring

end HRS.MS.BreakdownS67
