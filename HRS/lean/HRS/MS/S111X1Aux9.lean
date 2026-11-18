import HRS.MS.S111X1Aux8

/-!
# S11.1 X1, part 9: `S111CovCore` from the analytic input
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ} {s a β γ : ℝ} {ρ : Euc d → ℝ}

theorem x1_toLp_norm {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  have h : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
    simp [sq]
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

theorem X1Input.F_add (h : X1Input d s a β γ ρ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    {φ ψ₁ ψ₂ : Euc d → ℝ} (hφ : IsOscTest (wholeSpaceIndex d : ℝ) φ)
    (h₁ : IsOscTest (wholeSpaceIndex d : ℝ) ψ₁) (h₂ : IsOscTest (wholeSpaceIndex d : ℝ) ψ₂) :
    Fcov d s a β γ ρ r t φ (ψ₁ + ψ₂) = Fcov d s a β γ ρ r t φ ψ₁ + Fcov d s a β γ ρ r t φ ψ₂ := by
  have := h.F_lin hr ht hφ h₁ h₂ 1
  simp only [one_mul] at this
  exact this

theorem X1Input.F_zero (h : X1Input d s a β γ ρ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    {φ : Euc d → ℝ} (hφ : IsOscTest (wholeSpaceIndex d : ℝ) φ) :
    Fcov d s a β γ ρ r t φ 0 = 0 := by
  have h0 : IsOscTest (wholeSpaceIndex d : ℝ) (0 : Euc d → ℝ) := (oscSub d (wholeSpaceIndex d : ℝ)).zero_mem
  have := h.F_add hr ht hφ h0 h0
  rw [add_zero] at this
  linarith

theorem X1Input.F_smul (h : X1Input d s a β γ ρ) {r t : ℝ} (hr : 0 ≤ r) (ht : 0 ≤ t)
    {φ ψ : Euc d → ℝ} (hφ : IsOscTest (wholeSpaceIndex d : ℝ) φ)
    (hψ : IsOscTest (wholeSpaceIndex d : ℝ) ψ) (c : ℝ) :
    Fcov d s a β γ ρ r t φ (c • ψ) = c * Fcov d s a β γ ρ r t φ ψ := by
  have h0 : IsOscTest (wholeSpaceIndex d : ℝ) (0 : Euc d → ℝ) := (oscSub d (wholeSpaceIndex d : ℝ)).zero_mem
  have := h.F_lin hr ht hφ h0 hψ c
  rw [h.F_zero hr ht hφ, zero_add] at this
  have e : (c • ψ) = (fun x => (0 : Euc d → ℝ) x + c * ψ x) := by
    funext x; simp
  rw [e]
  exact this

theorem x1_core_of_input (h : X1Input d s a β γ ρ) :
    HRS.MS.S111BD.S111CovCore d s a β γ ρ := by
  haveI := h.finite
  obtain ⟨M, hM⟩ := h.bdd
  set m : ℝ := (wholeSpaceIndex d : ℝ) with hm
  have hS : ∀ ψ ∈ oscSub d m, MemLp ψ 2 (HRS.Whole.withDensityReal ρ) :=
    fun ψ hψ => x1_osc_memLp h.meas h.nonneg hM hψ
  refine ⟨oscSub d m, hS, h.meas, h.pos, fun ψ hψ => hψ, ?_⟩
  intro r hr t ht φ hφ
  obtain ⟨B, hB0, hB⟩ := h.F_bound hr ht hφ
  let ℓ : oscSub d m →ₗ[ℝ] ℝ :=
    { toFun := fun ψ => Fcov d s a β γ ρ r t φ ψ
      map_add' := fun ψ₁ ψ₂ => h.F_add hr ht hφ ψ₁.2 ψ₂.2
      map_smul' := fun c ψ => h.F_smul hr ht hφ ψ.2 c }
  refine ⟨ℓ, B, hB0, fun ψ => ?_, fun ψ => rfl⟩
  have e : ‖HRS.MS.TensRel.s111_toLp (oscSub d m) hS ψ‖ =
      Real.sqrt (∫ x, (ψ : Euc d → ℝ) x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) :=
    x1_toLp_norm (hS ψ ψ.2)
  rw [e]
  exact hB ψ ψ.2

end HRS.MS.S111X1
