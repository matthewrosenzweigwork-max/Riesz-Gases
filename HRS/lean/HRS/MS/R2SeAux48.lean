import HRS.MS.R2SeAux47
import HRS.MS.QsfAux3
import HRS.MC.E213TElem
import HRS.Energy.StaticLimitJoint
import HRS.Prob.Edgeworth

/-!
# S9.9 `r2_static_edgeworth`: the proof of the frozen statement

Worker S99, namespace `S99`.  `round2_static_edgeworth_proof : type_of% @HRS.Whole.r2_static_edgeworth`.
The `ℓ²` picture (`s99_main_l2`) is transported to `B_m` through the isometry `Ψ = s45_Psi`: `ζ_N = Ψ⁻¹ W_N`,
`G = G'∘Ψ`, `ℓ_x = Ψ⁻¹ ellv x`; the tensor `K` is the Bochner tensor `bochTensor3` of the bounded continuous map `x ↦ ℓ_x`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s99_coord_symm (m : ℕ) (e : ℕ ≃ MultiIndex d) (z : SeqL2) (α : MultiIndex d) :
    OscDual.coord ((s45_Psi (m : ℝ) e).symm z) α = SeqL2.coord z (e.symm α) := by
  have := s45_Psi_coord (m : ℝ) e ((s45_Psi (m : ℝ) e).symm z) (e.symm α)
  rw [LinearIsometryEquiv.apply_symm_apply] at this
  rw [this]; simp

theorem s99_ball_bd {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {Φ : B → ℝ}
    (hΦ : Φ ∈ HRS.CbUnitBall B 5) : ∀ i : ℕ, i ≤ 5 → ∀ z, ‖iteratedFDeriv ℝ i Φ z‖ ≤ 1 := by
  obtain ⟨-, hbdd, hcb⟩ := hΦ
  intro j hj z
  have hnn : ∀ j, 0 ≤ ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖ := fun j =>
    Real.iSup_nonneg fun _ => norm_nonneg _
  have h1 : ‖iteratedFDeriv ℝ j Φ z‖ ≤ ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖ :=
    le_ciSup (hbdd j (by omega)) z
  have h2 : ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖ ≤ HRS.cbNorm 5 Φ := by
    unfold HRS.cbNorm
    exact Finset.single_le_sum (f := fun j => ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖)
      (fun j _ => hnn j) (by simpa [Nat.lt_succ_iff] using hj)
  linarith

theorem s99_tensor_of_cont (μ : Measure (Euc d)) [IsProbabilityMeasure μ] {M : ℝ} {Y : Euc d → OscDual d M}
    (hcont : Continuous Y) {C : ℝ} (hC : ∀ x, ‖Y x‖ ≤ C) :
    ∃ K : HRS.projTensor (OscDual d M) 3, ∀ T : (OscDual d M) [×3]→L[ℝ] ℝ,
      (K : HRS.TensorDual (OscDual d M) 3) T = ∫ x, T ![Y x, Y x, Y x] ∂μ := by
  have hasm : AEStronglyMeasurable Y μ := hcont.aestronglyMeasurable
  have hint : Integrable (fun x => ‖Y x‖ * ‖Y x‖ * ‖Y x‖) μ := by
    refine Integrable.of_bound (C := C * C * C) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((hcont.norm.mul hcont.norm).mul hcont.norm).aestronglyMeasurable
    · have h0 : 0 ≤ ‖Y x‖ := norm_nonneg _
      have h1 := hC x
      have hC0 : 0 ≤ C := h0.trans h1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      gcongr
  refine ⟨⟨HRS.MC.E213T.bochTensor3 μ Y Y Y, HRS.MC.E213T.bochTensor3_mem hasm hasm hasm hint⟩, fun T => ?_⟩
  exact HRS.MC.E213T.bochTensor3_apply hasm hasm hasm hint T

end S99

end
