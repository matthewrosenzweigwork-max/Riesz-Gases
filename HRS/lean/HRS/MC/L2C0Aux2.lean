import HRS.MC.L2C0Aux1
import HRS.PDE.MeanFieldWeak

/-!
# Packet L2C-0, part 2: `AdjointData` at every level for the Section 7 regime

Both density paths `ρ^t` (via the proved `Regime.reg`, `HRS.MC.RegSet.reg_proof`) and the frozen `ρ_β`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.PDE

namespace HRS.MC.L2C0

variable {d : ℕ}

/-- Generic assembly of the hypotheses of Proposition 3.9 at every level `m ≥ 1` and every horizon. -/
theorem l2c0_adjointData_generic (D : DynData d) (hM : D.M = -1) (hV : Torus.IsSmooth D.V)
    (hν : 0 < D.invβ) (μ : ℝ → Torus d → ℝ)
    (hprob : ∀ r : ℝ, 0 ≤ r → IsProbDensity (μ r))
    (hreg : ∀ j : ℕ, ∃ Λ : ℝ, ∀ T : ℝ, IsRegularMF j Λ T μ)
    (hcont : ∀ T : ℝ, ∀ ψ : Torus d → ℝ, Continuous ψ →
      ContinuousOn (fun r => ∫ x, ψ x * μ r x) (Set.Icc 0 T)) :
    ∀ m : ℕ, 1 ≤ m → ∀ T : ℝ, 0 < T → ∃ (R : PDE.Regime) (MB Λ VB ν₀ : ℝ),
      AdjointData D.s m R MB Λ VB D ν₀ T μ := by
  intro m _ T hT
  obtain ⟨R, hR⟩ : ∃ R : PDE.Regime, ∀ (M : Matrix (Fin d) (Fin d) ℝ) (invβ ν₀ T : ℝ)
      (μ : ℝ → Torus d → ℝ), 0 < ν₀ → ν₀ ≤ invβ → R.Holds d D.s M invβ ν₀ T μ := by
    rcases le_or_gt D.s ((d : ℝ) - 2) with h | h
    · exact ⟨.R1, fun _ _ _ _ _ _ _ => h⟩
    · exact ⟨.R3, fun _ _ _ _ _ h1 h2 => ⟨h, h1, h2⟩⟩
  obtain ⟨Λ, hΛ⟩ := hreg (m + 3)
  have hVm : Torus.IsCk (m + 3) D.V :=
    ClassicalAux.isCk_of_le (WithTop.coe_le_coe.2 le_top) hV
  refine ⟨R, 1, Λ, Torus.cbNorm (m + 3) D.V, D.invβ, rfl, ?_, ⟨hVm, le_rfl⟩, ?_, hT,
    hR _ _ _ _ _ hν le_rfl⟩
  · intro i k
    rw [hM, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> norm_num
  · refine ⟨fun r hr => hprob r hr.1, fun r hr => ?_, fun r hr => ?_, hcont T⟩
    · exact (hΛ T r hr).1
    · exact (hΛ T r hr).2
