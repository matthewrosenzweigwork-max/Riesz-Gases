import HRS.Equilibrium.Parametrix.PX3aAuxU

/-!
# Packet PX3a auxiliaries V: the Newton map `𝒩` (no symmetry)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

theorem px3a_newton_map_general (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {β : ℝ}
    (hβ : 0 < β) {σ : ℝ} (hσ : σ < d) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 2) (fun c => b + if σ - 2 + (c : ℝ) = 0 then 1 else 0) m (C * B)
        (newtonOp d β ρ F) := by
  obtain ⟨Cn, hCn0, hCn⟩ := newton_ofChart_general hd (ν := β⁻¹) (inv_pos.mpr hβ) hσ b m
  obtain ⟨Cc, hCc0, hCc⟩ := canonical_conormal hd hρ (σ := σ - 2) (by linarith) (b + 1) m
  refine ⟨Cc * Cn, mul_nonneg hCc0 hCn0, fun B F hB hF => ?_⟩
  have hN := hCn B F hB hF
  have hcc := hCc (fun c => b + if σ - 2 + (c : ℝ) = 0 then 1 else 0)
    (fun c => by split_ifs <;> omega) (Cn * B) _ (mul_nonneg hCn0 hB) hN
  rw [← mul_assoc] at hcc
  refine conormalL_congr_offDiag (fun x y hxy => ?_) hcc
  unfold newtonOp
  rw [if_neg hxy]

end HRS.Parx

end
