import HRS.MC.L2C4Aux1

/-!
# Packet L2C-4, helper 2: the frozen classical solution and time-homogeneity

For `t > 0` and smooth `φ` the frozen adjoint propagator on `[0,t]` is a classical adjoint solution `F`,
`F r = Ū^{r,t}φ`, and `F v = Ū^{0,t-v}φ` for `0 ≤ v < t` (`MFSemigroup.propagator_frozen_eq`).
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear

namespace HRS.MC.L2C4

variable {d : ℕ}

theorem l2c4_frozen_classical (R : Regime d) {t : ℝ} (ht : 0 < t) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) :
    ∃ F : ℝ → Torus d → ℝ, IsClassicalAdjointSolution R.D (fun _ => R.ρβ) t φ F ∧
      (∀ r ∈ Set.Icc 0 t, propagator R.D (fun _ => R.ρβ) r t φ = F r) ∧
      ∀ v ∈ Set.Ico (0 : ℝ) t, F v = propagator R.D (fun _ => R.ρβ) 0 (t - v) φ := by
  have hd1 : 1 ≤ d := by have := R.hd; omega
  have hν : 0 < R.D.invβ := by rw [R.hDβ]; exact inv_pos.2 R.hβ
  obtain ⟨hprob', hreg', hcont'⟩ := HRS.MC.L2C0.l2c0_frozen_hyps R
  have hA := HRS.MC.L2C0.l2c0_adjointData_generic R.D R.hM R.hV hν (fun _ => R.ρβ) hprob' hreg' hcont'
  have hm1 : 1 ≤ mStar d := by have := ClassicalPart.three_le_mStar d; omega
  obtain ⟨Rg, MB, Λ, VB, ν₀, hAD⟩ := hA (mStar d) hm1 t ht
  obtain ⟨C, Cs, -, -, hmain⟩ := adjoint_torus_classical hd1 R.D.s R.D.hs0 R.D.hsd (mStar d) le_rfl
    Rg MB Λ VB
  have hφc : Continuous φ := continuous_of_isSmooth hφ
  obtain ⟨h1, h2, -⟩ := hmain R.D ν₀ t (fun _ => R.ρβ) hAD t ⟨ht, le_rfl⟩ φ hφc
    (MFSemigroup.memSobolev_of_isSmooth hφ _)
  refine ⟨_, h1, h2, fun v hv => ?_⟩
  have := MFSemigroup.propagator_frozen_eq R.hd R.D.s R.D.hs0 R.D.hsd (mStar d) hm1 Rg MB Λ VB R.D ν₀ t
    R.ρβ hAD (T' := t) ⟨ht, le_rfl⟩ h1 (τ := t - v) ⟨by linarith [hv.2], by linarith [hv.1]⟩
  rw [this]
  congr 1
  ring

end HRS.MC.L2C4
