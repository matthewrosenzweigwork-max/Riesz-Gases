import HRS.PDE.Uniqueness
import HRS.PDE.Hadamard
import HRS.PDE.KernelInputsD1

/-!
# `(r,Λ)`-regularity with and without the `s ≥ d-1` proviso (`B:eq:mf-regularity`, M L10082-10088)

`HRS.IsRegularMF` records only the bound `sup_t ‖μ^t‖_{C^r} ≤ Λ`; the printed definition adds, for `d-1 ≤ s < d`,
`sup_t ‖|∇|^{s-d} ∇μ^t‖_∞ ≤ Λ` (`HRS.PDE.IsRegularMFProviso`).  `docs/ISSUES.md` (Torus PDE layer, item 2) accepted the
shorter definition because the extra bound follows from `C^r` regularity with `r ≥ 1`.  This file proves that
implication: for `r ≥ 1` the two classes coincide up to a constant factor in the level `Λ`.

The proof is the bound `‖∇g * h‖_{C^0} ≤ C ‖h‖_{C^1}` for the cancellation convention (`convGradConv_cbNorm_of_one_le`
with `m = 0`) and `|∇|^{s-d}∇μ = c_{d,s}^{-1} ∇g * μ` (`HRS.PDE.fracForce`).
-/

noncomputable section

namespace HRS.MH.RegularMFBridge

open HRS HRS.PDE

variable {d : ℕ}

theorem cbNorm_nonneg' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) (φ : Torus d → E) :
    0 ≤ Torus.cbNorm k φ :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

/-- For `r ≥ 1` and `0 ≤ s < d`, `(r,Λ)`-regularity without the proviso implies `(r,CΛ)`-regularity with it, where `C ≥ 1`
depends only on `(d, s)`. -/
theorem isRegularMFProviso_of_isRegularMF (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {r : ℕ} (hr : 1 ≤ r) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Λ T : ℝ) (ρ : ℝ → Torus d → ℝ), 0 ≤ Λ → IsRegularMF r Λ T ρ →
      IsRegularMFProviso s r (C * Λ) T ρ := by
  obtain ⟨C0, hC0⟩ := convGradConv_cbNorm_of_one_le hd hs0 hsd 0
  have hrc : 0 < rieszConst d s := rieszConst_pos' hd hs0 hsd
  refine ⟨max 1 ((rieszConst d s)⁻¹ * |C0|), le_max_left _ _, fun Λ T ρ hΛ hreg => ?_⟩
  refine ⟨fun t ht => ⟨(hreg t ht).1, (hreg t ht).2.trans
    (le_mul_of_one_le_left hΛ (le_max_left _ _))⟩, fun _ t ht x => ?_⟩
  have h1 : Torus.IsCk 1 (ρ t) := by
    have := (hreg t ht).1
    unfold Torus.IsCk at this ⊢
    exact this.of_le (by exact_mod_cast hr)
  obtain ⟨-, hb⟩ := hC0 (ρ t) (by simpa using h1)
  have hcont := convGradConv_continuous_of_one_le hd hs0 hsd (ρ t) h1
  have hx := norm_le_cbNorm_zero _ hcont x
  have hmono : Torus.cbNorm 1 (ρ t) ≤ Torus.cbNorm r (ρ t) := cbNorm_monoU hr _
  have hΛt : Torus.cbNorm r (ρ t) ≤ Λ := (hreg t ht).2
  have hn1 : 0 ≤ Torus.cbNorm 1 (ρ t) := cbNorm_nonneg' _ _
  have hconv : ‖convGradConv (periodicRieszGrad d s) (ρ t) x‖ ≤ |C0| * Λ := by
    calc _ ≤ Torus.cbNorm 0 (convGradConv (periodicRieszGrad d s) (ρ t)) := hx
      _ ≤ C0 * Torus.cbNorm (0 + 1) (ρ t) := hb
      _ ≤ |C0| * Torus.cbNorm 1 (ρ t) := mul_le_mul_of_nonneg_right (le_abs_self _) hn1 |>.trans_eq' (by simp)
      _ ≤ |C0| * Λ := mul_le_mul_of_nonneg_left (hmono.trans hΛt) (abs_nonneg _)
  unfold fracForce
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hrc)]
  calc (rieszConst d s)⁻¹ * ‖convGradConv (periodicRieszGrad d s) (ρ t) x‖
      ≤ (rieszConst d s)⁻¹ * (|C0| * Λ) := mul_le_mul_of_nonneg_left hconv (inv_pos.2 hrc).le
    _ = ((rieszConst d s)⁻¹ * |C0|) * Λ := by ring
    _ ≤ max 1 ((rieszConst d s)⁻¹ * |C0|) * Λ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hΛ

/-- The converse is immediate: the proviso class at level `Λ` lies in the class without it at level `Λ`. -/
theorem isRegularMF_of_isRegularMFProviso {s : ℝ} {r : ℕ} {Λ T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : IsRegularMFProviso s r Λ T ρ) : IsRegularMF r Λ T ρ := h.1

end HRS.MH.RegularMFBridge
