import HRS.ME.ParxUNewton1
import HRS.ME.ParxUConormal2
import HRS.Equilibrium.Parametrix.PX3aAuxAA

/-!
# Packet P2 (part 2): uniform Newton maps

Uniform versions (constants chosen before `β, V, ρ`, through the bundle `ParxU`) of
`HRS.Parx.newton_ofChart_sym`, `HRS.Parx.px3a_newton_map`, `HRS.Parx.px3a_newton_map_general`,
`HRS.Parx.newton_map`, `HRS.Parx.newton_map_general`.

The `β`-dependence of the chart is the scalar `1/(2β⁻¹)` (`ParxUNewton1`), bounded by `1/(2νm)`.
The `ρ`-dependence is only through the canonical projection, `canonical_conormal_unif`, which
needs `m ≤ N` (derivatives of `ρ` up to order `N`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- **Uniform version of `newton_ofChart_sym`.** The constant depends only on `(d, s, N, νm, νp,
c₀, Λ₀, σ, b, m)`; it is chosen before `β, V, ρ`. -/
theorem newton_ofChart_sym_unif (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → IsSymmPair F → Conormal σ b m B F →
      ConormalL (σ - 2) (fun c => b + if σ - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0) m (C * B)
        (ofChart (newtonChart d β⁻¹ (toChart F))) := by
  obtain ⟨Cs, hCs0, hCs⟩ := newton_ofChart_sym hd (ν := 1 / 2) (by norm_num) hσ b m
  refine ⟨Cs * (1 / (2 * max νm 0)), mul_nonneg hCs0
    (div_nonneg zero_le_one (mul_nonneg two_pos.le (le_max_right νm 0))),
    fun β V ρ U B F hB hsym hF => ?_⟩
  have hνm : 0 < νm := U.F.hνm
  rw [max_eq_left hνm.le]
  have hνb : νm ≤ β⁻¹ := U.beta_bounds.1
  exact conormalL_ofChart_newton_scale (C₀ := Cs) (B := B) F hνm hνb hCs0 hB
    (hCs B F hB hsym hF)

/-- **Uniform version of `px3a_newton_map`.** The constant depends only on `(d, s, N, νm, νp, c₀,
Λ₀, σ, b, m)`; `ρ` and `β` are chosen after it. -/
theorem px3a_newton_map_unif (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) (b m : ℕ) (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → IsSymmPair F → Conormal σ b m B F →
        ConormalL (σ - 2)
          (fun c => b + if σ - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0) m (C * B)
          (newtonOp d β ρ F) := by
  obtain ⟨Cn, hCn0, hCn⟩ := newton_ofChart_sym_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hσ b m
  obtain ⟨Cc, hCc0, hCc⟩ := canonical_conormal_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd (σ := σ - 2) (by linarith) (b + 1) m hN
  refine ⟨Cc * Cn, mul_nonneg hCc0 hCn0, fun β V ρ U B F hB hsym hF => ?_⟩
  have hN' := hCn β V ρ U B F hB hsym hF
  have hcc := hCc β V ρ U (fun c => b + if σ - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0)
    (fun c => by split_ifs <;> omega) (Cn * B) _ (mul_nonneg hCn0 hB) hN'
  rw [← mul_assoc] at hcc
  refine conormalL_congr_offDiag (fun x y hxy => ?_) hcc
  unfold newtonOp
  rw [if_neg hxy]

/-- **Uniform version of `px3a_newton_map_general`** (no symmetry; log power `b + 1` at every
resonance). The constant depends only on `(d, s, N, νm, νp, c₀, Λ₀, σ, b, m)`. -/
theorem px3a_newton_map_general_unif (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) (b m : ℕ) (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
        ConormalL (σ - 2)
          (fun c => b + if σ - 2 + (c : ℝ) = 0 then 1 else 0) m (C * B)
          (newtonOp d β ρ F) := by
  obtain ⟨Cn, hCn0, hCn⟩ := newton_ofChart_general_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hσ b m
  obtain ⟨Cc, hCc0, hCc⟩ := canonical_conormal_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd (σ := σ - 2) (by linarith) (b + 1) m hN
  refine ⟨Cc * Cn, mul_nonneg hCc0 hCn0, fun β V ρ U B F hB hF => ?_⟩
  have hN' := hCn β V ρ U B F hB hF
  have hcc := hCc β V ρ U (fun c => b + if σ - 2 + (c : ℝ) = 0 then 1 else 0)
    (fun c => by split_ifs <;> omega) (Cn * B) _ (mul_nonneg hCn0 hB) hN'
  rw [← mul_assoc] at hcc
  refine conormalL_congr_offDiag (fun x y hxy => ?_) hcc
  unfold newtonOp
  rw [if_neg hxy]

/-- **Uniform version of `newton_map`** (the Newton map of a symmetric conormal kernel). -/
theorem newton_map_unif (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) (b m : ℕ) (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → IsSymmPair F → Conormal σ b m B F →
        ConormalL (σ - 2)
          (fun c => b + if σ - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0) m (C * B)
          (newtonOp d β ρ F) :=
  px3a_newton_map_unif hd hσ b m hN

/-- **Uniform version of `newton_map_general`.** -/
theorem newton_map_general_unif (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) (b m : ℕ) (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
        ConormalL (σ - 2)
          (fun c => b + if σ - 2 + (c : ℝ) = 0 then 1 else 0) m (C * B)
          (newtonOp d β ρ F) :=
  px3a_newton_map_general_unif hd hσ b m hN

end HRS.ME.ParxU

end
