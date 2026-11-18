import HRS.ME.ParxUPx4b2
import HRS.ME.ParxUPx4bK2
import HRS.Equilibrium.Parametrix.Packets

/-!
# Packet P3c (part 2): uniform `px4b_Ps_class`

Uniform version (constant chosen before `β, V, ρ`, through the bundle `ParxU`) of
`HRS.Parx.px4b_Ps_class` (Packets:1002).  The packet proof uses `px4b_aa_class`, `px4b_N_class`,
`px4b_cN_class` and `px4b_Sm_class` (the last one has an explicit constant `|β⁻¹/2| · d · cbNorm a`,
bounded by `|νp|/2`).  The uniform ingredients are `px4b_aa_class_unif` and `px4b_N_class_unif`
(ParxUPx4b1) and `px4b_cN_class_unif` (ParxUPx4bK2, which needs `0 < s` through `jop_engine_unif`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- **Uniform version of `px4b_Ps_class`.** The constant depends only on `(d, s, N, νm, νp, c₀, Λ₀)`
and `(σ, b, m)` and on the parameter facts `2 ≤ d`, `0 < s < d`, `m ≤ N`; it is chosen before
`β, V, ρ`. -/
theorem px4b_Ps_class_unif (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {σ : ℝ} (hσ : σ ≤ s)
    (b m : ℕ) (hm : 2 ≤ m) (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B → Conormal σ b m B F →
      ConormalL (σ - 1) (fun _ => b + 3) (m - 2) (C * B)
        (fun x y => px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y -
          px4b_cN d s V β ρ (newtonOp d β ρ F) y -
          px4b_cN d s V β ρ (swapK (newtonOp d β ρ F)) x) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  obtain ⟨CA, hCA0, hCA⟩ := px4b_aa_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hsd hσ b (n + 2) hN
  obtain ⟨C1, hC10, hC1⟩ := px4b_N_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hsd hσ b (n + 2) hN
  have hτ : (σ - 2) + 2 < d := by linarith
  obtain ⟨Cc, hCc0, hCc⟩ := px4b_cN_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hs0 hsd (τ := σ - 2) hτ (b + 1) (n + 2) hm hN
  refine ⟨|νp| / 2 * ((d : ℝ) * CA + (d : ℝ) * CA) + Cc * C1 + Cc * C1, by positivity,
    fun β V ρ U B F hB hF => ?_⟩
  have hbinv : |β⁻¹| ≤ |νp| := abs_beta_inv_le_of U
  obtain ⟨hA1, hA2, hA3, hA4⟩ := hCA β V ρ U B F hB hF
  have hAn : Torus.IsCk (((n + 2 : ℕ)) : WithTop ℕ∞) (px4b_aF d β ρ F) := hA1
  have hA'n : Torus.IsCk (((n + 2 : ℕ)) : WithTop ℕ∞) (px4b_a'F d β ρ F) := hA3
  have hN1 := hC1 β V ρ U B F hB hF
  have hB1 : 0 ≤ C1 * B := mul_nonneg hC10 hB
  have c1 := PDE.cbNorm_nonneg'C (n + 2) (px4b_aF d β ρ F)
  have c2 := PDE.cbNorm_nonneg'C (n + 2) (px4b_a'F d β ρ F)
  have hν : 0 ≤ |β⁻¹ / 2| := abs_nonneg _
  have hSm := px4b_Sm_class β⁻¹ (σ - 1) (fun _ => b + 3) hAn hA'n
  have hSm' : ConormalL (σ - 1) (fun _ => b + 3) n
      (|β⁻¹ / 2| * ((d : ℝ) * (CA * B) + (d : ℝ) * (CA * B)))
      (px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F)) :=
    conormalL_mono_B hSm (mul_nonneg hν (add_nonneg (mul_nonneg (Nat.cast_nonneg _) c1)
      (mul_nonneg (Nat.cast_nonneg _) c2)))
      (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hA2 (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hA4 (Nat.cast_nonneg _))) hν)
  obtain ⟨hc1, hc2⟩ := hCc β V ρ U (C1 * B) _ hB1 hN1
  obtain ⟨hc3, hc4⟩ := hCc β V ρ U (C1 * B) _ hB1 (conormalL_swap hN1)
  have k1 : ConormalL (σ - 1) (fun _ => b + 3) n (Cc * (C1 * B))
      (fun _ y => px4b_cN d s V β ρ (newtonOp d β ρ F) y) :=
    conormalL_mono_B (px4b_conormal_snd (σ - 1) (fun _ => b + 3) hc1)
      (PDE.cbNorm_nonneg'C _ _) hc2
  have k2 : ConormalL (σ - 1) (fun _ => b + 3) n (Cc * (C1 * B))
      (fun x _ => px4b_cN d s V β ρ (swapK (newtonOp d β ρ F)) x) :=
    conormalL_mono_B (px4b_conormal_fst (σ - 1) (fun _ => b + 3) hc3)
      (PDE.cbNorm_nonneg'C _ _) hc4
  have e : (fun x y => px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y -
          px4b_cN d s V β ρ (newtonOp d β ρ F) y -
          px4b_cN d s V β ρ (swapK (newtonOp d β ρ F)) x) =
      fun x y => (px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y +
          (-1 : ℝ) * px4b_cN d s V β ρ (newtonOp d β ρ F) y) +
          (-1 : ℝ) * px4b_cN d s V β ρ (swapK (newtonOp d β ρ F)) x := by
    funext x y; ring
  rw [e]
  have h3 := conormalL_add (conormalL_add hSm' (ConormalL.smul k1 (-1))) (ConormalL.smul k2 (-1))
  refine conormalL_mono_B h3 (by positivity) ?_
  -- the `β`-dependent factor `|β⁻¹ / 2|` is bounded by `|νp| / 2`
  have hb2 : |β⁻¹ / 2| ≤ |νp| / 2 := by
    rw [abs_div, abs_two]
    linarith
  have hY : 0 ≤ (d : ℝ) * (CA * B) + (d : ℝ) * (CA * B) := by positivity
  have hbz := mul_le_mul_of_nonneg_right hb2 hY
  rw [abs_neg, abs_one]
  nlinarith [hbz]

end HRS.ME.ParxU

end
