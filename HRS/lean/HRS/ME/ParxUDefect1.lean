import HRS.ME.ParxUPx4bZ1
import HRS.ME.ParxUPx4bZ2
import HRS.Equilibrium.Parametrix.Packets

/-!
# Packet P3d (part 1): uniform `defect_map`

Uniform version (constant chosen before `β, V, ρ`, through the bundle `ParxU`) of
`HRS.Parx.defect_map` (Packets:1111).  The packet proof combines the uniform classes
`px4b_N_class_unif`, `px4b_Zv_class_unif`, `px4b_Y1_class_unif`, `px4b_T1_class_unif`,
`px4b_J_class_unif`, `px4b_Ps_class_unif` with the constant-free relaxation
`px4b_conormal_relax` and the qualitative identity `px4b_defect_decomp` (applied to `U.H`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- **Uniform version of `defect_map`.** The constant depends only on `(d, s, N, νm, νp, c₀, Λ₀)`
and on `(σ, b, m)` and the parameter facts `2 ≤ d`, `0 < s < d`, `m ≤ N`; it is chosen before
`β, V, ρ`. -/
theorem defect_map_unif (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (σ : ℝ) (hσ : σ ≤ s)
    (b m : ℕ) (hm : 2 ≤ m) (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B : ℝ) (F : Torus d → Torus d → ℝ), 0 ≤ B →
      Conormal σ b m B F →
        Conormal (σ - 1 / 2) b (m - 2) (C * B) (defectOp d s V β ρ F) := by
  obtain ⟨C1, hC10, hC1⟩ := px4b_N_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hsd hσ b m hN
  obtain ⟨C2, hC20, hC2⟩ := px4b_Zv_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hsd hσ b m hm hN
  obtain ⟨C3, hC30, hC3⟩ := px4b_Y1_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hsd hσ b m hm hN
  obtain ⟨C4, hC40, hC4⟩ := px4b_T1_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hsd hσ b m hm hN
  obtain ⟨C5, hC50, hC5⟩ := px4b_J_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hs0 hsd hσ b m hm hN
  obtain ⟨C6, hC60, hC6⟩ := px4b_Ps_class_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hs0 hsd hσ b m hm hN
  obtain ⟨Cr, hCr1, hCr⟩ := px4b_conormal_relax (d := d) (fun _ => b + 3) (fun _ => b) (m - 2)
    (show σ - 1 < σ - 1 / 2 by linarith)
  refine ⟨Cr * (C2 + C3 + C4 + C5 + C6), by positivity, fun β V ρ U B F hB hF => ?_⟩
  have e2 := hC2 β V ρ U B F hB hF
  have e3 := hC3 β V ρ U B F hB hF
  have e4 := hC4 β V ρ U B F hB hF
  have e5 := hC5 β V ρ U B F hB hF
  have e6 := hC6 β V ρ U B F hB hF
  have hsum := conormalL_add (conormalL_add (conormalL_add (conormalL_add e2 e3) e4) e5) e6
  have hB' : C2 * B + C3 * B + C4 * B + C5 * B + C6 * B = (C2 + C3 + C4 + C5 + C6) * B := by ring
  rw [hB'] at hsum
  have hcongr := conormalL_congr_offDiag
    (F' := defectOp d s V β ρ F) (fun x y hxy => ?_) hsum
  · have := hCr _ _ (by positivity) hcongr
    rw [← mul_assoc] at this
    exact this
  · have hN1 := hC1 β V ρ U B F hB hF
    have hdec := px4b_defect_decomp U.H F hm (b' := b + 1) hN1 hxy
    simp only [defectOp, if_neg hxy]
    rw [hdec]
    have hZ : px4b_Z0 β⁻¹ F (newtonOp d β ρ F) x y =
        (px4b_Z0 β⁻¹ F (newtonOp d β ρ F) x y - px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y) +
          px4b_Sm β⁻¹ (px4b_aF d β ρ F) (px4b_a'F d β ρ F) x y := by ring
    linarith

end HRS.ME.ParxU

end
