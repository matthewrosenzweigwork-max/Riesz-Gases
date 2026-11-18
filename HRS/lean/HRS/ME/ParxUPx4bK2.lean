import HRS.ME.ParxUPx4bK1
import HRS.ME.ParxUConormal1

/-!
# Packet P3b (part 2): uniform `px4b_cN_class`

Uniform version (constant chosen before `β, V, ρ`, through the bundle `ParxU`) of
`HRS.Parx.px4b_cN_class` (Packets:768).  The two ρ-dependent ingredients of the old proof are
replaced by their uniform versions:

* `px4b_Kc_class` by `px4b_Kc_class_unif` (ParxUPx4bK1);
* `conormal_row_smooth H` (the row integral `x ↦ ∫ F(x,y) ρ(y) dy`) by its uniform version
  `conormal_row_smooth_aux_unif` (ParxUConormal1), whose constant depends only on `(d, σ, b, m, Λ₀)`.

The identity `px4b_cN_eq` is qualitative and is applied with the bundle's `ParxHyp` part.
The kernel is called `Nk` (the name `N` is the derivative level of the bundle).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- **Uniform version of `px4b_cN_class`.** The constant depends only on `(d, s, N, νm, νp, Λ₀, b', m, τ)`
and on the parameter facts `2 ≤ d`, `0 < s < d`, `τ + 2 < d`, `m ≤ N`; it is chosen before `β, V, ρ`. -/
theorem px4b_cN_class_unif (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {τ : ℝ} (hτ : τ + 2 < d)
    (b' m : ℕ) (hm : 2 ≤ m) (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (B' : ℝ) (Nk : Torus d → Torus d → ℝ), 0 ≤ B' → Conormal τ b' m B' Nk →
        Torus.IsCk ((m - 2 : ℕ) : WithTop ℕ∞) (px4b_cN d s V β ρ Nk) ∧
          Torus.cbNorm (m - 2) (px4b_cN d s V β ρ Nk) ≤ C * B' := by
  obtain ⟨Ck, hCk0, hCk⟩ := px4b_Kc_class_unif (d := d) (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hs0 hsd hτ b' m hm hN
  obtain ⟨Cr, hCr0, hCr⟩ := conormal_row_smooth_aux_unif (d := d) (s := s) (N := N) (νm := νm)
    (νp := νp) (c₀ := c₀) (Λ₀ := Λ₀) hd (σ := τ + 2) hτ (b' + 2) (m - 2) (by omega)
  refine ⟨Cr * Ck, mul_nonneg hCr0 hCk0, fun β V ρ U B' Nk hB' hNk => ?_⟩
  have hKc := hCk β V ρ U B' Nk hB' hNk
  have h := hCr β V ρ U (Ck * B') (swapK (px4b_Kc d s β ρ Nk)) (mul_nonneg hCk0 hB')
    (conormalL_swap hKc)
  rw [px4b_cN_eq U.H hm hNk]
  refine ⟨h.1, ?_⟩
  calc _ ≤ Cr * (Ck * B') := h.2
    _ = _ := by ring

end HRS.ME.ParxU

end
