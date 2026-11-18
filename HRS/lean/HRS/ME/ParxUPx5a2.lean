import HRS.ME.ParxUPx5a1
import HRS.ME.ParxUConormal1

/-!
# Packet P4a (part 2): uniform `px5_jpair_bound`

Uniform version (constant chosen before `β, V, ρ`, through the bundle `ParxU`) of
`HRS.Parx.px5_jpair_bound` (PX5AuxE:164), with the constants of

* `px5_K_class_unif` (uniform `px5_K_class`, PX5AuxE:86), from `px5_psi_class_unif` and
  `jop_general_unif`;
* `px5_K_pointwise_unif` (uniform `px5_K_pointwise`, PX5AuxE:112): the constant `Cw` of the original
  proof depends only on `s` (its proof uses the parameter `0 < s` and no density), so it is stated with
  `hs0 : 0 < s` and no bundle;
* `px5_K_rowcol_unif` (uniform `px5_K_rowcol`, PX5AuxE:134), from `conormal_row_int_unif`, whose
  constant is `|Λ₀| · ∫ envW` and depends on `(d, Λ₀)` only.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- **Uniform version of `px5_K_class`.** The constant depends only on `(d, s, N, νm, νp, c₀, Λ₀)`,
on `J` and on `2 ≤ d`, `0 < s < d`, `px5m d J ≤ N`; it is chosen before `β, V, ρ`. -/
theorem px5_K_class_unif (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (J : ℕ) (hN : px5m d J ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Conormal 0 3 (J + 1) (C * posSeminorm (px5m d J + 2) f)
        (px5K d s ρ (parxPsi d s V β ρ f (parxL d J))) := by
  obtain ⟨Cp, hCp0, hCp⟩ := px5_psi_class_unif hd hs0 hsd J hN
  have hJN : J + 3 ≤ N := by
    have : J + 3 ≤ px5m d J := by unfold px5m parxL; omega
    omega
  obtain ⟨CJ, hCJ0, hCJ⟩ := jop_general_unif hd hs0 hsd (s - 2) (by linarith) 1 (J + 3)
    (by omega) hJN
  refine ⟨CJ * Cp, mul_nonneg hCJ0 hCp0, fun β V ρ U f hf => ?_⟩
  have hB0 : 0 ≤ Cp * posSeminorm (px5m d J + 2) f := mul_nonneg hCp0 (posSeminorm_nonneg' _ _)
  have h := hCJ β V ρ U _ _ hB0 (hCp β V ρ U f hf)
  have e1 : s - 2 + 2 - s = 0 := by ring
  have e2 : J + 3 - 2 = J + 1 := by omega
  rw [e1, e2] at h
  have e3 : CJ * (Cp * posSeminorm (px5m d J + 2) f) = CJ * Cp * posSeminorm (px5m d J + 2) f := by
    ring
  rw [e3] at h
  exact h

/-- **Uniform version of `px5_K_pointwise`.** The constant depends only on `s` (`0 < s`): the pointwise
bound of a conormal kernel of order `0` with log index `3` does not involve the density, so no bundle
is needed. -/
theorem px5_K_pointwise_unif (hs0 : 0 < s) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ {B : ℝ} {F : Torus d → Torus d → ℝ}, 0 ≤ B → Conormal 0 3 0 B F →
      ∀ x y, x ≠ y → |F x y| ≤ B * (1 + Cw) * wEnv s x y := by
  obtain ⟨C0, hC0, hC⟩ := rpow_log_pow_le s hs0 3
  refine ⟨C0, hC0, fun {B F} hB hF x y hxy => ?_⟩
  refine px5_value_bound hF hB hC0 (E := fun r => 1 + r ^ (-s)) (fun r hr => ?_)
    (fun r hr0 hrr => ?_) x y hxy
  · have : 0 ≤ r ^ (-s) := Real.rpow_nonneg hr _
    linarith
  · have hr1 : r ≤ 1 := by unfold r0 at hrr; linarith
    have h1 := hC r hr0 hr1
    have e : r ^ (-s) * r ^ s = 1 := by rw [← Real.rpow_add hr0]; simp
    have e2 : (1 + |Real.log r|) ^ 3 = r ^ (-s) * (r ^ s * (1 + |Real.log r|) ^ 3) := by
      rw [← mul_assoc, e, one_mul]
    simp only [add_zero, Nat.cast_zero, neg_zero, Real.rpow_zero, one_mul]
    rw [e2]
    have h3 : 0 ≤ r ^ (-s) := Real.rpow_nonneg hr0.le _
    calc r ^ (-s) * (r ^ s * (1 + |Real.log r|) ^ 3) ≤ r ^ (-s) * C0 :=
          mul_le_mul_of_nonneg_left h1 h3
      _ ≤ C0 * (1 + r ^ (-s)) := by nlinarith

/-- **Uniform version of `px5_K_rowcol`.** The constant `Kr` depends only on `(d, Λ₀)` and on
`2 ≤ d`; it is chosen before `β, V, ρ`. -/
theorem px5_K_rowcol_unif (hd : 2 ≤ d) :
    ∃ Kr : ℝ, 0 ≤ Kr ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ {B : ℝ} {F : Torus d → Torus d → ℝ}, 0 ≤ B → Conormal 0 3 0 B F →
      (∀ x, F x x = 0) →
      (∀ x, Integrable (fun y => F x y) (withDensityReal ρ) ∧
        ∫ y, |F x y| ∂(withDensityReal ρ) ≤ Kr * B) ∧
      (∀ y, Integrable (fun x => F x y) (withDensityReal ρ) ∧
        ∫ x, |F x y| ∂(withDensityReal ρ) ≤ Kr * B) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨Kr, hKr0, hKr⟩ := conormal_row_int_unif (d := d) (s := s) (N := N) (νm := νm)
    (νp := νp) (c₀ := c₀) (Λ₀ := Λ₀) hd (σ := (0 : ℝ)) (by linarith) 3
  refine ⟨Kr, hKr0, fun β V ρ U {B F} hB hF hdiag => ⟨fun x => hKr β V ρ U B F hB hF hdiag x,
    fun y => ?_⟩⟩
  exact hKr β V ρ U B (swapK F) hB (conormalL_swap hF) (fun x => hdiag x) y

/-- **Uniform version of `px5_jpair_bound`.** The constant depends only on `(d, s, N, νm, νp, c₀, Λ₀)`,
on `J` and on `2 ≤ d`, `0 < s < d`, `px5m d J ≤ N`; it is chosen before `β, V, ρ`, `f, x, y`. -/
theorem px5_jpair_bound_unif (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (J : ℕ)
    (hN : px5m d J ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ f : Torus d → ℝ, Torus.IsSmooth f → ∀ x y, x ≠ y →
      |Jpair d s ρ (parxPsi d s V β ρ f (parxL d J)) x y| ≤
        C * posSeminorm (px5m d J + 2) f * wEnv s x y := by
  obtain ⟨CK, hCK0, hCK⟩ := px5_K_class_unif hd hs0 hsd J hN
  obtain ⟨Cw, hCw0, hCw⟩ := px5_K_pointwise_unif (d := d) (s := s) hs0
  obtain ⟨Kr, hKr0, hKr⟩ := px5_K_rowcol_unif (d := d) (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd
  refine ⟨CK * (2 * (1 + Cw) + 2 * Kr), by positivity, fun β V ρ U f hf x y hxy => ?_⟩
  set ψ := parxPsi d s V β ρ f (parxL d J) with hψ
  set B := CK * posSeminorm (px5m d J + 2) f with hB
  have hB0 : 0 ≤ B := mul_nonneg hCK0 (posSeminorm_nonneg' _ _)
  have hcl := hCK β V ρ U f hf
  have hcl0 : Conormal 0 3 0 B (px5K d s ρ ψ) :=
    ConormalL.mono hcl hB0 le_rfl (fun c => le_rfl) (Nat.zero_le _) le_rfl
  have hsym := px5_symm U.H J f hf
  have hd0 : 0 < d := by omega
  rw [px5_jpair_formula hd0 ψ hsym x y hxy]
  obtain ⟨hrow, hcol⟩ := hKr β V ρ U hB0 hcl0 (px5K_diag ψ)
  have p1 := hCw hB0 hcl0 x y hxy
  have p2 := hCw hB0 hcl0 y x (Ne.symm hxy)
  rw [px5_wEnv_symm s y x] at p2
  have m1 : |∫ z, px5K d s ρ ψ z y ∂(withDensityReal ρ)| ≤ Kr * B :=
    (abs_integral_le_integral_abs).trans (hcol y).2
  have m2 : |∫ z, px5K d s ρ ψ z x ∂(withDensityReal ρ)| ≤ Kr * B :=
    (abs_integral_le_integral_abs).trans (hcol x).2
  have hw := px5_wEnv_ge_one s x y
  calc |(px5K d s ρ ψ x y - ∫ z, px5K d s ρ ψ z y ∂(withDensityReal ρ)) +
        (px5K d s ρ ψ y x - ∫ z, px5K d s ρ ψ z x ∂(withDensityReal ρ))|
      ≤ |px5K d s ρ ψ x y| + |∫ z, px5K d s ρ ψ z y ∂(withDensityReal ρ)| +
        (|px5K d s ρ ψ y x| + |∫ z, px5K d s ρ ψ z x ∂(withDensityReal ρ)|) := by
        refine (abs_add_le _ _).trans ?_
        exact add_le_add (abs_sub _ _) (abs_sub _ _)
    _ ≤ B * (1 + Cw) * wEnv s x y + Kr * B + (B * (1 + Cw) * wEnv s x y + Kr * B) := by
        gcongr
    _ ≤ CK * (2 * (1 + Cw) + 2 * Kr) * posSeminorm (px5m d J + 2) f * wEnv s x y := by
        rw [hB]
        have hp := posSeminorm_nonneg' (px5m d J + 2) f
        have h1 : 0 ≤ CK * posSeminorm (px5m d J + 2) f * Kr := by positivity
        nlinarith

end HRS.ME.ParxU

end
