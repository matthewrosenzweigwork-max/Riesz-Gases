/-
# HRS.MD.DOMLeib2 — packet DOM-LEIB (bounds)

Pointwise bounds `|χ_ε(F-c) - (F-c)|`, `|∇(χ_ε(F-c)) - ∇F|`, `|𝓛(χ_ε(F-c)) - 𝓛F|` by `C Pw⁴` off collisions,
vanishing when `¬ Near ε X`.
-/
import HRS.MD.DOMLeib

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.MD.DOMProof

open HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

/-- The remainder estimate (pure algebra). -/
theorem domp_remainder_alg {P E X B b0 gχ lχ gF bn fc i1 i2 : ℝ} (hP : 1 ≤ P) (hE : 0 ≤ E) (hX : 0 ≤ X)
    (hB : 0 ≤ B) (hb0 : 0 ≤ b0) (hgχ0 : 0 ≤ gχ) (hgχ : gχ ≤ X * P) (hlχ : |lχ| ≤ X * P ^ 2)
    (hgF0 : 0 ≤ gF) (hgF : gF ≤ E * P) (hbn0 : 0 ≤ bn) (hbn : bn ≤ E * P ^ 2) (hfc : |fc| ≤ B * P)
    (hi1 : |i1| ≤ gχ * gF) (hi2 : |i2| ≤ bn * gχ) :
    |b0 * (2 * i1 + fc * lχ) - fc * i2| ≤
      (b0 * (2 * X * E + B * X) + B * E * X) * P ^ 4 := by
  have hP0 : 0 ≤ P := by linarith
  have hP2 : P ^ 2 ≤ P ^ 4 := pow_le_pow_right₀ hP (by norm_num)
  have hP3 : P ^ 3 ≤ P ^ 4 := pow_le_pow_right₀ hP (by norm_num)
  have h1 : |i1| ≤ X * E * P ^ 2 := by
    calc |i1| ≤ gχ * gF := hi1
      _ ≤ (X * P) * (E * P) := mul_le_mul hgχ hgF hgF0 (by positivity)
      _ = X * E * P ^ 2 := by ring
  have h2 : |fc * lχ| ≤ B * X * P ^ 3 := by
    rw [abs_mul]
    calc |fc| * |lχ| ≤ (B * P) * (X * P ^ 2) := mul_le_mul hfc hlχ (abs_nonneg _) (by positivity)
      _ = B * X * P ^ 3 := by ring
  have h3 : |fc * i2| ≤ B * E * X * P ^ 4 := by
    rw [abs_mul]
    have : |i2| ≤ (E * P ^ 2) * (X * P) := hi2.trans (mul_le_mul hbn hgχ hgχ0 (by positivity))
    calc |fc| * |i2| ≤ (B * P) * ((E * P ^ 2) * (X * P)) := mul_le_mul hfc this (abs_nonneg _) (by positivity)
      _ = B * E * X * P ^ 4 := by ring
  have h4 : |2 * i1 + fc * lχ| ≤ 2 * X * E * P ^ 4 + B * X * P ^ 4 := by
    calc |2 * i1 + fc * lχ| ≤ |2 * i1| + |fc * lχ| := abs_add_le _ _
      _ ≤ 2 * (X * E * P ^ 2) + B * X * P ^ 3 := by
          rw [abs_mul, abs_two]; linarith
      _ ≤ 2 * X * E * P ^ 4 + B * X * P ^ 4 := by
          have := mul_le_mul_of_nonneg_left hP2 (mul_nonneg hX hE)
          have := mul_le_mul_of_nonneg_left hP3 (mul_nonneg hB hX)
          nlinarith
  calc |b0 * (2 * i1 + fc * lχ) - fc * i2| ≤ |b0 * (2 * i1 + fc * lχ)| + |fc * i2| := abs_sub _ _
    _ = b0 * |2 * i1 + fc * lχ| + |fc * i2| := by rw [abs_mul, abs_of_nonneg hb0]
    _ ≤ b0 * (2 * X * E * P ^ 4 + B * X * P ^ 4) + B * E * X * P ^ 4 := by
        have := mul_le_mul_of_nonneg_left h4 hb0
        linarith
    _ = _ := by ring

section Bounds

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
include hd hcrit

theorem domp_diff_bounds {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) {ρ : Torus d → ℝ} {f : Torus d → ℝ} {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ}
    (hψ : IsPairCorrector d s V β ρ f K₁ ψ) (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ∀ (X : Config d N), X ∉ collisionSet d N →
      (¬ Near ε X →
        Fe ε c (Fstat ψ) X - (Fstat ψ X - c) = 0 ∧
        (∀ i, configGrad (Fe ε c (Fstat ψ)) X i - configGrad (Fstat ψ) X i = 0) ∧
        particleGen d s V β (Fe ε c (Fstat ψ)) X - particleGen d s V β (Fstat ψ) X = 0) ∧
      |Fe ε c (Fstat ψ) X - (Fstat ψ X - c)| ≤ C * Pw s X ^ 4 ∧
      (∀ i, ‖configGrad (Fe ε c (Fstat ψ)) X i - configGrad (Fstat ψ) X i‖ ≤ C * Pw s X ^ 4) ∧
      |particleGen d s V β (Fe ε c (Fstat ψ)) X - particleGen d s V β (Fstat ψ) X| ≤ C * Pw s X ^ 4 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  obtain ⟨E, hE0, hE⟩ := domp_F_envelope hd hcrit hV hβ hN hψ (N := N)
  obtain ⟨Xc, hXc0, hXc⟩ := domp_chi_deriv hs1 (d := d) (N := N)
  set B : ℝ := E + |c| with hB
  have hB0 : 0 ≤ B := by positivity
  set b0 : ℝ := β⁻¹ with hb0def
  have hb0 : 0 ≤ b0 := inv_nonneg.2 hβ.le
  set K₂ : ℝ := b0 * (2 * Xc * E + B * Xc) + B * E * Xc with hK₂
  have hK₂0 : 0 ≤ K₂ := by positivity
  set K₃ : ℝ := N * (b0 * E + E * E) with hK₃
  have hK₃0 : 0 ≤ K₃ := by positivity
  set Cc : ℝ := B + (E + B * Xc) + (K₃ + N * K₂) with hCc
  have hC1 : B ≤ Cc := by
    have : 0 ≤ (E + B * Xc) + (K₃ + N * K₂) := by positivity
    linarith
  have hC2 : E + B * Xc ≤ Cc := by
    have : 0 ≤ B + (K₃ + N * K₂) := by positivity
    linarith
  have hC3 : K₃ + N * K₂ ≤ Cc := by
    have : 0 ≤ B + (E + B * Xc) := by positivity
    linarith
  refine ⟨Cc, by positivity, fun ε hε X hX => ?_⟩
  have hXne : ∀ a b : Fin N, a ≠ b → X a ≠ X b := fun a b hab hXab => hX ⟨a, b, hab, hXab⟩
  have hP1 := domp_one_le_Pw (s := s) X
  set P : ℝ := Pw s X with hP
  have hP0 : 0 ≤ P := by linarith
  have hP2 : P ≤ P ^ 4 := by simpa using pow_le_pow_right₀ hP1 (show 1 ≤ 4 by norm_num)
  have hP2' : P ^ 2 ≤ P ^ 4 := pow_le_pow_right₀ hP1 (by norm_num)
  have hP3' : P ^ 3 ≤ P ^ 4 := pow_le_pow_right₀ hP1 (by norm_num)
  have hP4 : 0 ≤ P ^ 4 := by positivity
  obtain ⟨hFb, hGb, hLb, hbb⟩ := hE X hX
  have hcs := fun i => hXc ε hε X hX i
  have hFsl := fun i => domp_Fstat_slice hψ.symm hψ.size.smooth X hXne i
  have hχ0 := domp_chi_nonneg ε X
  have hχ1 := domp_chi_le_one ε X
  have hχm : |chi ε X - 1| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  have hfc : |Fstat ψ X - c| ≤ B * P := by
    calc |Fstat ψ X - c| ≤ |Fstat ψ X| + |c| := abs_sub _ _
      _ ≤ E * P + |c| * P := by
          have : |c| ≤ |c| * P := le_mul_of_one_le_right (abs_nonneg _) hP1
          linarith
      _ = B * P := by rw [hB]; ring
  have hD1 : Fe ε c (Fstat ψ) X - (Fstat ψ X - c) = (chi ε X - 1) * (Fstat ψ X - c) := by
    unfold Fe; ring
  have hD2 : ∀ i, configGrad (Fe ε c (Fstat ψ)) X i - configGrad (Fstat ψ) X i =
      (chi ε X - 1) • configGrad (Fstat ψ) X i + (Fstat ψ X - c) • configGrad (chi ε) X i := by
    intro i
    rw [domp_configGrad_Fe (hFsl i) (hcs i).1]
    module
  have hgen := domp_particleGen_Fe (V := V) (β := β) (s := s) (F := Fstat ψ) (c := c) (X := X)
    hFsl (fun i => (hcs i).1)
  have hD3 : particleGen d s V β (Fe ε c (Fstat ψ)) X - particleGen d s V β (Fstat ψ) X =
      (chi ε X - 1) * particleGen d s V β (Fstat ψ) X +
        ∑ i, (b0 * (2 * inner ℝ (configGrad (chi ε) X i) (configGrad (Fstat ψ) X i) +
            (Fstat ψ X - c) * configLap (chi ε) X i) -
          (Fstat ψ X - c) * inner ℝ (Torus.grad V (X i) + (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
            periodicRieszGrad d s (X i - X j)) (configGrad (chi ε) X i)) := by
    rw [hgen]; ring
  -- bound of the generator of `F`
  have hLF : |particleGen d s V β (Fstat ψ) X| ≤ K₃ * P ^ 3 := by
    unfold particleGen
    calc |∑ i, (β⁻¹ * configLap (Fstat ψ) X i - inner ℝ (Torus.grad V (X i) + (1 / (N : ℝ)) •
          ∑ j ∈ Finset.univ.erase i, periodicRieszGrad d s (X i - X j)) (configGrad (Fstat ψ) X i))|
        ≤ ∑ i, |β⁻¹ * configLap (Fstat ψ) X i - inner ℝ (Torus.grad V (X i) + (1 / (N : ℝ)) •
          ∑ j ∈ Finset.univ.erase i, periodicRieszGrad d s (X i - X j)) (configGrad (Fstat ψ) X i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, (b0 * E + E * E) * P ^ 3 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : |β⁻¹ * configLap (Fstat ψ) X i| ≤ b0 * E * P ^ 3 := by
            rw [abs_mul, abs_of_nonneg hb0]
            calc b0 * |configLap (Fstat ψ) X i| ≤ b0 * (E * P) := mul_le_mul_of_nonneg_left (hLb i) hb0
              _ ≤ b0 * E * P ^ 3 := by
                  have := mul_le_mul_of_nonneg_left hP3' (mul_nonneg hb0 hE0)
                  have h' : P ≤ P ^ 3 := by simpa using pow_le_pow_right₀ hP1 (show 1 ≤ 3 by norm_num)
                  nlinarith [mul_nonneg hb0 hE0]
          have h2 : |inner ℝ (Torus.grad V (X i) + (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
              periodicRieszGrad d s (X i - X j)) (configGrad (Fstat ψ) X i)| ≤ E * E * P ^ 3 := by
            calc _ ≤ ‖Torus.grad V (X i) + (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
                periodicRieszGrad d s (X i - X j)‖ * ‖configGrad (Fstat ψ) X i‖ :=
                  abs_real_inner_le_norm _ _
              _ ≤ (E * P ^ 2) * (E * P) := mul_le_mul (hbb i) (hGb i) (norm_nonneg _) (by positivity)
              _ = E * E * P ^ 3 := by ring
          calc _ ≤ |β⁻¹ * configLap (Fstat ψ) X i| + |inner ℝ (Torus.grad V (X i) + (1 / (N : ℝ)) •
              ∑ j ∈ Finset.univ.erase i, periodicRieszGrad d s (X i - X j)) (configGrad (Fstat ψ) X i)| :=
                abs_sub _ _
            _ ≤ b0 * E * P ^ 3 + E * E * P ^ 3 := add_le_add h1 h2
            _ = (b0 * E + E * E) * P ^ 3 := by ring
      _ = K₃ * P ^ 3 := by simp [hK₃]; ring
  -- bound of the remainder
  have hR : ∀ i, |b0 * (2 * inner ℝ (configGrad (chi ε) X i) (configGrad (Fstat ψ) X i) +
            (Fstat ψ X - c) * configLap (chi ε) X i) -
          (Fstat ψ X - c) * inner ℝ (Torus.grad V (X i) + (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
            periodicRieszGrad d s (X i - X j)) (configGrad (chi ε) X i)| ≤ K₂ * P ^ 4 := by
    intro i
    refine domp_remainder_alg hP1 hE0 hXc0 hB0 hb0 (norm_nonneg _) (hcs i).2.1 (hcs i).2.2.1
      (norm_nonneg _) (hGb i) (norm_nonneg _) (hbb i) hfc ?_ ?_
    · exact abs_real_inner_le_norm _ _
    · exact abs_real_inner_le_norm _ _
  refine ⟨fun hnear => ?_, ?_, fun i => ?_, ?_⟩
  · have h1 := domp_chi_eq_one hε hnear
    have hz := fun i => (hcs i).2.2.2 hnear
    refine ⟨by rw [hD1, h1]; ring, fun i => ?_, ?_⟩
    · rw [hD2, h1, (hz i).1]; simp
    · rw [hD3, h1]
      simp [(hz _).1, (hz _).2]
  · rw [hD1, abs_mul]
    calc |chi ε X - 1| * |Fstat ψ X - c| ≤ 1 * (B * P) := mul_le_mul hχm hfc (abs_nonneg _) zero_le_one
      _ = B * P := one_mul _
      _ ≤ B * P ^ 4 := mul_le_mul_of_nonneg_left hP2 hB0
      _ ≤ Cc * P ^ 4 := mul_le_mul_of_nonneg_right hC1 hP4
  · rw [hD2]
    calc ‖(chi ε X - 1) • configGrad (Fstat ψ) X i + (Fstat ψ X - c) • configGrad (chi ε) X i‖
        ≤ ‖(chi ε X - 1) • configGrad (Fstat ψ) X i‖ + ‖(Fstat ψ X - c) • configGrad (chi ε) X i‖ :=
          norm_add_le _ _
      _ = |chi ε X - 1| * ‖configGrad (Fstat ψ) X i‖ + |Fstat ψ X - c| * ‖configGrad (chi ε) X i‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 1 * (E * P) + (B * P) * (Xc * P) :=
          add_le_add (mul_le_mul hχm (hGb i) (norm_nonneg _) zero_le_one)
            (mul_le_mul hfc (hcs i).2.1 (norm_nonneg _) (by positivity))
      _ = E * P + B * Xc * P ^ 2 := by ring
      _ ≤ E * P ^ 4 + B * Xc * P ^ 4 :=
          add_le_add (mul_le_mul_of_nonneg_left hP2 hE0) (mul_le_mul_of_nonneg_left hP2' (by positivity))
      _ = (E + B * Xc) * P ^ 4 := by ring
      _ ≤ Cc * P ^ 4 := mul_le_mul_of_nonneg_right hC2 hP4
  · rw [hD3]
    have hsum : |∑ i, (b0 * (2 * inner ℝ (configGrad (chi ε) X i) (configGrad (Fstat ψ) X i) +
            (Fstat ψ X - c) * configLap (chi ε) X i) -
          (Fstat ψ X - c) * inner ℝ (Torus.grad V (X i) + (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
            periodicRieszGrad d s (X i - X j)) (configGrad (chi ε) X i))| ≤ N * (K₂ * P ^ 4) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ _i : Fin N, K₂ * P ^ 4 := Finset.sum_le_sum fun i _ => hR i
        _ = N * (K₂ * P ^ 4) := by simp
    calc _ ≤ |(chi ε X - 1) * particleGen d s V β (Fstat ψ) X| + |∑ i, (b0 * (2 * inner ℝ (configGrad (chi ε) X i) (configGrad (Fstat ψ) X i) +
            (Fstat ψ X - c) * configLap (chi ε) X i) -
          (Fstat ψ X - c) * inner ℝ (Torus.grad V (X i) + (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
            periodicRieszGrad d s (X i - X j)) (configGrad (chi ε) X i))| := abs_add_le _ _
      _ ≤ K₃ * P ^ 3 + N * (K₂ * P ^ 4) := by
          refine add_le_add ?_ hsum
          rw [abs_mul]
          calc |chi ε X - 1| * |particleGen d s V β (Fstat ψ) X| ≤ 1 * (K₃ * P ^ 3) :=
                mul_le_mul hχm hLF (abs_nonneg _) zero_le_one
            _ = K₃ * P ^ 3 := one_mul _
      _ ≤ K₃ * P ^ 4 + N * (K₂ * P ^ 4) :=
          add_le_add (mul_le_mul_of_nonneg_left hP3' hK₃0) le_rfl
      _ = (K₃ + N * K₂) * P ^ 4 := by ring
      _ ≤ Cc * P ^ 4 := mul_le_mul_of_nonneg_right hC3 hP4

end Bounds

end HRS.MD.DOMProof

end
