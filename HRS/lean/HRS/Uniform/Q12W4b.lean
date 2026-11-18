import HRS.Uniform.Q12W4

/-!
# Q12, part W4b: smeared densities are smooth
-/

noncomputable section

open HRS MeasureTheory Filter Topology
open HRS.CoercAux
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q12

variable {d : ℕ}

lemma q12_sobWeight_gauss_le {m : ℝ} (hm : 0 ≤ m) {t : ℝ} (ht : 0 < t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℝ, 0 ≤ w → (1 + 4 * Real.pi ^ 2 * w) ^ m * Real.exp (-t * w) ≤ B := by
  have hpi : (0 : ℝ) < 4 * Real.pi ^ 2 := by positivity
  set β : ℝ := t / (4 * Real.pi ^ 2) with hβ
  have hβ0 : 0 < β := by positivity
  set C₁ : ℝ := 1 + (⌈m⌉₊.factorial : ℝ) with hC₁
  refine ⟨Real.exp β * (β ^ m)⁻¹ * C₁, by positivity, fun w hw => ?_⟩
  set a : ℝ := 1 + 4 * Real.pi ^ 2 * w with ha
  have ha0 : 0 < a := by positivity
  have hexp : Real.exp (-t * w) = Real.exp β * Real.exp (-(β * a)) := by
    rw [← Real.exp_add]; congr 1
    rw [ha, hβ]; field_simp; ring
  have hR := q12_rpow_exp_le hm (u := β * a) (by positivity)
  rw [Real.mul_rpow hβ0.le ha0.le] at hR
  have hbm : 0 < β ^ m := Real.rpow_pos_of_pos hβ0 m
  have h1 : a ^ m * Real.exp (-(β * a)) ≤ (β ^ m)⁻¹ * C₁ := by
    rw [← div_eq_inv_mul, le_div_iff₀ hbm]
    calc a ^ m * Real.exp (-(β * a)) * β ^ m = β ^ m * a ^ m * Real.exp (-(β * a)) := by ring
      _ ≤ C₁ := hR
  rw [hexp]
  calc a ^ m * (Real.exp β * Real.exp (-(β * a))) = Real.exp β * (a ^ m * Real.exp (-(β * a))) := by ring
    _ ≤ Real.exp β * ((β ^ m)⁻¹ * C₁) := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = _ := by ring

lemma q12_norm_integral_mode_le (ν : Measure (Torus d)) [IsProbabilityMeasure ν] (k : Lattice d) :
    ‖∫ y, Torus.mode (-k) y ∂ν‖ ≤ 1 := by
  refine (norm_integral_le_of_norm_le_const (C := 1) (Filter.Eventually.of_forall fun y => ?_)).trans ?_
  · rw [norm_mode]
  · simp

theorem q12_isSmooth_smearDens {t : ℝ} (ht : 0 < t) (ν : Measure (Torus d)) [IsProbabilityMeasure ν] :
    Torus.IsSmooth (smearDens d t ν) := by
  set φ := smearDens d t ν with hφ
  have hc : Continuous φ := q12_continuous_smearDens ht ν
  have hint : Integrable φ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnorm : ∀ k : Lattice d, ‖PDE.coeffOf φ k‖ ≤ Real.exp (-t * Lattice.enorm k ^ 2) := by
    intro k
    rw [PDE.coeffOf_eq_fcoef, hφ, q12_fcoef_smearDens ht ν k, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-t * Lattice.enorm k ^ 2) * ‖∫ y, Torus.mode (-k) y ∂ν‖
        ≤ Real.exp (-t * Lattice.enorm k ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left (q12_norm_integral_mode_le ν k) (Real.exp_pos _).le
      _ = _ := mul_one _
  have hsum : Summable fun k => ‖PDE.coeffOf φ k‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hnorm (summable_gauss_lattice d t ht)
  have hinv : PDE.toFun (PDE.coeffOf φ) = φ := PDE.toFun_coeffOf φ hc hsum
  have hreal := PDE.isRealCoeff_coeffOf φ hint
  have hCk : ∀ j : ℕ, Torus.IsCk (j : WithTop ℕ∞) φ := by
    intro j
    set m : ℝ := (d : ℝ) / 2 + j + 1 with hm
    have hm0 : 0 ≤ m := by positivity
    obtain ⟨C, hC⟩ := PDE.toFun_isCk_le j m (by rw [hm]; linarith)
    obtain ⟨B, hB0, hB⟩ := q12_sobWeight_gauss_le hm0 ht
    have hmem : PDE.MemHs m (PDE.coeffOf φ) := by
      unfold PDE.MemHs
      refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (sq_nonneg _)) (fun k => ?_) ((summable_gauss_lattice d t ht).mul_left B)
      unfold PDE.sobWeight
      have h1 : ‖PDE.coeffOf φ k‖ ^ 2 ≤ Real.exp (-t * Lattice.enorm k ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hnorm k) 2
      have h2 : Real.exp (-t * Lattice.enorm k ^ 2) ^ 2 =
          Real.exp (-t * Lattice.enorm k ^ 2) * Real.exp (-t * Lattice.enorm k ^ 2) := sq _
      have h3 := hB (Lattice.enorm k ^ 2) (sq_nonneg _)
      have hp0 : 0 ≤ (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ m :=
        Real.rpow_nonneg (by positivity) _
      calc (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ m * ‖PDE.coeffOf φ k‖ ^ 2
          ≤ (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ m * Real.exp (-t * Lattice.enorm k ^ 2) ^ 2 :=
            mul_le_mul_of_nonneg_left h1 hp0
        _ = ((1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ m * Real.exp (-t * Lattice.enorm k ^ 2)) *
              Real.exp (-t * Lattice.enorm k ^ 2) := by rw [h2]; ring
        _ ≤ B * Real.exp (-t * Lattice.enorm k ^ 2) :=
            mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    have := (hC (PDE.coeffOf φ) hmem hreal).1
    rwa [hinv] at this
  unfold Torus.IsSmooth Torus.IsCk
  exact contDiff_infty.2 fun n => hCk n

end HRS.Uniform.Q12
