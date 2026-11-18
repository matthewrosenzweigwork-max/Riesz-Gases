import HRS.MH.FilteredSF5

/-!
# Packet SF6 `sf6_trace_error_L` (pointwise trace-norm covariance error with `N^{-2L/d}`)

Statement copied verbatim from `HRS/MH/FilteredSpec.lean` (namespace `HRS.MH.Filtered` there, `HRS.MH.FilteredP` here).
Copy of `gf_trace_error_proof` (`HRS/Main/GFB3Aux4.lean:62-154`) with the order `1` replaced by `L`
(`filtered_coercivity_proof` for all `L`), test-function facts at order `2L` from `sf5_F_props_L`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.FilteredP

open HRS HRS.Uniform HRS.GF

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem sf6_trace_error_L (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (γ : ℕ) (hγ : 2 * d + 10 < γ)
    (L : ℕ) (hL : 1 ≤ L) (hγL : (d : ℝ) / 2 + 1 + 2 * (L : ℝ) < (γ : ℝ)) (Λ : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk (γ + 2 * d + 12) ρ →
        Torus.cbNorm (γ + 2 * d + 12) ρ ≤ Λ → ∀ X : Config d N, X ∉ collisionSet d N →
        ∀ q : ℝ, 0 ≤ q →
          traceNormForm (covForm (γ : ℝ) q (empirical X) - covForm (γ : ℝ) q (withDensityReal ρ)) ≤
            C * q * (Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N) +
              (N : ℝ) ^ (-(2 * (L : ℝ)) / d)) := by
  classical
  have hγR : (d : ℝ) + ((d + 1 : ℕ) : ℝ) + 1 < (γ : ℝ) := by
    have : ((2 * d + 10 : ℕ) : ℝ) < (γ : ℝ) := by exact_mod_cast hγ
    push_cast at this ⊢
    linarith
  have hγ2 : (d : ℝ) / 2 + 2 < (γ : ℝ) := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    push_cast at hγR
    linarith
  obtain ⟨C₀min, hC⟩ := HRS.Uniform.Q12.filtered_coercivity_proof hd s hs0 hsd Λ
  refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
  obtain ⟨Cf, hCf, hmain⟩ := hC C₀ hC₀ L hL
  set α : ℝ := ((d : ℝ) - s) / 2 with hαdef
  have hα0 : 0 ≤ α := by rw [hαdef]; linarith
  have hα : 2 * α ≤ d := by rw [hαdef]; linarith
  set Kh : ℝ := gfb3_Chom d α * gfb3_Cn d (γ : ℝ) (d + 1) with hKh
  obtain ⟨KΔ, hKΔ0, hKΔ⟩ := sf5_F_props_L hd L hL hγL
  have hKh0 : 0 ≤ Kh := mul_nonneg (gfb3_Chom_nonneg d α) (gfb3_Cn_nonneg d _ _)
  refine ⟨2 * Cf * (Kh + KΔ + 1), by positivity, ?_⟩
  intro N hN ρ hρ hρk hρΛ X hX q hq
  have hρle : ∀ x, ρ x ≤ Λ := by
    intro x
    have h0 := HRS.PDE.ET.norm_iteratedFDeriv_le_cbNorm (φ := ρ) (k := γ + 2 * d + 12) (j := 0)
      (Nat.zero_le _) hρk (Torus.rep x)
    rw [norm_iteratedFDeriv_zero] at h0
    have : Torus.lift ρ (Torus.rep x) = ρ x := by simp [Torus.lift, Torus.mk_rep]
    rw [this, Real.norm_eq_abs] at h0
    exact (le_abs_self _).trans (h0.trans hρΛ)
  obtain ⟨hnn, hbd⟩ := hmain N hN ρ hρ hρle X hX
  haveI : IsProbabilityMeasure (empirical X) := empirical_isProbabilityMeasure (by omega) X
  haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.isProb_withDensityReal hρ
  set E : ℝ := rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N with hE
  set n : ℝ := (N : ℝ) ^ (-(2 * (L : ℝ)) / d) with hn
  have hn0 : 0 ≤ n := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hsq0 : 0 ≤ Real.sqrt E := Real.sqrt_nonneg _
  have hRHS : 0 ≤ 2 * Cf * (Kh + KΔ + 1) * q * (Real.sqrt E + n) :=
    mul_nonneg (mul_nonneg (by positivity) hq) (add_nonneg hsq0 hn0)
  unfold traceNormForm
  refine Real.iSup_le (fun p => ?_) hRHS
  obtain ⟨⟨m, e, f⟩, he, hf⟩ := p
  show ∑ i : Fin m, |(covForm (γ : ℝ) q (empirical X) - covForm (γ : ℝ) q (withDensityReal ρ)) (e i) (f i)| ≤ _
  set D := covForm (γ : ℝ) q (empirical X) - covForm (γ : ℝ) q (withDensityReal ρ) with hD
  set ε : Fin m → ℝ := fun i => if 0 ≤ D (e i) (f i) then 1 else -1 with hεdef
  have hε : ∀ i, |ε i| ≤ 1 := by
    intro i; simp only [hεdef]; split_ifs <;> simp
  have habs : ∀ i, |D (e i) (f i)| = ε i * D (e i) (f i) := by
    intro i
    simp only [hεdef]
    split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (not_le.mp h)]; ring
  have hB := gfb3_B_norm_le e f ε hε he hf
  obtain ⟨-, hfin, hhom, -⟩ := gfb3_F_props hd hγR α hα0 hα (gfb3_B e f ε) hB
  obtain ⟨hCk, hlap⟩ := hKΔ (gfb3_B e f ε) hB
  have hsum : ∑ i, |D (e i) (f i)| = 2 * q * (∫ x, gfb3_F (γ : ℝ) (gfb3_B e f ε) x ∂(empirical X) -
      ∫ x, gfb3_F (γ : ℝ) (gfb3_B e f ε) x ∂(withDensityReal ρ)) := by
    simp_rw [habs]
    have h1 := gfb3_family_cov hγ2 hq (empirical X) e f ε
    have h2 := gfb3_family_cov hγ2 hq (withDensityReal ρ) e f ε
    simp only [hD, ContinuousLinearMap.sub_apply, mul_sub, Finset.sum_sub_distrib, h1, h2]
  rw [hsum]
  have hco := hbd (gfb3_F (γ : ℝ) (gfb3_B e f ε)) hCk hfin (KΔ) hKΔ0 hlap
  have hhom' : homSobolev α (gfb3_F (γ : ℝ) (gfb3_B e f ε)) ≤ Kh := hhom
  have hco2 : |∫ x, gfb3_F (γ : ℝ) (gfb3_B e f ε) x ∂(empirical X) -
      ∫ x, gfb3_F (γ : ℝ) (gfb3_B e f ε) x ∂(withDensityReal ρ)| ≤ Cf * Kh * Real.sqrt E + Cf * n * KΔ := by
    refine hco.trans ?_
    have := mul_le_mul_of_nonneg_left hhom' hCf.le
    nlinarith [mul_le_mul_of_nonneg_right this hsq0]
  calc 2 * q * (∫ x, gfb3_F (γ : ℝ) (gfb3_B e f ε) x ∂(empirical X) -
        ∫ x, gfb3_F (γ : ℝ) (gfb3_B e f ε) x ∂(withDensityReal ρ))
      ≤ 2 * q * |∫ x, gfb3_F (γ : ℝ) (gfb3_B e f ε) x ∂(empirical X) -
        ∫ x, gfb3_F (γ : ℝ) (gfb3_B e f ε) x ∂(withDensityReal ρ)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    _ ≤ 2 * q * (Cf * Kh * Real.sqrt E + Cf * n * KΔ) := mul_le_mul_of_nonneg_left hco2 (by positivity)
    _ ≤ _ := by
        have h3 : Cf * Kh * Real.sqrt E + Cf * n * KΔ ≤ Cf * (Kh + KΔ + 1) * (Real.sqrt E + n) := by
          nlinarith [mul_nonneg hCf.le hKh0, mul_nonneg hCf.le hKΔ0, mul_nonneg hCf.le hsq0,
            mul_nonneg hCf.le hn0, mul_nonneg (mul_nonneg hCf.le hKh0) hn0,
            mul_nonneg (mul_nonneg hCf.le hKΔ0) hsq0, mul_nonneg (mul_nonneg hCf.le hsq0) hn0]
        nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * q)]

end HRS.MH.FilteredP
