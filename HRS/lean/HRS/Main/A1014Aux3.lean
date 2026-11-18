import HRS.Main.A1014Aux2

/-!
# Packet A1014, part 3: helpers for Corollary A.14 (fields): Gaussian `d_{C²}` bound, arithmetic
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A1014

variable {d : ℕ}

/-- from the coupling of `a34_gauss_couple` to `d₂(νG, νGlim) ≤ √Cg (Δ + √Δ)`. -/
theorem a1014_gauss_dist {Cg Δ : ℝ} (hCg : 0 < Cg) (hΔ : 0 ≤ Δ)
    {νG νGlim : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hP : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (G₁ G₂ : Ω → NegSobolev d (gammaIdx d : ℝ)), Measurable G₁ ∧ Measurable G₂ ∧
      P.map G₁ = νG ∧ P.map G₂ = νGlim ∧ Integrable (fun ω => ‖G₁ ω - G₂ ω‖ ^ 2) P ∧
      ∫ ω, ‖G₁ ω - G₂ ω‖ ^ 2 ∂P ≤ Cg * (Δ + Δ ^ 2)) :
    smoothDist 2 νG νGlim ≤ Real.sqrt Cg * (Δ + Real.sqrt Δ) := by
  obtain ⟨Ω, mΩ, P, hP, G₁, G₂, hm₁, hm₂, hl₁, hl₂, hint, hbd⟩ := hP
  haveI := hP
  have h2 : smoothDist 2 νG νGlim ≤ ∫ ω, ‖G₁ ω - G₂ ω‖ ∂P := by
    rw [← hl₁, ← hl₂]
    exact HRS.A34.a34_smoothDist_coupling P G₁ G₂ hm₁ hm₂
      (HRS.A34.a34_E_norm_le (hm₁.sub hm₂).aestronglyMeasurable hint).1
  have h3 : ∫ ω, ‖G₁ ω - G₂ ω‖ ∂P ≤ Real.sqrt (∫ ω, ‖G₁ ω - G₂ ω‖ ^ 2 ∂P) :=
    (HRS.A34.a34_E_norm_le (hm₁.sub hm₂).aestronglyMeasurable hint).2
  have h4 : Real.sqrt (∫ ω, ‖G₁ ω - G₂ ω‖ ^ 2 ∂P) ≤ Real.sqrt Cg * (Δ + Real.sqrt Δ) := by
    refine (Real.sqrt_le_sqrt hbd).trans ?_
    rw [Real.sqrt_mul hCg.le]
    exact mul_le_mul_of_nonneg_left (HRS.A34.a34_sqrt_Δ_le Δ hΔ) (Real.sqrt_nonneg _)
  exact h2.trans (h3.trans h4)

theorem a1014_fieldRate_nonneg {εf q σ 𝔈 : ℝ} {N : ℕ} (hε : 0 ≤ εf) (hq : 0 ≤ q) (hσ : 0 ≤ σ)
    (h𝔈 : 0 ≤ 𝔈) : 0 ≤ fieldRate d εf q σ 𝔈 N := by
  unfold fieldRate
  have h1 : 0 ≤ 𝔈 ^ ((1 : ℝ) / 2) := Real.rpow_nonneg h𝔈 _
  have h2 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  positivity

theorem a1014_arith_field {C9 Cs sg L9 t fr Δ δ : ℝ} (hC9 : 0 < C9) (hsg : 0 ≤ sg) (ht : 0 ≤ t)
    (hL9 : 0 < L9) (hfr : 0 ≤ fr) (hΔ : 0 ≤ Δ) (hδ : Δ ≤ δ) (G : ℝ) (hG : G ≤ sg * δ) (D : ℝ)
    (hD : D ≤ Cs * Δ) :
    C9 * Real.exp (L9 * t) * fr + D + G ≤
      (C9 + |Cs| + sg + 1) * Real.exp ((L9 + 1) * t) * (fr + δ) := by
  have hδ0 : 0 ≤ δ := hΔ.trans hδ
  have e1 : Real.exp (L9 * t) ≤ Real.exp ((L9 + 1) * t) :=
    Real.exp_le_exp.2 (by nlinarith)
  have e2 : 1 ≤ Real.exp ((L9 + 1) * t) := Real.one_le_exp (by nlinarith)
  have hE := Real.exp_pos ((L9 + 1) * t)
  have hD' : D ≤ |Cs| * δ := by
    calc D ≤ Cs * Δ := hD
      _ ≤ |Cs| * Δ := mul_le_mul_of_nonneg_right (le_abs_self _) hΔ
      _ ≤ |Cs| * δ := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
  set E := Real.exp ((L9 + 1) * t) with hEdef
  have t1 : C9 * Real.exp (L9 * t) * fr ≤ C9 * E * fr :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e1 hC9.le) hfr
  have t2 : |Cs| * δ ≤ |Cs| * E * δ :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (abs_nonneg _) e2) hδ0
  have t3 : sg * δ ≤ sg * E * δ :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hsg e2) hδ0
  have hCs := abs_nonneg Cs
  have key : (C9 + |Cs| + sg + 1) * E * (fr + δ) - (C9 * E * fr + |Cs| * E * δ + sg * E * δ) =
      C9 * E * δ + |Cs| * E * fr + sg * E * fr + E * fr + E * δ := by ring
  have hpos : 0 ≤ C9 * E * δ + |Cs| * E * fr + sg * E * fr + E * fr + E * δ := by
    have := hC9.le
    positivity
  linarith

end HRS.Main.A1014
