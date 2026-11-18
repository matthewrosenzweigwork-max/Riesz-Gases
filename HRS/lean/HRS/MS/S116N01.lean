import Mathlib

/-!
# S11.6 packet N01 (`R26-T8B.N01`): finite exponential interpolation with integrability and the Jensen lower bound

Prefix `s116_`, namespace `HRS.MS.S116`.  For `F` integrable with `exp(-b₀F), exp(-b₁F)` integrable and `θ ∈ [b₀, b₁]`:
`exp(-θF)` is integrable, `exp(-θ E F) ≤ E exp(-θF) ≤ max (E exp(-b₀F)) (E exp(-b₁F))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace HRS.MS.S116

/-- Convex-combination weights for `θ ∈ [b₀, b₁]`. -/
theorem s116_weights {b₀ b₁ θ : ℝ} (hb : b₀ ≤ b₁) (hθ : θ ∈ Set.Icc b₀ b₁) :
    ∃ l m : ℝ, 0 ≤ l ∧ 0 ≤ m ∧ l + m = 1 ∧ l * b₀ + m * b₁ = θ := by
  rcases hθ with ⟨h0, h1⟩
  rcases hb.eq_or_lt with h | h
  · refine ⟨1, 0, zero_le_one, le_rfl, by norm_num, ?_⟩
    have : θ = b₀ := le_antisymm (h ▸ h1) h0
    simp [this]
  · have hpos : 0 < b₁ - b₀ := sub_pos.mpr h
    refine ⟨(b₁ - θ) / (b₁ - b₀), (θ - b₀) / (b₁ - b₀), div_nonneg (by linarith) hpos.le,
      div_nonneg (by linarith) hpos.le, ?_, ?_⟩
    · field_simp; ring
    · field_simp; ring

theorem s116_exp_interp {b₀ b₁ θ : ℝ} (hb : b₀ ≤ b₁) (hθ : θ ∈ Set.Icc b₀ b₁) (y : ℝ) :
    ∃ l m : ℝ, 0 ≤ l ∧ 0 ≤ m ∧ l + m = 1 ∧
      Real.exp (-θ * y) ≤ l * Real.exp (-b₀ * y) + m * Real.exp (-b₁ * y) := by
  obtain ⟨l, m, hl, hm, hlm, hθe⟩ := s116_weights hb hθ
  refine ⟨l, m, hl, hm, hlm, ?_⟩
  have h := convexOn_exp.2 (Set.mem_univ (-b₀ * y)) (Set.mem_univ (-b₁ * y)) hl hm hlm
  have e : -θ * y = l • (-b₀ * y) + m • (-b₁ * y) := by
    simp only [smul_eq_mul]; rw [← hθe]; ring
  rw [e]; simpa using h

theorem s116_exponential_interval {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] (F : A → ℝ)
    (hF : Measurable F) (hFi : Integrable F P) (b₀ b₁ : ℝ) (hb : b₀ ≤ b₁)
    (h₀ : Integrable (fun x => Real.exp (-b₀ * F x)) P)
    (h₁ : Integrable (fun x => Real.exp (-b₁ * F x)) P) :
    ∀ θ ∈ Set.Icc b₀ b₁,
      Integrable (fun x => Real.exp (-θ * F x)) P ∧
      Real.exp (-θ * ∫ x, F x ∂P) ≤ ∫ x, Real.exp (-θ * F x) ∂P ∧
      (∫ x, Real.exp (-θ * F x) ∂P) ≤
        max (∫ x, Real.exp (-b₀ * F x) ∂P) (∫ x, Real.exp (-b₁ * F x) ∂P) := by
  intro θ hθ
  have hmeas : Measurable (fun x => Real.exp (-θ * F x)) :=
    Real.measurable_exp.comp (measurable_const.mul hF)
  have hint : Integrable (fun x => Real.exp (-θ * F x)) P := by
    refine (h₀.add h₁).mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    obtain ⟨l, m, hl, hm, hlm, hle⟩ := s116_exp_interp hb hθ (F x)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have p0 := (Real.exp_pos (-b₀ * F x)).le
    have p1 := (Real.exp_pos (-b₁ * F x)).le
    simp only [Pi.add_apply]
    nlinarith
  refine ⟨hint, ?_, ?_⟩
  · -- Jensen
    have hJ := convexOn_exp.map_integral_le (μ := P) (f := fun x => -θ * F x)
      Real.continuous_exp.continuousOn isClosed_univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
      (hFi.const_mul (-θ)) hint
    simp only [integral_const_mul] at hJ
    exact hJ
  · obtain ⟨l, m, hl, hm, hlm, hθe⟩ := s116_weights hb hθ
    have hpt : ∀ x, Real.exp (-θ * F x) ≤ l * Real.exp (-b₀ * F x) + m * Real.exp (-b₁ * F x) := by
      intro x
      have h := convexOn_exp.2 (Set.mem_univ (-b₀ * F x)) (Set.mem_univ (-b₁ * F x)) hl hm hlm
      have e : -θ * F x = l • (-b₀ * F x) + m • (-b₁ * F x) := by
        simp only [smul_eq_mul]; rw [← hθe]; ring
      rw [e]; simpa using h
    calc ∫ x, Real.exp (-θ * F x) ∂P
        ≤ ∫ x, (l * Real.exp (-b₀ * F x) + m * Real.exp (-b₁ * F x)) ∂P :=
          integral_mono hint ((h₀.const_mul l).add (h₁.const_mul m)) hpt
      _ = l * ∫ x, Real.exp (-b₀ * F x) ∂P + m * ∫ x, Real.exp (-b₁ * F x) ∂P := by
          rw [integral_add (h₀.const_mul l) (h₁.const_mul m), integral_const_mul, integral_const_mul]
      _ ≤ l * max (∫ x, Real.exp (-b₀ * F x) ∂P) (∫ x, Real.exp (-b₁ * F x) ∂P)
            + m * max (∫ x, Real.exp (-b₀ * F x) ∂P) (∫ x, Real.exp (-b₁ * F x) ∂P) :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) hl)
            (mul_le_mul_of_nonneg_left (le_max_right _ _) hm)
      _ = _ := by rw [← add_mul, hlm, one_mul]

end HRS.MS.S116

end
