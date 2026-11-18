import HRS.Main.A34Aux7

/-!
# Packet A34, helper 8: the random part `A η°(U φ)` of the statistic
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

section XPart

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {η : Ω → (Torus d → ℝ) → ℝ} {m₀ : ℕ} {Cin : ℝ}

/-- hypotheses of `FunctionalMoment` in unbundled form -/
structure XHyp (P : Measure Ω) (η : Ω → (Torus d → ℝ) → ℝ) (m₀ : ℕ) (Cin : ℝ) : Prop where
  meas : ∀ ψ : Torus d → ℝ, Measurable fun ω => η ω ψ
  linear : ∀ ω, ∀ ψ χ : Torus d → ℝ, ∀ c : ℝ, MemSobolev (m₀ : ℝ) ψ → MemSobolev (m₀ : ℝ) χ →
    η ω (c • ψ + χ) = c * η ω ψ + η ω χ
  second_moment : ∀ ψ : Torus d → ℝ, MemSobolev (m₀ : ℝ) ψ → Continuous ψ →
    ∫⁻ ω, ENNReal.ofReal ((η ω ψ) ^ 2) ∂P ≤ ENNReal.ofReal (Cin ^ 2 * sobolevNorm (m₀ : ℝ) ψ ^ 2)

theorem a34_X_integrable (h : XHyp P η m₀ Cin) {ψ : Torus d → ℝ} (hψ : MemSobolev (m₀ : ℝ) ψ)
    (hψc : Continuous ψ) (A : ℝ) : Integrable (fun ω => A * η ω ψ) P := by
  obtain ⟨hm, -⟩ := a34_moment_abs h.meas h.second_moment hψ hψc
  exact (hm.integrable one_le_two).const_mul A

theorem a34_memSobolev_sub {a : ℝ} {ψ₁ ψ₂ : Torus d → ℝ} (h₁ : MemSobolev a ψ₁)
    (h₂ : MemSobolev a ψ₂) (c₁ : Continuous ψ₁) (c₂ : Continuous ψ₂) :
    MemSobolev a (fun x => ψ₁ x - ψ₂ x) := by
  refine memSobolev_of_memHs _ _ (ClassicalAux.memLp_two_of_continuous (c₁.sub c₂)) ?_
  rw [ClassicalAux.coeffOf_sub (ClassicalAux.integrable_of_continuous c₁)
    (ClassicalAux.integrable_of_continuous c₂)]
  exact memHs_sub (hsNormSq_coeffOf a ψ₁ h₁).1 (hsNormSq_coeffOf a ψ₂ h₂).1

/-- coupled difference -/
theorem a34_X_diff (h : XHyp P η m₀ Cin) {ψ₁ ψ₂ : Torus d → ℝ} (h₁ : MemSobolev (m₀ : ℝ) ψ₁)
    (h₂ : MemSobolev (m₀ : ℝ) ψ₂) (c₁ : Continuous ψ₁) (c₂ : Continuous ψ₂) (A₁ A₂ : ℝ) :
    ∫ ω, |A₁ * η ω ψ₁ - A₂ * η ω ψ₂| ∂P ≤
      |A₁ - A₂| * (|Cin| * sobolevNorm (m₀ : ℝ) ψ₁) +
        |A₂| * (|Cin| * sobolevNorm (m₀ : ℝ) (fun x => ψ₁ x - ψ₂ x)) := by
  have hdm := a34_memSobolev_sub h₁ h₂ c₁ c₂
  have hdc : Continuous fun x => ψ₁ x - ψ₂ x := c₁.sub c₂
  obtain ⟨hm1, hb1⟩ := a34_moment_abs h.meas h.second_moment h₁ c₁
  obtain ⟨hmd, hbd⟩ := a34_moment_abs h.meas h.second_moment hdm hdc
  have hi1 : Integrable (fun ω => |η ω ψ₁|) P := (hm1.integrable one_le_two).abs
  have hid : Integrable (fun ω => |η ω (fun x => ψ₁ x - ψ₂ x)|) P :=
    (hmd.integrable one_le_two).abs
  have hlin : ∀ ω, η ω (fun x => ψ₁ x - ψ₂ x) = η ω ψ₁ - η ω ψ₂ := by
    intro ω
    have := h.linear ω ψ₂ ψ₁ (-1) h₂ h₁
    have e : (fun x => ψ₁ x - ψ₂ x) = (-1 : ℝ) • ψ₂ + ψ₁ := by
      funext x; simp [sub_eq_add_neg, add_comm]
    rw [e, this]; ring
  have hpt : ∀ ω, |A₁ * η ω ψ₁ - A₂ * η ω ψ₂| ≤
      |A₁ - A₂| * |η ω ψ₁| + |A₂| * |η ω (fun x => ψ₁ x - ψ₂ x)| := by
    intro ω
    rw [hlin ω]
    have : A₁ * η ω ψ₁ - A₂ * η ω ψ₂ = (A₁ - A₂) * η ω ψ₁ + A₂ * (η ω ψ₁ - η ω ψ₂) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
  have hI1 : Integrable (fun ω => |A₁ * η ω ψ₁ - A₂ * η ω ψ₂|) P :=
    ((a34_X_integrable h h₁ c₁ A₁).sub (a34_X_integrable h h₂ c₂ A₂)).abs
  calc ∫ ω, |A₁ * η ω ψ₁ - A₂ * η ω ψ₂| ∂P
      ≤ ∫ ω, (|A₁ - A₂| * |η ω ψ₁| + |A₂| * |η ω (fun x => ψ₁ x - ψ₂ x)|) ∂P :=
        integral_mono hI1 ((hi1.const_mul _).add (hid.const_mul _)) hpt
    _ = |A₁ - A₂| * ∫ ω, |η ω ψ₁| ∂P + |A₂| * ∫ ω, |η ω (fun x => ψ₁ x - ψ₂ x)| ∂P := by
        rw [integral_add (hi1.const_mul _) (hid.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by
        gcongr

/-- crude bound -/
theorem a34_X_crude (h : XHyp P η m₀ Cin) {ψ₁ ψ₂ : Torus d → ℝ} (h₁ : MemSobolev (m₀ : ℝ) ψ₁)
    (h₂ : MemSobolev (m₀ : ℝ) ψ₂) (c₁ : Continuous ψ₁) (c₂ : Continuous ψ₂) (A₁ A₂ : ℝ) :
    ∫ ω, |A₁ * η ω ψ₁ - A₂ * η ω ψ₂| ∂P ≤
      |A₁| * (|Cin| * sobolevNorm (m₀ : ℝ) ψ₁) + |A₂| * (|Cin| * sobolevNorm (m₀ : ℝ) ψ₂) := by
  obtain ⟨hm1, hb1⟩ := a34_moment_abs h.meas h.second_moment h₁ c₁
  obtain ⟨hm2, hb2⟩ := a34_moment_abs h.meas h.second_moment h₂ c₂
  have hi1 : Integrable (fun ω => |η ω ψ₁|) P := (hm1.integrable one_le_two).abs
  have hi2 : Integrable (fun ω => |η ω ψ₂|) P := (hm2.integrable one_le_two).abs
  have hI1 : Integrable (fun ω => |A₁ * η ω ψ₁ - A₂ * η ω ψ₂|) P :=
    ((a34_X_integrable h h₁ c₁ A₁).sub (a34_X_integrable h h₂ c₂ A₂)).abs
  calc ∫ ω, |A₁ * η ω ψ₁ - A₂ * η ω ψ₂| ∂P
      ≤ ∫ ω, (|A₁| * |η ω ψ₁| + |A₂| * |η ω ψ₂|) ∂P :=
        integral_mono hI1 ((hi1.const_mul _).add (hi2.const_mul _)) (fun ω => by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul])
    _ = |A₁| * ∫ ω, |η ω ψ₁| ∂P + |A₂| * ∫ ω, |η ω ψ₂| ∂P := by
        rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ _ := by gcongr

end XPart

end HRS.A34
