import HRS.MS.S111X1Aux3

/-!
# S11.1 X1, part 4: linearity and the L2 bound of the susceptibility covariance
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

/-- Cauchy-Schwarz for `L²` functions, in discriminant form. -/
theorem x1_cs_L2 {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have hff : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have hgg : Integrable (fun x => g x ^ 2) μ := hg.integrable_sq
  have hfg : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  have h := discrim_le_zero (a := ∫ x, g x ^ 2 ∂μ) (b := 2 * ∫ x, f x * g x ∂μ)
    (c := ∫ x, f x ^ 2 ∂μ) (fun l => by
      have : 0 ≤ ∫ x, (f x + l * g x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
      have e : ∫ x, (f x + l * g x) ^ 2 ∂μ =
          (∫ x, f x ^ 2 ∂μ) + 2 * l * (∫ x, f x * g x ∂μ) + l ^ 2 * ∫ x, g x ^ 2 ∂μ := by
        have e1 : ∀ x, (f x + l * g x) ^ 2 =
            f x ^ 2 + 2 * l * (f x * g x) + l ^ 2 * g x ^ 2 := fun x => by ring
        simp_rw [e1]
        have hi : Integrable (fun x => f x ^ 2 + 2 * l * (f x * g x)) μ :=
          hff.add (hfg.const_mul _)
        rw [integral_add hi (hgg.const_mul _),
          integral_add hff (hfg.const_mul _), integral_const_mul, integral_const_mul]
      rw [e] at this
      nlinarith)
  unfold discrim at h
  nlinarith

/-- `responseInverse` is square integrable. -/
theorem x1_RI_memLp (g : Euc d → ℝ) (μ : Measure (Euc d)) (γ : ℝ) (b : Euc d → ℝ) :
    MemLp (HRS.Whole.responseInverse g μ γ b) 2 μ := by
  classical
  unfold HRS.Whole.responseInverse
  split_ifs with h
  · exact h.choose_spec.1.1
  · exact MemLp.zero

theorem x1_projMean_memLp (μ : Measure (Euc d)) [IsFiniteMeasure μ] {a : Euc d → ℝ}
    (ha : MemLp a 2 μ) : MemLp (HRS.Whole.projMean μ a) 2 μ := by
  unfold HRS.Whole.projMean
  exact ha.sub (memLp_const _)

theorem x1_projMean_lin (μ : Measure (Euc d)) [IsFiniteMeasure μ] {a₁ a₂ : Euc d → ℝ}
    (h₁ : MemLp a₁ 2 μ) (h₂ : MemLp a₂ 2 μ) (c : ℝ) :
    HRS.Whole.projMean μ (fun y => a₁ y + c * a₂ y) =
      fun x => HRS.Whole.projMean μ a₁ x + c * HRS.Whole.projMean μ a₂ x := by
  funext x
  unfold HRS.Whole.projMean HRS.Whole.pair
  rw [integral_add (h₁.integrable one_le_two) ((h₂.integrable one_le_two).const_mul c),
    integral_const_mul]
  ring

theorem x1_suscept_lin (g : Euc d → ℝ) (μ : Measure (Euc d)) [IsFiniteMeasure μ] (γ : ℝ)
    {a₁ a₂ : Euc d → ℝ} (h₁ : MemLp a₁ 2 μ) (h₂ : MemLp a₂ 2 μ) (c : ℝ) (b : Euc d → ℝ) :
    HRS.Whole.susceptibilityCov g μ γ (fun y => a₁ y + c * a₂ y) b =
      HRS.Whole.susceptibilityCov g μ γ a₁ b + c * HRS.Whole.susceptibilityCov g μ γ a₂ b := by
  unfold HRS.Whole.susceptibilityCov HRS.Whole.l2Inner
  rw [x1_projMean_lin μ h₁ h₂ c]
  have hR := x1_RI_memLp g μ γ b
  have i1 : Integrable (fun x => HRS.Whole.projMean μ a₁ x * HRS.Whole.responseInverse g μ γ b x) μ :=
    (x1_projMean_memLp μ h₁).integrable_mul hR
  have i2 : Integrable (fun x => HRS.Whole.projMean μ a₂ x * HRS.Whole.responseInverse g μ γ b x) μ :=
    (x1_projMean_memLp μ h₂).integrable_mul hR
  have e : ∀ x, (HRS.Whole.projMean μ a₁ x + c * HRS.Whole.projMean μ a₂ x) *
      HRS.Whole.responseInverse g μ γ b x =
      HRS.Whole.projMean μ a₁ x * HRS.Whole.responseInverse g μ γ b x +
        c * (HRS.Whole.projMean μ a₂ x * HRS.Whole.responseInverse g μ γ b x) := fun x => by ring
  simp_rw [e]
  rw [integral_add i1 (i2.const_mul c), integral_const_mul]

/-- the `L²` bound of the susceptibility covariance in terms of the response of the second argument -/
theorem x1_suscept_bound (g : Euc d → ℝ) (μ : Measure (Euc d)) [IsFiniteMeasure μ] (γ : ℝ)
    {a b : Euc d → ℝ} (ha : MemLp a 2 μ) :
    |HRS.Whole.susceptibilityCov g μ γ a b| ≤
      Real.sqrt (∫ x, HRS.Whole.projMean μ a x ^ 2 ∂μ) *
        Real.sqrt (∫ x, HRS.Whole.responseInverse g μ γ b x ^ 2 ∂μ) := by
  unfold HRS.Whole.susceptibilityCov HRS.Whole.l2Inner
  have hcs := x1_cs_L2 (x1_projMean_memLp μ ha) (x1_RI_memLp g μ γ b)
  rw [← Real.sqrt_mul (integral_nonneg fun x => sq_nonneg _)]
  exact Real.abs_le_sqrt hcs

end HRS.MS.S111X1
