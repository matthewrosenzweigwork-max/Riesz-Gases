import HRS.MS.S111X1Aux1

/-!
# S11.1 X1, part 2: bilinearity and Cauchy-Schwarz for the noise pairing
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

theorem x1_gradient_add_smul {a b : Euc d → ℝ} (c : ℝ) {x : Euc d} (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) :
    gradient (fun y => a y + c * b y) x = gradient a x + c • gradient b x := by
  unfold gradient
  rw [fderiv_fun_add ha (hb.const_mul c), fderiv_const_mul hb]
  simp [map_add, map_smul]

/-- the discriminant form of Cauchy-Schwarz for a double integral of an inner product -/
theorem x1_cs {ρ : Euc d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (u v : ℝ → Euc d → Euc d) (T0 : ℝ)
    (hxuu : ∀ s ∈ Set.Icc (0 : ℝ) T0, Integrable fun x => inner ℝ (u s x) (u s x) * ρ x)
    (hxvv : ∀ s ∈ Set.Icc (0 : ℝ) T0, Integrable fun x => inner ℝ (v s x) (v s x) * ρ x)
    (hxuv : ∀ s ∈ Set.Icc (0 : ℝ) T0, Integrable fun x => inner ℝ (u s x) (v s x) * ρ x)
    (hsuu : IntegrableOn (fun s => ∫ x, inner ℝ (u s x) (u s x) * ρ x) (Set.Icc (0 : ℝ) T0))
    (hsvv : IntegrableOn (fun s => ∫ x, inner ℝ (v s x) (v s x) * ρ x) (Set.Icc (0 : ℝ) T0))
    (hsuv : IntegrableOn (fun s => ∫ x, inner ℝ (u s x) (v s x) * ρ x) (Set.Icc (0 : ℝ) T0)) :
    (∫ s in Set.Icc (0 : ℝ) T0, ∫ x, inner ℝ (u s x) (v s x) * ρ x) ^ 2 ≤
      (∫ s in Set.Icc (0 : ℝ) T0, ∫ x, inner ℝ (u s x) (u s x) * ρ x) *
        (∫ s in Set.Icc (0 : ℝ) T0, ∫ x, inner ℝ (v s x) (v s x) * ρ x) := by
  set Iuu := ∫ s in Set.Icc (0 : ℝ) T0, ∫ x, inner ℝ (u s x) (u s x) * ρ x with hIuu
  set Ivv := ∫ s in Set.Icc (0 : ℝ) T0, ∫ x, inner ℝ (v s x) (v s x) * ρ x with hIvv
  set Iuv := ∫ s in Set.Icc (0 : ℝ) T0, ∫ x, inner ℝ (u s x) (v s x) * ρ x with hIuv
  have key : ∀ l : ℝ, 0 ≤ Iuu + 2 * l * Iuv + l ^ 2 * Ivv := by
    intro l
    have hinner : ∀ s ∈ Set.Icc (0 : ℝ) T0,
        ∫ x, inner ℝ (u s x + l • v s x) (u s x + l • v s x) * ρ x =
          (∫ x, inner ℝ (u s x) (u s x) * ρ x) + 2 * l * (∫ x, inner ℝ (u s x) (v s x) * ρ x) +
            l ^ 2 * ∫ x, inner ℝ (v s x) (v s x) * ρ x := by
      intro s hs
      have e : ∀ x, inner ℝ (u s x + l • v s x) (u s x + l • v s x) * ρ x =
          inner ℝ (u s x) (u s x) * ρ x + 2 * l * (inner ℝ (u s x) (v s x) * ρ x) +
            l ^ 2 * (inner ℝ (v s x) (v s x) * ρ x) := by
        intro x
        simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
          real_inner_comm (u s x) (v s x), conj_trivial]
        ring
      simp_rw [e]
      have hi1 : Integrable (fun x => inner ℝ (u s x) (u s x) * ρ x +
          2 * l * (inner ℝ (u s x) (v s x) * ρ x)) :=
        (hxuu s hs).add ((hxuv s hs).const_mul _)
      rw [integral_add hi1 ((hxvv s hs).const_mul _),
        integral_add (hxuu s hs) ((hxuv s hs).const_mul _), integral_const_mul, integral_const_mul]
    have hnn : 0 ≤ ∫ s in Set.Icc (0 : ℝ) T0, ∫ x, inner ℝ (u s x + l • v s x) (u s x + l • v s x) * ρ x := by
      refine setIntegral_nonneg measurableSet_Icc fun s _ => integral_nonneg fun x => ?_
      exact mul_nonneg real_inner_self_nonneg (hρ0 x)
    rw [setIntegral_congr_fun measurableSet_Icc hinner] at hnn
    have hj1 : IntegrableOn (fun s => (∫ x, inner ℝ (u s x) (u s x) * ρ x) +
        2 * l * ∫ x, inner ℝ (u s x) (v s x) * ρ x) (Set.Icc (0 : ℝ) T0) :=
      hsuu.add (hsuv.const_mul _)
    rw [integral_add hj1 (hsvv.const_mul _),
      integral_add hsuu (hsuv.const_mul _), integral_const_mul, integral_const_mul] at hnn
    exact hnn
  have hIvv0 : 0 ≤ Ivv := by
    refine setIntegral_nonneg measurableSet_Icc fun s _ => integral_nonneg fun x => ?_
    exact mul_nonneg real_inner_self_nonneg (hρ0 x)
  have hIuu0 : 0 ≤ Iuu := by
    refine setIntegral_nonneg measurableSet_Icc fun s _ => integral_nonneg fun x => ?_
    exact mul_nonneg real_inner_self_nonneg (hρ0 x)
  by_cases hv : Ivv = 0
  · -- then Iuv = 0
    have : Iuv = 0 := by
      by_contra hne
      have h1 := key (-(Iuu + 1) / (2 * Iuv))
      have h2 : 2 * (-(Iuu + 1) / (2 * Iuv)) * Iuv = -(Iuu + 1) := by field_simp
      rw [h2, hv] at h1
      linarith
    rw [this, hv]; simp
  · have hpos : 0 < Ivv := lt_of_le_of_ne hIvv0 (Ne.symm hv)
    have h1 := key (-Iuv / Ivv)
    field_simp at h1
    nlinarith

end HRS.MS.S111X1
