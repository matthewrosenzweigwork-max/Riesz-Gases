import HRS.MS.SuppU8Aux13
import HRS.MS.SuppU8Aux2

/-!
# Worker U8 aux 14: symmetry of the singular integral (Fubini in `(x, y)` and translation)
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace HRS.U8

variable {d : ℕ}

theorem u8_duality (hd : 1 ≤ d) (m : ℕ) (α : ℝ)
    (φ v : EuclideanSpace ℝ (Fin d) → ℂ)
    (hφc : Continuous φ) (hφi : Integrable φ) (hvc : Continuous v) (Bv : ℝ)
    (hvb : ∀ x, ‖v x‖ ≤ Bv) (γ Cφ Cv : ℝ) (hγ : (d : ℝ) < γ)
    (hφP1 : ∀ x, Integrable (fun y => ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) φ x))
    (hφP2 : ∀ x, ∫ y, ‖‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) φ x‖ ≤
      Cφ * (1 + ‖x‖) ^ (-γ))
    (hvP1 : ∀ x, Integrable (fun y => ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) v x))
    (hvP2 : ∀ x, ∫ y, ‖‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) v x‖ ≤ Cv) :
    (∫ x, v x * ∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) φ x) =
      ∫ x, (∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) v x) * φ x := by
  have : NeZero d := ⟨by omega⟩
  have hKm : Measurable (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖ ^ (-((d : ℝ) + α))) :=
    measurable_norm.pow_const _
  obtain ⟨f, hf⟩ : ∃ f : (EuclideanSpace ℝ (Fin d) → ℂ) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) → ℂ, f = fun u x y =>
        ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) u x := ⟨_, rfl⟩
  have hfm : ∀ u : EuclideanSpace ℝ (Fin d) → ℂ, Continuous u → Measurable
      (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => f u p.1 p.2) := by
    intro u hu
    have hc : Continuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        u8_fd (u8_L m p.2) u p.1) := (u8_L_cont_joint m hu).comp continuous_swap
    rw [hf]
    exact (hKm.comp measurable_snd).smul hc.measurable
  have hfeq : ∀ u x y, f u x y = ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) u x :=
    fun u x y => by rw [hf]
  simp only [← hfeq] at hφP1 hφP2 hvP1 hvP2 ⊢
  have hmφ := hfm φ hφc
  have hmv := hfm v hvc
  have hIA : Integrable (Function.uncurry fun x y => v x * f φ x y)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) := by
    have hm : AEStronglyMeasurable (Function.uncurry fun x y => v x * f φ x y)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) :=
      ((hvc.measurable.comp measurable_fst).mul hmφ).aestronglyMeasurable
    rw [integrable_prod_iff hm]
    refine ⟨Filter.Eventually.of_forall (fun x => (hφP1 x).const_mul (v x)), ?_⟩
    have hmaj : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Bv * (Cφ * (1 + ‖x‖) ^ (-γ))) :=
      ((integrable_one_add_norm (by simpa using hγ)).const_mul Cφ).const_mul Bv
    refine Integrable.mono' hmaj hm.norm.integral_prod_right' (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _))]
    have h1 : ∀ y, ‖Function.uncurry (fun x y => v x * f φ x y) (x, y)‖ =
        ‖v x‖ * ‖f φ x y‖ := fun y => by simp [Function.uncurry, norm_mul]
    have h2 : ∫ y, ‖Function.uncurry (fun x y => v x * f φ x y) (x, y)‖ =
        ‖v x‖ * ∫ y, ‖f φ x y‖ := by
      rw [← integral_const_mul]
      congr 1; funext y; exact h1 y
    rw [h2]
    exact mul_le_mul (hvb x) (hφP2 x) (integral_nonneg (fun y => norm_nonneg _))
      ((norm_nonneg _).trans (hvb x))
  have hIB : Integrable (Function.uncurry fun x y => f v x y * φ x)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) := by
    have hm : AEStronglyMeasurable (Function.uncurry fun x y => f v x y * φ x)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) :=
      (hmv.mul (hφc.measurable.comp measurable_fst)).aestronglyMeasurable
    rw [integrable_prod_iff hm]
    refine ⟨Filter.Eventually.of_forall (fun x => (hvP1 x).mul_const (φ x)), ?_⟩
    have hmaj : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Cv * ‖φ x‖) :=
      hφi.norm.const_mul Cv
    refine Integrable.mono' hmaj hm.norm.integral_prod_right' (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _))]
    have h1 : ∀ y, ‖Function.uncurry (fun x y => f v x y * φ x) (x, y)‖ =
        ‖f v x y‖ * ‖φ x‖ := fun y => by simp [Function.uncurry, norm_mul]
    have h2 : ∫ y, ‖Function.uncurry (fun x y => f v x y * φ x) (x, y)‖ =
        (∫ y, ‖f v x y‖) * ‖φ x‖ := by
      rw [← integral_mul_const]
      congr 1; funext y; exact h1 y
    rw [h2]
    exact mul_le_mul_of_nonneg_right (hvP2 x) (norm_nonneg _)
  have e1 : ∀ x, v x * (∫ y, f φ x y) = ∫ y, v x * f φ x y := by
    intro x; exact (integral_const_mul _ _).symm
  have e2 : ∀ x, (∫ y, f v x y) * φ x = ∫ y, f v x y * φ x := by
    intro x; exact (integral_mul_const _ _).symm
  simp_rw [e1, e2]
  rw [integral_integral_swap hIA, integral_integral_swap hIB]
  congr 1; funext y
  have hL : ∀ (g : EuclideanSpace ℝ (Fin d) → ℂ), u8_fd ((u8_L m y).map Neg.neg) g =
      u8_fd (u8_L m y) g := fun g => u8_fd_perm (u8_L_neg_perm m y) g
  have hadj := u8_fd_adjoint (u8_L m y) v φ hvc ⟨Bv, hvb⟩ hφc hφi
  rw [hL v] at hadj
  have s1 : ∀ x, v x * f φ x y = ‖y‖ ^ (-((d : ℝ) + α)) • (v x * u8_fd (u8_L m y) φ x) := by
    intro x; rw [hfeq]; exact mul_smul_comm _ _ _
  have s2 : ∀ x, f v x y * φ x = ‖y‖ ^ (-((d : ℝ) + α)) • (u8_fd (u8_L m y) v x * φ x) := by
    intro x; rw [hfeq]; exact smul_mul_assoc _ _ _
  simp_rw [s1, s2]
  rw [integral_smul, integral_smul, hadj]

end HRS.U8
