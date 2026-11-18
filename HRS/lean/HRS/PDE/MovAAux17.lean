import HRS.PDE.MovAAux16

/-!
# MOVA Aux17: a continuous function with vanishing pairings against smooth tests vanishes; time derivative
of the pairings.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_isCk_two_of_smooth {ψ : Torus d → ℝ} (h : Torus.IsSmooth ψ) : Torus.IsCk 2 ψ :=
  ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ψ) from h)
    (WithTop.coe_le_coe.2 le_top)

theorem mova_eq_zero_of_integral_zero {f : Torus d → ℝ} (hf : Continuous f)
    (h : ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ → ∫ x, ψ x * f x = 0) : ∀ x, f x = 0 := by
  have hint : ∀ g : Torus d → ℝ, Continuous g → Integrable g := fun g hg => mova_int_cont hg
  have hff : Continuous fun x => f x * f x := hf.mul hf
  have habs : Continuous fun x => |f x| := hf.abs
  have key : ∀ ε : ℝ, 0 < ε → ∫ x, f x * f x ≤ ε * ∫ x, |f x| := by
    intro ε hε
    obtain ⟨ψ, hψs, hψ⟩ := d1_exists_smooth_approx hf hε
    have hψc : Continuous ψ := mova_continuous_of_isCk (mova_isCk_two_of_smooth hψs)
    have h0 := h ψ (mova_isCk_two_of_smooth hψs)
    have c1 : Continuous fun x => f x * (f x - ψ x) := hf.mul (hf.sub hψc)
    have c2 : Continuous fun x => ψ x * f x := hψc.mul hf
    have e : ∫ x, f x * f x = (∫ x, f x * (f x - ψ x)) + ∫ x, ψ x * f x := by
      rw [← integral_add (hint _ c1) (hint _ c2)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only; ring
    rw [e, h0, add_zero]
    calc ∫ x, f x * (f x - ψ x) ≤ ∫ x, ε * |f x| := by
          refine integral_mono (hint _ c1) (hint _ (continuous_const.mul habs)) fun x => ?_
          simp only
          calc f x * (f x - ψ x) ≤ |f x * (f x - ψ x)| := le_abs_self _
            _ = |f x| * |f x - ψ x| := abs_mul _ _
            _ ≤ |f x| * ε := mul_le_mul_of_nonneg_left (hψ x) (abs_nonneg _)
            _ = ε * |f x| := mul_comm _ _
      _ = ε * ∫ x, |f x| := integral_const_mul _ _
  have hA : 0 ≤ ∫ x, |f x| := integral_nonneg fun x => abs_nonneg _
  have hB : 0 ≤ ∫ x, f x * f x := integral_nonneg fun x => mul_self_nonneg _
  have hI : ∫ x, f x * f x = 0 := by
    obtain ⟨A, hAd⟩ : ∃ A, A = ∫ x, |f x| := ⟨_, rfl⟩
    obtain ⟨B, hBd⟩ : ∃ B, B = ∫ x, f x * f x := ⟨_, rfl⟩
    rw [← hAd] at hA key
    rw [← hBd] at hB key ⊢
    by_contra hne
    have hpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hne)
    have hden : 0 < 2 * (A + 1) := by linarith
    have := key (B / (2 * (A + 1))) (div_pos hpos hden)
    have h2 : B / (2 * (A + 1)) * A < B := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
    linarith
  have hae : (fun x => f x * f x) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg _) (hint _ hff)).1 hI
  have hae2 : f =ᵐ[volume] 0 := by
    filter_upwards [hae] with x hx
    simpa using hx
  have := (Continuous.ae_eq_iff_eq (μ := (volume : Measure (Torus d))) hf continuous_const).1 hae2
  intro x
  exact congrFun this x

end HRS
