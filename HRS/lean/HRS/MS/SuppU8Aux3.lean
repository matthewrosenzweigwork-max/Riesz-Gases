import Mathlib

/-!
# Worker U8 aux 3: radial integrals of powers on `ℝ^d`
-/

noncomputable section

open MeasureTheory Metric Set

namespace HRS.U8

variable {d : ℕ}

/-- The surface-type constant `d · |B(0,1)|`. -/
def u8_cd (d : ℕ) : ℝ := d * (volume : Measure (EuclideanSpace ℝ (Fin d))).real (ball 0 1)

theorem u8_cd_pos (hd : 1 ≤ d) : 0 < u8_cd d := by
  unfold u8_cd
  have : (0 : ℝ) < d := by exact_mod_cast hd
  have h2 : 0 < (volume : Measure (EuclideanSpace ℝ (Fin d))).real (ball 0 1) :=
    ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  positivity

theorem u8_ball_integral (hd : 1 ≤ d) (ρ : ℝ) (hρ : 0 < ρ) (f : ℝ → ℝ) :
    ∫ x in ball (0 : EuclideanSpace ℝ (Fin d)) ρ, f ‖x‖ =
      u8_cd d * ∫ y in Ioo 0 ρ, y ^ (d - 1) * f y := by
  have : NeZero d := ⟨by omega⟩
  have e1 : ∫ x in ball (0 : EuclideanSpace ℝ (Fin d)) ρ, f ‖x‖ =
      ∫ x : EuclideanSpace ℝ (Fin d), ((Iio ρ).indicator f) ‖x‖ := by
    rw [← integral_indicator measurableSet_ball]
    congr 1; funext x
    by_cases hx : ‖x‖ < ρ
    · simp [hx]
    · simp [hx]
  have this : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * (Iio ρ).indicator f y =
      ∫ y in Ioo 0 ρ, y ^ (d - 1) * f y := by
    rw [← integral_indicator measurableSet_Ioi]
    rw [show Ioo (0 : ℝ) ρ = Ioi 0 ∩ Iio ρ by ext; simp,
      ← integral_indicator (measurableSet_Ioi.inter measurableSet_Iio)]
    congr 1; funext y
    by_cases h1 : 0 < y <;> by_cases h2 : y < ρ <;> simp [h1, h2, indicator]
  rw [e1, integral_fun_norm_addHaar volume, finrank_euclideanSpace_fin]
  unfold u8_cd
  simp only [nsmul_eq_mul, smul_eq_mul]
  rw [this]
  ring

theorem u8_pow_mul_rpow (hd : 1 ≤ d) (y : ℝ) (hy : 0 < y) (s : ℝ) :
    y ^ (d - 1) * y ^ s = y ^ (s + d - 1) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hy, Nat.cast_sub hd]
  congr 1; push_cast; ring

/-- Integrability and value of `‖y‖^(η-d)` on a ball. -/
theorem u8_near_int (hd : 1 ≤ d) (η ρ : ℝ) (hη : 0 < η) (hρ : 0 < ρ) :
    IntegrableOn (fun y : EuclideanSpace ℝ (Fin d) => ‖y‖ ^ (η - d)) (ball 0 ρ) ∧
      ∫ y in ball (0 : EuclideanSpace ℝ (Fin d)) ρ, ‖y‖ ^ (η - d) = u8_cd d * (ρ ^ η / η) := by
  have : NeZero d := ⟨by omega⟩
  have hfun : ∀ y ∈ Ioo (0 : ℝ) ρ, y ^ (d - 1) * y ^ (η - d) = y ^ (η - 1) := by
    intro y hy
    rw [u8_pow_mul_rpow hd y hy.1]
    congr 1; ring
  have hint : IntegrableOn (fun y : ℝ => y ^ (d - 1) • y ^ (η - d)) (Ioo 0 ρ) := by
    have h1 : IntegrableOn (fun y : ℝ => y ^ (η - 1)) (Ioo 0 ρ) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ρ) (r := η - 1)
        (by linarith))
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hρ.le] at this
      exact this
    refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioo
    simp only [smul_eq_mul]
    rw [hfun y hy]
  refine ⟨?_, ?_⟩
  · rw [integrableOn_fun_norm_addHaar volume (f := fun y : ℝ => y ^ (η - d)),
      finrank_euclideanSpace_fin]
    exact hint
  · rw [u8_ball_integral hd ρ hρ (fun y => y ^ (η - d))]
    congr 1
    rw [setIntegral_congr_fun measurableSet_Ioo (fun y hy => hfun y hy)]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ.le,
      integral_rpow (Or.inl (by linarith))]
    have : η - 1 + 1 = η := by ring
    rw [this, Real.zero_rpow hη.ne']
    ring

/-- Integrability and value of `‖y‖^(-d-η)` outside a ball. -/
theorem u8_far_int (hd : 1 ≤ d) (η ρ : ℝ) (hη : 0 < η) (hρ : 0 < ρ) :
    Integrable ((ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ.indicator
      (fun y => ‖y‖ ^ (-(d : ℝ) - η))) ∧
      ∫ y, ((ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ.indicator
        (fun y => ‖y‖ ^ (-(d : ℝ) - η))) y = u8_cd d * (ρ ^ (-η) / η) := by
  have : NeZero d := ⟨by omega⟩
  set F : ℝ → ℝ := fun y => y ^ (-η - 1) with hF
  set g : ℝ → ℝ := (Ici ρ).indicator (fun r => r ^ (-(d : ℝ) - η)) with hg
  have hfun : ((ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ.indicator
        (fun y => ‖y‖ ^ (-(d : ℝ) - η))) = fun y => g ‖y‖ := by
    funext y
    by_cases h : ρ ≤ ‖y‖
    · have h1 : y ∈ (ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ := by simpa using h
      simp [hg, h, h1]
    · have h1 : y ∉ (ball (0 : EuclideanSpace ℝ (Fin d)) ρ)ᶜ := by simpa using h
      simp [hg, h, h1]
  have hy : ∀ y ∈ Ioi (0 : ℝ), y ^ (d - 1) • g y = (Ici ρ).indicator F y := by
    intro y hy0
    by_cases h : ρ ≤ y
    · simp only [hg, hF, smul_eq_mul, indicator_of_mem (mem_Ici.2 h)]
      rw [u8_pow_mul_rpow hd y hy0]
      congr 1; ring
    · simp [hg, hF, h]
  have hFint : IntegrableOn F (Ici ρ) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by linarith) hρ
  have hind : Integrable ((Ici ρ).indicator F) := (integrable_indicator_iff measurableSet_Ici).2 hFint
  refine ⟨?_, ?_⟩
  · rw [hfun, integrable_fun_norm_addHaar volume (f := g), finrank_euclideanSpace_fin]
    exact (hind.integrableOn).congr_fun (fun y hy0 => (hy y hy0).symm) measurableSet_Ioi
  · rw [hfun, integral_fun_norm_addHaar volume g, finrank_euclideanSpace_fin]
    unfold u8_cd
    simp only [nsmul_eq_mul, smul_eq_mul]
    have h1 : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * g y = ρ ^ (-η) / η := by
      have : ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * g y = ∫ y in Ioi (0 : ℝ), (Ici ρ).indicator F y :=
        setIntegral_congr_fun measurableSet_Ioi (fun y hy0 => by simpa using hy y hy0)
      rw [this, ← integral_indicator measurableSet_Ioi]
      have : (Ioi (0 : ℝ)).indicator ((Ici ρ).indicator F) = (Ici ρ).indicator F := by
        funext y
        by_cases h : ρ ≤ y
        · have : y ∈ Ioi (0 : ℝ) := lt_of_lt_of_le hρ h
          simp [indicator_of_mem this]
        · simp [h]
      rw [this, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
        integral_Ioi_rpow_of_lt (by linarith) hρ]
      have : -η - 1 + 1 = -η := by ring
      rw [this]
      field_simp
    rw [h1]
    ring

end HRS.U8
