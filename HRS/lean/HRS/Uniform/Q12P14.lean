import HRS.Uniform.Q12P13

/-!
# Q12, Peyre part 14: the weak continuity equation with defect `π² τ²`
-/

noncomputable section

open HRS MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Real

namespace HRS.Uniform.Q12

variable {d : ℕ}

namespace PeyreData

variable (D : PeyreData d)

lemma continuous_f : Continuous D.f :=
  Torus.continuous_of_continuous_lift D.contDiff_lift_f.continuous

lemma continuous_g : Continuous D.g :=
  Torus.continuous_of_continuous_lift D.contDiff_lift_g.continuous

lemma continuous_rhoT (t : ℝ) : Continuous (D.rhoT t) :=
  (continuous_const.mul D.continuous_g).add (continuous_const.mul D.continuous_f)

lemma isProbDensity_rhoT (t : ℝ) : IsProbDensity (D.rhoT t) := by
  obtain ⟨h0, h1⟩ := theta_mem t
  refine ⟨fun x => ?_, (D.continuous_rhoT t).measurable, ?_⟩
  · unfold rhoT
    have := D.hf.nonneg x; have := D.hg.nonneg x
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (D.hg.nonneg x), mul_nonneg h0 (D.hf.nonneg x)]
  · unfold rhoT
    have hfi := q12_integrable_of_isProbDensity D.hf
    have hgi := q12_integrable_of_isProbDensity D.hg
    rw [integral_add (hgi.const_mul _) (hfi.const_mul _), integral_const_mul, integral_const_mul,
      D.hf.integral_one, D.hg.integral_one]
    ring

instance muT_prob (t : ℝ) : IsProbabilityMeasure (D.muT t) :=
  PDE.MFSemigroup.isProb_withDensityReal (D.isProbDensity_rhoT t)

lemma integral_muT (t : ℝ) (G : Torus d → ℝ) :
    ∫ x, G x ∂(D.muT t) = ∫ x, D.rhoT t x * G x :=
  PDE.MFSemigroup.pair_withDensityReal (D.isProbDensity_rhoT t) G

lemma abs_J_le {Φ : Euc d → ℝ} {B : ℝ} (hp : Torus.Per Φ) (hC : C2b B Φ) :
    |∫ x : Torus d, Φ (Torus.rep x) * (D.f x - D.g x)| ≤ 2 * B := by
  have hΦc : Continuous fun x : Torus d => Φ (Torus.rep x) :=
    Torus.continuous_descend hp hC.1.continuous
  have hfi := q12_integrable_of_isProbDensity D.hf
  have hgi := q12_integrable_of_isProbDensity D.hg
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hC.2 0).1
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (g := fun x => B * (D.f x + D.g x))
    ((hfi.add hgi).const_mul B) (Filter.Eventually.of_forall fun x => ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_mul]
    have h1 := (hC.2 (Torus.rep x)).1
    have hf0 := D.hf.nonneg x
    have hg0 := D.hg.nonneg x
    exact mul_le_mul h1 (by rw [abs_le]; constructor <;> linarith) (abs_nonneg _) hB0
  · rw [integral_const_mul, integral_add hfi hgi, D.hf.integral_one, D.hg.integral_one]
    linarith

/-- The weak continuity equation, with a defect of order `τ²`. -/
theorem weak_CE {t τ : ℝ} (hτ : 0 ≤ τ) {Φ : Euc d → ℝ} {B : ℝ} (hp : Torus.Per Φ) (hC : C2b B Φ) :
    |τ * ∫ x, fderiv ℝ Φ (Torus.rep x) (D.vf t (Torus.rep x)) ∂(D.muT t) +
      (Iw (D.muT t) Φ - Iw (D.muT (t + τ)) Φ)| ≤ π ^ 2 * τ ^ 2 * B := by
  obtain ⟨c₀, hc₀, -, hlow⟩ := D.exists_rho_lower
  have hΦc : Continuous Φ := hC.1.continuous
  have hΦr : Continuous fun x : Torus d => Φ (Torus.rep x) := Torus.continuous_descend hp hΦc
  set J : ℝ := ∫ x : Torus d, Φ (Torus.rep x) * (D.f x - D.g x) with hJ
  -- the transport term
  have hA : ∫ x, fderiv ℝ Φ (Torus.rep x) (D.vf t (Torus.rep x)) ∂(D.muT t) = theta' t * J := by
    rw [D.integral_muT]
    have hpt : ∀ x : Torus d, D.rhoT t x * fderiv ℝ Φ (Torus.rep x) (D.vf t (Torus.rep x)) =
        theta' t * fderiv ℝ Φ (Torus.rep x) (D.gradU (Torus.rep x)) := by
      intro x
      have hr : D.rho t (Torus.rep x) = D.rhoT t x := D.rho_rep t x
      have hne : D.rhoT t x ≠ 0 := (lt_of_lt_of_le hc₀ (hlow t x)).ne'
      unfold PeyreData.vf
      rw [map_smul, hr, smul_eq_mul]
      field_simp
    simp_rw [hpt]
    rw [integral_const_mul, D.ibp hp hC.1]
  -- the density term
  have hI : ∀ s : ℝ, Iw (D.muT s) Φ = ∫ x : Torus d, D.rhoT s x * Φ (Torus.rep x) := fun s => by
    unfold Iw; rw [D.integral_muT]
  have hdiff : Iw (D.muT t) Φ - Iw (D.muT (t + τ)) Φ = (theta t - theta (t + τ)) * J := by
    rw [hI, hI, hJ, ← integral_sub, ← integral_const_mul]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      unfold rhoT; ring
    · exact (D.continuous_rhoT t |>.mul hΦr).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact (D.continuous_rhoT (t + τ) |>.mul hΦr).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [hA, hdiff]
  have hJ2 := D.abs_J_le hp hC
  have hT := theta_taylor t hτ
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hC.2 0).1
  calc |τ * (theta' t * J) + (theta t - theta (t + τ)) * J|
      = |(τ * theta' t - (theta (t + τ) - theta t)) * J| := by ring_nf
    _ = |τ * theta' t - (theta (t + τ) - theta t)| * |J| := abs_mul _ _
    _ ≤ (π ^ 2 / 2 * τ ^ 2) * (2 * B) := by
        refine mul_le_mul ?_ hJ2 (abs_nonneg _) (by positivity)
        rw [abs_sub_comm]
        exact hT
    _ = π ^ 2 * τ ^ 2 * B := by ring

end PeyreData

end HRS.Uniform.Q12
