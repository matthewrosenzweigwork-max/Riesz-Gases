import Mathlib
import HRS.Main.A33Aux5

/-!
# Packet A33, helper 6: the Gram identity for the noise vectors
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A33

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

open Classical in
/-- The vector `h_{t,φ} ∈ L²(ν; ℝ^d)` (zero if the integrand is not square integrable). -/
def a33_vec (S : A33Setup d) (q t : ℝ) (φ : Torus d → ℝ) : Lp (Euc d) 2 (a33_nu d S.T S.ρ) :=
  if h : MemLp (a33_g S.D S.ρ q t φ) 2 (a33_nu d S.T S.ρ) then h.toLp _ else 0

namespace A33Setup

variable (S : A33Setup d)

theorem vec_ae (q : ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    (a33_vec S q t φ : ℝ × Torus d → Euc d) =ᵐ[a33_nu d S.T S.ρ] a33_g S.D S.ρ q t φ := by
  have h := S.g_memLp q ht hφ
  unfold a33_vec
  rw [dif_pos h]
  exact h.coeFn_toLp

/-- Gram integral over the base measure. -/
theorem inner_vec (q : ℝ) {s t : ℝ} (hs : s ∈ Set.Icc 0 S.T) (ht : t ∈ Set.Icc 0 S.T)
    {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) :
    ⟪a33_vec S q s φ, a33_vec S q t ψ⟫ =
      ∫ p, S.ρ p.1 p.2 * ⟪a33_g S.D S.ρ q s φ p, a33_g S.D S.ρ q t ψ p⟫ ∂(a33_mu0 d S.T) := by
  have hρ := S.rho
  rw [L2.inner_def]
  have h1 : ∫ p, ⟪(a33_vec S q s φ : ℝ × Torus d → Euc d) p, (a33_vec S q t ψ : ℝ × Torus d → Euc d) p⟫
      ∂(a33_nu d S.T S.ρ) =
      ∫ p, ⟪a33_g S.D S.ρ q s φ p, a33_g S.D S.ρ q t ψ p⟫ ∂(a33_nu d S.T S.ρ) := by
    refine integral_congr_ae ?_
    filter_upwards [S.vec_ae q hs hφ, S.vec_ae q ht hψ] with p h1 h2
    rw [h1, h2]
  rw [h1]
  unfold a33_nu
  rw [integral_withDensity_eq_integral_toReal_smul₀ (hρ.aemeasurable.ennreal_ofReal)
    (Eventually.of_forall fun p => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [a33_ae_mu0 (d := d) S.T] with p hp
  rw [ENNReal.toReal_ofReal (hρ.nonneg p.1 hp p.2), smul_eq_mul]

theorem g_meas' (q : ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) : Measurable (a33_g S.D S.ρ q t φ) := by
  rcases ht.1.eq_or_lt with h0 | h0
  · have : a33_g S.D S.ρ q t φ = 0 := by
      funext p
      unfold a33_g
      simp [← h0]
    rw [this]
    exact measurable_const
  · exact S.g_meas q ⟨h0, ht.2⟩ hφ

theorem g_bound' (q : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Set.Icc 0 S.T, ∀ φ : Torus d → ℝ,
    Torus.IsSmooth φ → ∀ p : ℝ × Torus d,
      ‖a33_g S.D S.ρ q t φ p‖ ≤ B * sobolevNorm (mStar d : ℝ) φ := by
  obtain ⟨B, hB0, hB⟩ := S.g_bound q
  refine ⟨B, hB0, fun t ht φ hφ p => ?_⟩
  rcases ht.1.eq_or_lt with h0 | h0
  · have : a33_g S.D S.ρ q t φ p = 0 := by
      unfold a33_g
      simp [← h0]
    rw [this, norm_zero]
    exact mul_nonneg hB0 (Real.sqrt_nonneg _)
  · exact hB t ⟨h0, ht.2⟩ φ hφ p

theorem gram (q : ℝ) (hq : 0 ≤ q) {s t : ℝ} (hs : s ∈ Set.Icc 0 S.T) (ht : t ∈ Set.Icc 0 S.T)
    {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) :
    ⟪a33_vec S q s φ, a33_vec S q t ψ⟫ =
      2 * q * ∫ r in Set.Icc 0 (min s t), ∫ x : Torus d,
        inner ℝ (Torus.grad (propagator S.D S.ρ r s φ) x) (Torus.grad (propagator S.D S.ρ r t ψ) x) *
          S.ρ r x := by
  classical
  have hρ := S.rho
  rw [S.inner_vec q hs ht hφ hψ]
  obtain ⟨Bρ, hBρ⟩ := hρ.bound
  obtain ⟨Bg, hBg0, hBg⟩ := S.g_bound' q
  set F : ℝ × Torus d → ℝ := fun p => S.ρ p.1 p.2 *
    ⟪a33_g S.D S.ρ q s φ p, a33_g S.D S.ρ q t ψ p⟫ with hF
  have hFint : Integrable F (a33_mu0 d S.T) := by
    have hm : AEStronglyMeasurable F (a33_mu0 d S.T) :=
      (hρ.aemeasurable.mul ((S.g_meas' q hs hφ).inner (S.g_meas' q ht hψ)).aemeasurable).aestronglyMeasurable
    refine Integrable.of_bound hm (Bρ * ((Bg * sobolevNorm (mStar d : ℝ) φ) *
      (Bg * sobolevNorm (mStar d : ℝ) ψ))) ?_
    filter_upwards [a33_ae_mu0 (d := d) S.T] with p hp
    simp only [hF, Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (hBρ p.1 hp p.2) ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hBg s hs φ hφ p) (hBg t ht ψ hψ p) (norm_nonneg _)
        (mul_nonneg hBg0 (Real.sqrt_nonneg _)))) (abs_nonneg _) ((abs_nonneg _).trans (hBρ p.1 hp p.2))
  have hfub := integral_prod F hFint
  have hprod : a33_mu0 d S.T = (volume.restrict (Set.Icc 0 S.T)).prod volume := rfl
  rw [hprod, hfub]
  set Φ : ℝ → ℝ := fun r => ∫ x : Torus d,
    inner ℝ (Torus.grad (propagator S.D S.ρ r s φ) x) (Torus.grad (propagator S.D S.ρ r t ψ) x) *
      S.ρ r x with hΦ
  have hinner : ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∫ x : Torus d, F (r, x) =
      (Set.Icc 0 (min s t)).indicator (fun r => 2 * q * Φ r) r *
        (if 0 < s ∧ 0 < t then 1 else 0) := by
    intro r hr
    by_cases hc : 0 < s ∧ 0 < t
    · rw [if_pos hc, mul_one]
      by_cases hr' : r ∈ Set.Icc 0 (min s t)
      · rw [Set.indicator_of_mem hr']
        have hrs : r ∈ Set.Icc 0 s := ⟨hr'.1, hr'.2.trans (min_le_left _ _)⟩
        have hrt : r ∈ Set.Icc 0 t := ⟨hr'.1, hr'.2.trans (min_le_right _ _)⟩
        have : ∀ x : Torus d, F (r, x) = 2 * q * (inner ℝ (Torus.grad (propagator S.D S.ρ r s φ) x)
            (Torus.grad (propagator S.D S.ρ r t ψ) x) * S.ρ r x) := by
          intro x
          simp only [hF, a33_g, hrs, hrt, hc.1, hc.2, and_self, if_true, inner_smul_left,
            inner_smul_right, conj_trivial]
          have h2 : Real.sqrt (2 * q) * Real.sqrt (2 * q) = 2 * q :=
            Real.mul_self_sqrt (by linarith)
          rw [mul_comm (S.ρ r x), ← mul_assoc, ← mul_assoc, h2]
        simp_rw [this]
        rw [integral_const_mul]
      · rw [Set.indicator_of_notMem hr']
        have : ∀ x : Torus d, F (r, x) = 0 := by
          intro x
          have hnot : ¬ ((r ∈ Set.Icc 0 s ∧ 0 < s) ∧ (r ∈ Set.Icc 0 t ∧ 0 < t)) := by
            rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
            exact hr' ⟨h1.1, le_min h1.2 h2.2⟩
          by_cases h1 : r ∈ Set.Icc 0 s ∧ 0 < s
          · have h2 : ¬ (r ∈ Set.Icc 0 t ∧ 0 < t) := fun h2 => hnot ⟨h1, h2⟩
            have hz : a33_g S.D S.ρ q t ψ (r, x) = 0 := by unfold a33_g; exact if_neg h2
            simp only [hF, hz, inner_zero_right, mul_zero]
          · have hz : a33_g S.D S.ρ q s φ (r, x) = 0 := by unfold a33_g; exact if_neg h1
            simp only [hF, hz, inner_zero_left, mul_zero]
        simp_rw [this]
        simp
    · rw [if_neg hc, mul_zero]
      have : ∀ x : Torus d, F (r, x) = 0 := by
        intro x
        have h : ¬ ((0 < s) ∧ (0 < t)) := hc
        by_cases h1 : 0 < s
        · have h2 : ¬ 0 < t := fun h2 => h ⟨h1, h2⟩
          have hz : a33_g S.D S.ρ q t ψ (r, x) = 0 := by
            unfold a33_g; exact if_neg (fun h' => h2 h'.2)
          simp only [hF, hz, inner_zero_right, mul_zero]
        · have hz : a33_g S.D S.ρ q s φ (r, x) = 0 := by
            unfold a33_g; exact if_neg (fun h' => h1 h'.2)
          simp only [hF, hz, inner_zero_left, mul_zero]
      simp_rw [this]
      simp
  have hcongr : ∫ r, ∫ x : Torus d, F (r, x) ∂volume ∂(volume.restrict (Set.Icc 0 S.T)) =
      ∫ r, (Set.Icc 0 (min s t)).indicator (fun r => 2 * q * Φ r) r *
        (if 0 < s ∧ 0 < t then 1 else 0) ∂(volume.restrict (Set.Icc 0 S.T)) := by
    refine integral_congr_ae ?_
    exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hinner)
  rw [hcongr]
  by_cases hc : 0 < s ∧ 0 < t
  · simp only [if_pos hc, mul_one]
    rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      Set.inter_eq_left.2 (Set.Icc_subset_Icc le_rfl ((min_le_left _ _).trans hs.2)),
      integral_const_mul]
  · simp only [if_neg hc, mul_zero, integral_zero]
    have hmin : min s t = 0 := by
      have h : ¬ ((0 < s) ∧ (0 < t)) := hc
      rcases not_and_or.1 h with h | h
      · have : s = 0 := le_antisymm (not_lt.1 h) hs.1
        simp [this, ht.1]
      · have : t = 0 := le_antisymm (not_lt.1 h) ht.1
        simp [this, hs.1]
    rw [hmin, Set.Icc_self, setIntegral_measure_zero _ (by simp), mul_zero]

end A33Setup

end HRS.A33
