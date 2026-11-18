import HRS.Equilibrium.Parametrix.PX3aAuxW

/-!
# Packet PX3a auxiliaries X: `𝒩F` is doubly centred
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

lemma conormalL_B_nonneg (hd : 2 ≤ d) {σ : ℝ} {b : ℕ → ℕ} {m : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hF : ConormalL σ b m B F) : 0 ≤ B := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  set z : Euc d := (1 / 16 : ℝ) • EuclideanSpace.single (⟨0, by omega⟩ : Fin d) (1 : ℝ) with hz
  have hzn : ‖z‖ = 1 / 16 := by rw [hz, norm_smul]; simp
  have hz0 : z ≠ 0 := by intro h; rw [h] at hzn; simp at hzn
  have h := hF.near 0 0 (by omega) 0 z hz0 (by unfold r0; rw [hzn]; norm_num)
  have h1 := norm_nonneg (mixedDeriv 0 0 (toChart F) 0 z)
  have h2 : 0 < 1 + ‖z‖ ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log ‖z‖|) ^ b 0 := by
    have : 0 ≤ ‖z‖ ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log ‖z‖|) ^ b 0 :=
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (pow_nonneg (by positivity) _)
    linarith
  by_contra hB
  push_neg at hB
  nlinarith

theorem conormalL_mono_m {σ : ℝ} {b : ℕ → ℕ} {m m' : ℕ} {B : ℝ} {F : Torus d → Torus d → ℝ}
    (hm : m' ≤ m) (hF : ConormalL σ b m B F) : ConormalL σ b m' B F where
  smooth := hF.smooth.of_le (by exact_mod_cast hm)
  near a c hac := hF.near a c (by omega)
  far k hk := hF.far k (by omega)

theorem doublyCentered_cc (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {σ : ℝ}
    (hσ : σ < d) (b : ℕ) {B : ℝ} (hB : 0 ≤ B) {H : Torus d → Torus d → ℝ} (hH : Conormal σ b 0 B H)
    (hdiag : ∀ x, H x x = 0) :
    PDE.DoublyCentered (withDensityReal ρ)
      (fun x y => if x = y then 0 else canonicalCenter (withDensityReal ρ) H x y) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  set μ : Measure (Torus d) := withDensityReal ρ with hμ
  obtain ⟨K, hK0, hK⟩ := conormal_row_int hd hρ hσ b
  have hHt : Conormal σ b 0 B (swapK H) := conormalL_swap hH
  have hdiagt : ∀ x, swapK H x x = 0 := hdiag
  have hint := conormal_prod_int hd hρ hσ b hB hH hdiag
  set r₁ : Torus d → ℝ := fun x => ∫ y, H x y ∂μ with hr₁
  set r₂ : Torus d → ℝ := fun y => ∫ x, H x y ∂μ with hr₂
  have hr1i : Integrable r₁ μ := hint.integral_prod_left
  have hr2i : Integrable r₂ μ := hint.integral_prod_right
  have hfub : ∫ x, r₁ x ∂μ = ∫ y, r₂ y ∂μ := integral_integral_swap hint
  have hne : ∀ a : Torus d, ∀ᵐ z ∂μ, z ≠ a := by
    intro a
    have h : ∀ᵐ z ∂(volume : Measure (Torus d)), z ≠ a := by
      rw [ae_iff]
      simpa using volume_singleton_torus (by omega) a
    exact (withDensity_absolutelyContinuous _ _).ae_le h
  have hcc : ∀ x y, canonicalCenter μ H x y = H x y - r₁ x - r₂ y + ∫ x', r₁ x' ∂μ := fun x y => rfl
  refine ⟨fun y => ?_, fun x => ?_⟩
  · have hcol : Integrable (fun x => H x y) μ := (hK B (swapK H) hB hHt hdiagt y).1
    show ∫ x, (if x = y then 0 else canonicalCenter μ H x y) ∂μ = 0
    have hae : (fun x => if x = y then (0 : ℝ) else canonicalCenter μ H x y) =ᵐ[μ]
        fun x => H x y + ((∫ x', r₁ x' ∂μ - r₂ y) - r₁ x) := by
      filter_upwards [hne y] with x hx
      rw [if_neg hx, hcc]; ring
    have e : ∫ x, ((∫ x', r₁ x' ∂μ - r₂ y) - r₁ x) ∂μ = (∫ x', r₁ x' ∂μ - r₂ y) - ∫ x', r₁ x' ∂μ := by
      rw [integral_sub (integrable_const _) hr1i]; simp
    have hi2 : Integrable (fun x => (∫ x', r₁ x' ∂μ - r₂ y) - r₁ x) μ := (integrable_const _).sub hr1i
    rw [integral_congr_ae hae, integral_add hcol hi2, e]
    have : ∫ x, H x y ∂μ = r₂ y := rfl
    rw [this]; ring
  · have hrow : Integrable (fun y => H x y) μ := (hK B H hB hH hdiag x).1
    show ∫ y, (if x = y then 0 else canonicalCenter μ H x y) ∂μ = 0
    have hae : (fun y => if x = y then (0 : ℝ) else canonicalCenter μ H x y) =ᵐ[μ]
        fun y => H x y + ((∫ x', r₁ x' ∂μ - r₁ x) - r₂ y) := by
      filter_upwards [hne x] with y hy
      rw [if_neg (Ne.symm hy), hcc]; ring
    have e : ∫ y, ((∫ x', r₁ x' ∂μ - r₁ x) - r₂ y) ∂μ = (∫ x', r₁ x' ∂μ - r₁ x) - ∫ y, r₂ y ∂μ := by
      rw [integral_sub (integrable_const _) hr2i]; simp
    have hi2 : Integrable (fun y => (∫ x', r₁ x' ∂μ - r₁ x) - r₂ y) μ := (integrable_const _).sub hr2i
    rw [integral_congr_ae hae, integral_add hrow hi2, e]
    have : ∫ y, H x y ∂μ = r₁ x := rfl
    rw [this, hfub]; ring

end HRS.Parx

end
