import HRS.Equilibrium.Parametrix.PXFIDAuxL

/-!
# Packet PX-FID, file M: the slice integrations by parts for a `PsiSize` kernel and the pointwise
equation with the projection means removed
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

/-- Integration by parts in the first variable. -/
theorem slice_ibp_fst (H : FidHyp d s V β ρ) {K₁ : ℝ} (hK : 0 ≤ K₁) {ψ : Torus d → Torus d → ℝ}
    (hψ : PsiSize s K₁ ψ) (y : Torus d) {ϕ : Torus d → ℝ} (hϕ : Torus.IsSmooth ϕ) :
    Integrable (Bop d s V β ρ (fun z => ψ z y)) (withDensityReal ρ) ∧
    Integrable (fun x => inner ℝ (gradFst ψ x y) (Torus.grad ϕ x)) (withDensityReal ρ) ∧
    ∫ x, Bop d s V β ρ (fun z => ψ z y) x * ϕ x ∂(withDensityReal ρ) =
      -β⁻¹ * ∫ x, inner ℝ (gradFst ψ x y) (Torus.grad ϕ x) ∂(withDensityReal ρ) := by
  obtain ⟨M, hM⟩ := exists_force_bound H.two_le H.s_nonneg H.s_lt H.beta_pos H.V_smooth H.thermal
    H.rho_smooth
  obtain ⟨h1, -, h3, h4⟩ := ibp_singular H.two_le H.crit H.beta_pos H.rho_smooth
    (force_relation H.two_le H.s_nonneg H.s_lt H.beta_pos H.V_smooth H.thermal H.rho_smooth) hM hK
    (Torus.rep y) (singSlice_fst hψ y) hϕ
  exact ⟨h1, h3, h4⟩

/-- Integration by parts in the second variable. -/
theorem slice_ibp_snd (H : FidHyp d s V β ρ) {K₁ : ℝ} (hK : 0 ≤ K₁) {ψ : Torus d → Torus d → ℝ}
    (hψ : PsiSize s K₁ ψ) (x : Torus d) {ϕ : Torus d → ℝ} (hϕ : Torus.IsSmooth ϕ) :
    Integrable (Bop d s V β ρ (fun z => ψ x z)) (withDensityReal ρ) ∧
    Integrable (fun y => inner ℝ (gradSnd ψ x y) (Torus.grad ϕ y)) (withDensityReal ρ) ∧
    ∫ y, Bop d s V β ρ (fun z => ψ x z) y * ϕ y ∂(withDensityReal ρ) =
      -β⁻¹ * ∫ y, inner ℝ (gradSnd ψ x y) (Torus.grad ϕ y) ∂(withDensityReal ρ) := by
  obtain ⟨M, hM⟩ := exists_force_bound H.two_le H.s_nonneg H.s_lt H.beta_pos H.V_smooth H.thermal
    H.rho_smooth
  obtain ⟨h1, -, h3, h4⟩ := ibp_singular H.two_le H.crit H.beta_pos H.rho_smooth
    (force_relation H.two_le H.s_nonneg H.s_lt H.beta_pos H.V_smooth H.thermal H.rho_smooth) hM hK
    (Torus.rep x) (singSlice_snd hψ x) hϕ
  exact ⟨h1, h3, h4⟩

theorem integral_Bop_fst (H : FidHyp d s V β ρ) {K₁ : ℝ} (hK : 0 ≤ K₁)
    {ψ : Torus d → Torus d → ℝ} (hψ : PsiSize s K₁ ψ) (y : Torus d) :
    ∫ x, Bop d s V β ρ (fun z => ψ z y) x ∂(withDensityReal ρ) = 0 := by
  have h := (slice_ibp_fst H hK hψ y (ϕ := fun _ => 1)
    (show ContDiff ℝ ∞ (Torus.lift (fun _ : Torus d => (1 : ℝ))) from contDiff_const)).2.2
  simp only [mul_one, grad_const_one, inner_zero_right, integral_zero, mul_zero] at h
  exact h

theorem integral_Bop_snd (H : FidHyp d s V β ρ) {K₁ : ℝ} (hK : 0 ≤ K₁)
    {ψ : Torus d → Torus d → ℝ} (hψ : PsiSize s K₁ ψ) (x : Torus d) :
    ∫ y, Bop d s V β ρ (fun z => ψ x z) y ∂(withDensityReal ρ) = 0 := by
  have h := (slice_ibp_snd H hK hψ x (ϕ := fun _ => 1)
    (show ContDiff ℝ ∞ (Torus.lift (fun _ : Torus d => (1 : ℝ))) from contDiff_const)).2.2
  simp only [mul_one, grad_const_one, inner_zero_right, integral_zero, mul_zero] at h
  exact h

/-- The pointwise equation with the projection means removed:
`-(B_x ψ + B_y ψ + 𝒥ψ) = H_f` off the diagonal. -/
theorem eq_off_diag (H : FidHyp d s V β ρ) {f : Torus d → ℝ} {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ}
    (hψ : IsPairCorrector d s V β ρ f K₁ ψ) (hK : 0 ≤ K₁) (x y : Torus d) (hxy : x ≠ y) :
    Hsource d s ρ f x y = -(Bop d s V β ρ (fun z => ψ z y) x + Bop d s V β ρ (fun z => ψ x z) y +
      Jpair d s ρ ψ x y) := by
  have hP := hψ.poisson x y hxy
  have h1 := integral_Bop_fst H hK hψ.size y
  have h2 := integral_Bop_snd H hK hψ.size x
  have i1 := (slice_ibp_fst H hK hψ.size y (ϕ := fun _ => 1)
    (show ContDiff ℝ ∞ (Torus.lift (fun _ : Torus d => (1 : ℝ))) from contDiff_const)).1
  have i2 := (slice_ibp_snd H hK hψ.size x (ϕ := fun _ => 1)
    (show ContDiff ℝ ∞ (Torus.lift (fun _ : Torus d => (1 : ℝ))) from contDiff_const)).1
  have e1 : ∫ z, (Bop d s V β ρ (fun z => ψ z y) z + Jop d s ρ (fun w => ψ w y) z)
      ∂(withDensityReal ρ) = ∫ z, Jop d s ρ (fun w => ψ w y) z ∂(withDensityReal ρ) :=
    integral_add_of_integral_zero i1 h1
  have e2 : ∫ z, (Bop d s V β ρ (fun z => ψ x z) z + Jop d s ρ (fun w => ψ x w) z)
      ∂(withDensityReal ρ) = ∫ z, Jop d s ρ (fun w => ψ x w) z ∂(withDensityReal ρ) :=
    integral_add_of_integral_zero i2 h2
  unfold genFst genSnd projGen projMean pair at hP
  simp only at hP
  unfold Jpair projMean pair
  rw [e1, e2] at hP
  linarith

end HRS.Parx.PXFID

end
