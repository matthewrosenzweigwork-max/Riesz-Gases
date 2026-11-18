import HRS.MC.L2C3Aux10

/-!
# Packet L2C-3, helper 11: stage 2 (integrated gradient energy) and the degenerate case `t = 0`
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear

namespace HRS.MC.L2C3

variable {d : ℕ}

theorem l2c3_Nn_cont {D : DynData d} {μ : ℝ → Torus d → ℝ} {t : ℝ} {φ : Torus d → ℝ}
    {F : ℝ → Torus d → ℝ} (hF : IsClassicalAdjointSolution D μ t φ F) :
    ContinuousOn (fun σ => ∫ x, ‖Torus.grad (F (t - σ)) x‖ ^ 2) (Set.Icc 0 t) := by
  have h := l2c3_energy_cont hF (w := fun _ => (1 : ℝ)) continuous_const
  have hc : ContinuousOn (fun σ : ℝ => t - σ) (Set.Icc 0 t) :=
    (continuous_const.sub continuous_id).continuousOn
  have := ContinuousOn.comp (g := fun r => ∫ x, (fun _ => (1 : ℝ)) x * ‖Torus.grad (F r) x‖ ^ 2) h hc
    (fun σ hσ => (⟨by linarith [hσ.2], by linarith [hσ.1]⟩ : t - σ ∈ Set.Icc (0 : ℝ) t))
  refine this.congr fun σ _ => ?_
  simp only [Function.comp_apply, one_mul]

/-- Stage 2: the unweighted integrated gradient energy, from the weighted one. -/
theorem l2c3_stage2 (R : Regime d) (Cx : Ctx R) {t : ℝ} {φ : Torus d → ℝ} {F : ℝ → Torus d → ℝ}
    (hF : IsClassicalAdjointSolution R.D R.ρ t φ F)
    (hFs : ∀ r ∈ Set.Icc (0 : ℝ) t, Torus.IsSmooth (F r)) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) t)
    {B : ℝ} (hW : R.β⁻¹ * ∫ σ in (0 : ℝ)..τ,
      Real.exp (l2c3_rate R Cx / 2 * σ) * l2c3_E1 R t F σ ≤ B) :
    ∫ σ in (0 : ℝ)..τ, l2c3_Nn R t F σ ≤ Cx.c₀⁻¹ * (B / R.β⁻¹) := by
  have hν : 0 < R.β⁻¹ := inv_pos.2 R.hβ
  have ha := l2c3_rate_pos R Cx
  have hτt : τ ≤ t := hτ.2
  have hNc := (l2c3_Nn_cont hF).mono (Set.Icc_subset_Icc le_rfl hτt)
  have hEc : ContinuousOn (fun σ => Real.exp (l2c3_rate R Cx / 2 * σ) * l2c3_E1 R t F σ)
      (Set.Icc 0 τ) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (l2c3_E1_cont R Cx hF)).mono (Set.Icc_subset_Icc le_rfl hτt)
  have hle : ∫ σ in (0 : ℝ)..τ, l2c3_Nn R t F σ ≤
      ∫ σ in (0 : ℝ)..τ, Cx.c₀⁻¹ * (Real.exp (l2c3_rate R Cx / 2 * σ) * l2c3_E1 R t F σ) := by
    refine intervalIntegral.integral_mono_on hτ.1
      (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]; exact hNc.integrableOn_Icc)
      (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
          exact (continuousOn_const.mul hEc).integrableOn_Icc) fun σ hσ => ?_
    have hσt : σ ∈ Set.Icc (0 : ℝ) t := ⟨hσ.1, hσ.2.trans hτt⟩
    have hF1 : Torus.IsCk 1 (F (t - σ)) :=
      l2c3_isCk_of_smooth (hFs _ ⟨by linarith [hσt.2], by linarith [hσt.1]⟩) 1
    have hN := l2c3_Nn_le R Cx hF1
    have hE := l2c3_E1_nonneg R Cx t F σ
    have h1 : 1 ≤ Real.exp (l2c3_rate R Cx / 2 * σ) :=
      Real.one_le_exp (by have := hσ.1; positivity)
    have hN' : l2c3_Nn R t F σ ≤ Cx.c₀⁻¹ * l2c3_E1 R t F σ := by
      rw [← div_eq_inv_mul, le_div_iff₀ Cx.hc₀]; linarith
    calc l2c3_Nn R t F σ ≤ Cx.c₀⁻¹ * l2c3_E1 R t F σ := hN'
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) (inv_nonneg.2 Cx.hc₀.le)
  rw [intervalIntegral.integral_const_mul] at hle
  refine hle.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 Cx.hc₀.le))
  rw [le_div_iff₀ hν]; linarith

theorem l2c3_prop_zero (D : DynData d) (ρ : ℝ → Torus d → ℝ) (φ : Torus d → ℝ) :
    propagator D ρ 0 0 φ = φ ∨ propagator D ρ 0 0 φ = 0 := by
  unfold propagator
  split_ifs with h
  · exact Or.inl (h.choose_spec.terminal)
  · exact Or.inr rfl

/-- The degenerate case `t = r = 0`. -/
theorem l2c3_zero_case (R : Regime d) (Cx : Ctx R) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    PDE.l2NormSq (projMean (withDensityReal R.ρβ) (propagator R.D R.ρ 0 0 φ)) ≤
        PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) ∧
      PDE.l2NormSq (fun x => projMean (withDensityReal R.ρβ) (propagator R.D R.ρ 0 0 φ) x -
          PDE.equilibriumSemigroup R.D R.ρβ 0 (projMean (withDensityReal R.ρβ) φ) x) ≤
        PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) := by
  have hd1 := Cx.hd1
  have hψs : Torus.IsSmooth (projMean (withDensityReal R.ρβ) φ) :=
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from hφ).sub contDiff_const
  have hψc : Continuous (projMean (withDensityReal R.ρβ) φ) :=
    Torus.continuous_of_continuous_lift (PDE.MFPair.isCk_of_smooth_ps hψs 0).continuous
  have hψm : MemSobolev ((PDE.mStar d : ℝ) + 4) (projMean (withDensityReal R.ρβ) φ) :=
    PDE.MFSemigroup.memSobolev_of_isSmooth hψs _
  have hD := (HRS.MC.L2C1.l2c1_dyn_eq R).symm
  have hSz := frozen_zero hd1 Cx.H hψc hψm
  unfold Sg at hSz
  rw [hD] at hSz
  have hp := MFSemigroup.pair_projMean (withDensityReal R.ρβ) φ
  have hpp : ∀ x, projMean (withDensityReal R.ρβ) (projMean (withDensityReal R.ρβ) φ) x =
      projMean (withDensityReal R.ρβ) φ x := by
    intro x
    have : pair (withDensityReal R.ρβ) (projMean (withDensityReal R.ρβ) φ) = 0 := hp
    simp only [projMean] at this ⊢
    rw [this, sub_zero]
  have hQ : ∀ x, equilibriumSemigroup R.D R.ρβ 0 (projMean (withDensityReal R.ρβ) φ) x =
      projMean (withDensityReal R.ρβ) φ x := by
    intro x; rw [hSz, hpp]
  have hQ0 : 0 ≤ PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) :=
    integral_nonneg fun x => sq_nonneg _
  have hz0 : ∀ x, projMean (withDensityReal R.ρβ) (0 : Torus d → ℝ) x = 0 := by
    intro x; simp [projMean, pair]
  rcases l2c3_prop_zero R.D R.ρ φ with h | h
  · rw [h]
    refine ⟨le_rfl, ?_⟩
    have : (fun x => projMean (withDensityReal R.ρβ) φ x -
        equilibriumSemigroup R.D R.ρβ 0 (projMean (withDensityReal R.ρβ) φ) x) = fun _ => 0 := by
      funext x; rw [hQ]; ring
    rw [this]
    simpa [PDE.l2NormSq] using hQ0
  · rw [h]
    have e1 : projMean (withDensityReal R.ρβ) (0 : Torus d → ℝ) = fun _ => 0 := funext hz0
    rw [e1]
    refine ⟨?_, ?_⟩
    · simpa [PDE.l2NormSq] using hQ0
    · have : (fun x => (fun _ : Torus d => (0 : ℝ)) x -
          equilibriumSemigroup R.D R.ρβ 0 (projMean (withDensityReal R.ρβ) φ) x) =
          fun x => -projMean (withDensityReal R.ρβ) φ x := by
        funext x; rw [hQ]; ring
      rw [this]
      unfold PDE.l2NormSq
      simp

end HRS.MC.L2C3
