import HRS.MC.L2C3Aux5

/-!
# Packet L2C-3, helper 6: the differential inequality of the Lyapunov functional along the path

For a classical adjoint solution `F` on `[0,t]` (all `F r` smooth) and a frozen-type path `S`, put
`y(τ) = P_β[F(t-τ)] - [S(τ)] ∈ L²(μ_β)`, `Fv(τ) = ⟨y(τ), A_β⁻¹ y(τ)⟩`.  `l2c3_lyap` shows: `Fv` is continuous on
`[0,t]`, differentiable on `(0,t)` with derivative `≤ -2ν E_v + 2 C_m e^{-κ(t-τ)} ‖∇F(t-τ)‖ ‖y(τ)‖`
(`E_v = ∫ρ_β|∇v|²`, `v = P_β F(t-τ) - S(τ)`), and `c_P ‖y‖² ≤ E_v`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear

namespace HRS.MC.L2C3

variable {d : ℕ}

/-- The dissipation `∫ρ_β |∇v|²` of `v = P_β F(t-τ) - S(τ)`. -/
def l2c3_Ev (R : Regime d) (t : ℝ) (F S : ℝ → Torus d → ℝ) (τ : ℝ) : ℝ :=
  ∫ x, R.ρβ x * ‖Torus.grad (fun x => projMean (withDensityReal R.ρβ) (F (t - τ)) x - S τ x) x‖ ^ 2

/-- The squared gradient norm `∫|∇F(t-τ)|² dx`. -/
def l2c3_Nn (R : Regime d) (t : ℝ) (F : ℝ → Torus d → ℝ) (τ : ℝ) : ℝ :=
  ∫ x, ‖Torus.grad (F (t - τ)) x‖ ^ 2

/-- The Lyapunov functional along the path. -/
def l2c3_Fv {R : Regime d} (Cx : Ctx R) (t : ℝ) (F S : ℝ → Torus d → ℝ) (τ : ℝ) : ℝ :=
  inner ℝ (l2c3_y R t F S τ) (Cx.Rop (l2c3_y R t F S τ))

theorem l2c3_pair_v {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {f g : Torus d → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hg0 : pair μ g = 0) :
    pair μ (fun x => projMean μ f x - g x) = 0 := by
  have hc1 : Continuous (projMean μ f) := hf.sub continuous_const
  unfold pair at hg0 ⊢
  rw [integral_sub (l2c3_integrable hc1) (l2c3_integrable hg), hg0]
  have := MFSemigroup.pair_projMean μ f
  unfold pair at this
  rw [this]; ring

theorem l2c3_pert_cont' (R : Regime d) {s : ℝ} (hs : 0 ≤ s) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) :
    Continuous (fun x => backwardGenerator R.D (R.ρ s) f x - backwardGenerator R.D R.ρβ f x) := by
  obtain ⟨Λ, hΛ⟩ := HRS.MC.RegSet.reg_proof R 1
  have hf2 : Torus.IsCk 2 f := l2c3_isCk_of_smooth hf 2
  exact (l2c3_bg_cont R (hΛ s s ⟨hs, le_rfl⟩).1 hf2).sub
    (l2c3_bg_cont R (l2c3_isCk_of_smooth R.thermal.2.1 1) hf2)

/-- The conclusion of the Lyapunov differential inequality, for constants `Cm, κ`. -/
def L2C3Lyap (R : Regime d) (Cx : Ctx R) (Cm κ : ℝ) : Prop :=
  ∀ {t : ℝ}, 0 < t → ∀ {φ : Torus d → ℝ} {F : ℝ → Torus d → ℝ},
      IsClassicalAdjointSolution R.D R.ρ t φ F → (∀ r ∈ Set.Icc (0 : ℝ) t, Torus.IsSmooth (F r)) →
      ∀ {S : ℝ → Torus d → ℝ}, (∀ τ ∈ Set.Icc (0 : ℝ) t, Torus.IsCk 2 (S τ)) →
      (∀ τ ∈ Set.Icc (0 : ℝ) t, pair (withDensityReal R.ρβ) (S τ) = 0) →
      (Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => S p.1 p.2) →
      (Continuous fun p : Set.Icc (0 : ℝ) t × Torus d =>
        equilibriumGen d R.D.s R.ρβ R.β⁻¹ (S p.1) p.2) →
      (∀ x : Torus d, ∀ τ ∈ Set.Ioo (0 : ℝ) t,
        HasDerivAt (fun τ' => S τ' x) (equilibriumGen d R.D.s R.ρβ R.β⁻¹ (S τ) x) τ) →
      ContinuousOn (l2c3_Fv Cx t F S) (Set.Icc 0 t) ∧
      (∀ τ ∈ Set.Ioo (0 : ℝ) t, ∃ f' : ℝ, HasDerivAt (l2c3_Fv Cx t F S) f' τ ∧
        f' ≤ -2 * R.β⁻¹ * l2c3_Ev R t F S τ +
          2 * Cm * Real.exp (-κ * (t - τ)) * Real.sqrt (l2c3_Nn R t F τ) * ‖l2c3_y R t F S τ‖) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) t, ‖l2c3_y R t F S τ‖ ^ 2 =
          l2Inner (withDensityReal R.ρβ) (fun x => projMean (withDensityReal R.ρβ) (F (t - τ)) x - S τ x)
            (fun x => projMean (withDensityReal R.ρβ) (F (t - τ)) x - S τ x) ∧
        Cx.cP * ‖l2c3_y R t F S τ‖ ^ 2 ≤ l2c3_Ev R t F S τ)

theorem l2c3_lyap (R : Regime d) (Cx : Ctx R) :
    ∃ Cm κ : ℝ, 0 ≤ Cm ∧ 0 < κ ∧ L2C3Lyap R Cx Cm κ := by
  obtain ⟨Cp, κ, hCp, hκ, Hp⟩ := l2c3_pert_Lp R
  refine ⟨Cp * Real.sqrt Cx.Λ₀ * ‖Cx.Rop‖, κ, by positivity, hκ, ?_⟩
  intro t ht φ F hF hFs S hS2 hS0 hSc hSg hSd
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) t, t - τ ∈ Set.Icc (0 : ℝ) t := fun τ hτ =>
    ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  obtain ⟨hyc, hyd⟩ := l2c3_path_deriv R hF hS2 hSc hSg hSd
  have hcF : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (F (t - τ)) := fun τ hτ =>
    ClassicalAux.continuous_f_apply hF (hmem τ hτ)
  have hcS : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (S τ) := fun τ hτ =>
    MFAux.continuous_of_isCk ((hS2 τ hτ).of_le (by norm_num))
  have hcG : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      Continuous (backwardGenerator R.D (R.ρ (t - τ)) (F (t - τ))) := fun τ hτ =>
    ClassicalAux.continuous_bg_apply hF (hmem τ hτ)
  have hcE : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (equilibriumGen d R.D.s R.ρβ R.β⁻¹ (S τ)) :=
    fun τ hτ => l2c3_eqGen_cont R (hS2 τ hτ)
  -- the a.e. descriptions
  have hyae : ∀ τ ∈ Set.Icc (0 : ℝ) t, ⇑(l2c3_y R t F S τ) =ᵐ[withDensityReal R.ρβ]
      fun x => projMean (withDensityReal R.ρβ) (F (t - τ)) x - S τ x := by
    intro τ hτ
    have h1 : ⇑(pL (withDensityReal R.ρβ) (fun τ' => F (t - τ')) τ) =ᵐ[withDensityReal R.ρβ] F (t - τ) :=
      pL_ae (G := fun τ' => F (t - τ')) (hcF τ hτ)
    have h2 : ⇑(pL (withDensityReal R.ρβ) S τ) =ᵐ[withDensityReal R.ρβ] S τ := pL_ae (hcS τ hτ)
    have h3 := l2c3_P_ae _ h1
    unfold l2c3_y
    filter_upwards [Lp.coeFn_sub (l2c3_P (withDensityReal R.ρβ)
      (pL (withDensityReal R.ρβ) (fun τ' => F (t - τ')) τ)) (pL (withDensityReal R.ρβ) S τ), h3, h2]
      with x e1 e2 e3
    rw [e1]
    simp only [Pi.sub_apply]
    rw [e2, e3]
  have hy'ae : ∀ τ ∈ Set.Icc (0 : ℝ) t, ⇑(l2c3_y' R t F S τ) =ᵐ[withDensityReal R.ρβ]
      fun x => projMean (withDensityReal R.ρβ) (backwardGenerator R.D (R.ρ (t - τ)) (F (t - τ))) x -
        equilibriumGen d R.D.s R.ρβ R.β⁻¹ (S τ) x := by
    intro τ hτ
    have h1 : ⇑(pL (withDensityReal R.ρβ)
        (fun τ' x => backwardGenerator R.D (R.ρ (t - τ')) (F (t - τ')) x) τ) =ᵐ[withDensityReal R.ρβ]
        backwardGenerator R.D (R.ρ (t - τ)) (F (t - τ)) :=
      pL_ae (G := fun τ' x => backwardGenerator R.D (R.ρ (t - τ')) (F (t - τ')) x) (hcG τ hτ)
    have h2 : ⇑(pL (withDensityReal R.ρβ) (fun τ' => equilibriumGen d R.D.s R.ρβ R.β⁻¹ (S τ')) τ)
        =ᵐ[withDensityReal R.ρβ] equilibriumGen d R.D.s R.ρβ R.β⁻¹ (S τ) :=
      pL_ae (G := fun τ' => equilibriumGen d R.D.s R.ρβ R.β⁻¹ (S τ')) (hcE τ hτ)
    have h3 := l2c3_P_ae _ h1
    unfold l2c3_y'
    filter_upwards [Lp.coeFn_sub (l2c3_P (withDensityReal R.ρβ)
      (pL (withDensityReal R.ρβ)
        (fun τ' x => backwardGenerator R.D (R.ρ (t - τ')) (F (t - τ')) x) τ))
      (pL (withDensityReal R.ρβ) (fun τ' => equilibriumGen d R.D.s R.ρβ R.β⁻¹ (S τ')) τ), h3, h2]
      with x e1 e2 e3
    rw [e1]
    simp only [Pi.sub_apply]
    rw [e2, e3]
  -- fixed-time facts
  have hvc : ∀ τ ∈ Set.Icc (0 : ℝ) t, Torus.IsCk 1
      (fun x => projMean (withDensityReal R.ρβ) (F (t - τ)) x - S τ x) := fun τ hτ =>
    (isCk_sub_const (l2c3_isCk_of_smooth (hFs _ (hmem τ hτ)) 1) _).sub ((hS2 τ hτ).of_le (by norm_num))
  have hv0 : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      pair (withDensityReal R.ρβ) (fun x => projMean (withDensityReal R.ρβ) (F (t - τ)) x - S τ x) = 0 :=
    fun τ hτ => l2c3_pair_v (hcF τ hτ) (hcS τ hτ) (hS0 τ hτ)
  refine ⟨?_, ?_, ?_⟩
  · -- continuity of `Fv`
    unfold l2c3_Fv
    exact hyc.inner (Cx.Rop.continuous.comp_continuousOn hyc)
  · intro τ hτ
    have hτ' : τ ∈ Set.Icc (0 : ℝ) t := Set.Ioo_subset_Icc_self hτ
    have hd := hyd τ hτ
    have hd2 := (Cx.Rop.hasFDerivAt.comp_hasDerivAt τ hd)
    have hd3 := hd.inner ℝ hd2
    refine ⟨_, hd3, ?_⟩
    have hs : 0 ≤ t - τ := by linarith [hτ.2]
    have hf := hFs _ (hmem τ hτ')
    have hpc := l2c3_pert_cont' R hs hf
    set e : Lp ℝ 2 (withDensityReal R.ρβ) :=
      (hpc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).toLp _ with he_def
    have he : ⇑e =ᵐ[withDensityReal R.ρβ] fun x =>
        backwardGenerator R.D (R.ρ (t - τ)) (F (t - τ)) x - backwardGenerator R.D R.ρβ (F (t - τ)) x :=
      MemLp.coeFn_toLp _
    have hM := Hp Cx.Λ₀ Cx.hup (t - τ) hs (F (t - τ)) hf e he
    have hft := l2c3_ft Cx hs hf (hS2 τ hτ') (hS0 τ hτ') (l2c3_y R t F S τ) (l2c3_y' R t F S τ) e
      (M := Cp * Real.exp (-κ * (t - τ)) * Real.sqrt (∫ x, ‖Torus.grad (F (t - τ)) x‖ ^ 2) *
        Real.sqrt Cx.Λ₀) (by have := Real.sqrt_nonneg Cx.Λ₀; positivity) (hyae τ hτ') (hy'ae τ hτ') he hM
    have h1 : inner ℝ (l2c3_y R t F S τ) (Cx.Rop (l2c3_y' R t F S τ)) =
        inner ℝ (Cx.Rop (l2c3_y R t F S τ)) (l2c3_y' R t F S τ) :=
      (Cx.hRs (l2c3_y R t F S τ) (l2c3_y' R t F S τ)).symm
    have h2 : inner ℝ (l2c3_y' R t F S τ) (Cx.Rop (l2c3_y R t F S τ)) =
        inner ℝ (Cx.Rop (l2c3_y R t F S τ)) (l2c3_y' R t F S τ) := real_inner_comm _ _
    simp only [Function.comp_apply]
    rw [h1, h2]
    unfold l2c3_Ev l2c3_Nn
    nlinarith [hft]
  · intro τ hτ
    have hy2 : ‖l2c3_y R t F S τ‖ ^ 2 =
        l2Inner (withDensityReal R.ρβ) (fun x => projMean (withDensityReal R.ρβ) (F (t - τ)) x - S τ x)
          (fun x => projMean (withDensityReal R.ρβ) (F (t - τ)) x - S τ x) := by
      rw [sq, ← real_inner_self_eq_norm_mul_norm, innerLp_eq_l2Inner]
      exact l2Inner_congr_ae (hyae τ hτ) (hyae τ hτ)
    refine ⟨hy2, ?_⟩
    rw [hy2]
    exact Cx.hPo _ (hvc τ hτ) (hv0 τ hτ)

end HRS.MC.L2C3
