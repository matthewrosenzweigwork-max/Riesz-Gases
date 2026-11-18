import HRS.MC.L2C5Aux2

/-!
# Packet L2C-5, helper 3: the integrated dissipation of the difference `Q_β(U - Ū)`

The `A_β⁻¹`-Lyapunov functional of L2C-3 for `y(τ) = P_β F(t-τ) - S(τ)` with `S(τ) = S_β(τ) φ`
(the frozen semigroup applied to `φ` itself, so `∇S(τ) = ∇Ū^{t-τ,t}φ`) has `y(0) = 0`; the differential
inequality of `L2C3Lyap` closed with the weighted Poincaré inequality gives
`F' + ν E_v ≤ C e^{-2κ(t-τ)} N`, and integration gives
`ν ∫_0^t ∫ρ_β |∇(F - F̄)|² ≤ C ∫_0^t e^{-2κ(t-σ)} ∫|∇F(t-σ)|² dσ`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear HRS.MC.L2C3

namespace HRS.MC.L2C5

variable {d : ℕ}

theorem l2c5_dissipation (R : Regime d) (Cx : Ctx R) {Cm κ : ℝ} (hCm : 0 ≤ Cm) (hκ : 0 < κ)
    (hL : L2C3Lyap R Cx Cm κ) :
    ∃ C5 : ℝ, 0 ≤ C5 ∧ ∀ {t : ℝ}, 0 < t → ∀ {φ : Torus d → ℝ}, Torus.IsSmooth φ →
      ∀ {F Fb : ℝ → Torus d → ℝ}, IsClassicalAdjointSolution R.D R.ρ t φ F →
      (∀ r ∈ Set.Icc (0 : ℝ) t, Torus.IsSmooth (F r)) →
      IsClassicalAdjointSolution R.D (fun _ => R.ρβ) t φ Fb →
      (∀ τ ∈ Set.Ioc (0 : ℝ) t,
        Torus.grad (equilibriumSemigroup R.D R.ρβ τ φ) = Torus.grad (Fb (t - τ))) →
      R.β⁻¹ * ∫ σ in (0 : ℝ)..t, ∫ x, R.ρβ x *
          ‖Torus.grad (F (t - σ)) x - Torus.grad (Fb (t - σ)) x‖ ^ 2 ≤
        C5 * ∫ σ in (0 : ℝ)..t, Real.exp (-2 * κ * (t - σ)) * l2c3_Nn R t F σ := by
  have hν : 0 < R.β⁻¹ := inv_pos.2 R.hβ
  have hcP := Cx.hcP
  refine ⟨Cm ^ 2 / (R.β⁻¹ * Cx.cP), by positivity, ?_⟩
  intro t ht φ hφ F Fb hF hFs hFb hSFb
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) t, t - τ ∈ Set.Icc (0 : ℝ) t := fun τ hτ =>
    ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hd1 := Cx.hd1
  have hφc : Continuous φ :=
    Torus.continuous_of_continuous_lift (PDE.MFPair.isCk_of_smooth_ps hφ 0).continuous
  have hφm : MemSobolev ((PDE.mStar d : ℝ) + 4) φ := PDE.MFSemigroup.memSobolev_of_isSmooth hφ _
  have hD := (HRS.MC.L2C1.l2c1_dyn_eq R).symm
  have hpath := frozen_path_data hd1 Cx.H hφc hφm ht
  rw [hD] at hpath
  obtain ⟨hS2, hS0, hSc, hSg, hSd⟩ := hpath
  have hSz := frozen_zero hd1 Cx.H hφc hφm
  unfold Sg at hSz
  rw [hD] at hSz
  obtain ⟨hA, hB, hC⟩ := hL ht hF hFs
    (S := fun τ => equilibriumSemigroup R.D R.ρβ τ φ) hS2 hS0 hSc hSg hSd
  have hFnn : ∀ τ ∈ Set.Icc (0 : ℝ) t, 0 ≤ l2c3_Fv Cx t F
      (fun τ => equilibriumSemigroup R.D R.ρβ τ φ) τ := by
    intro τ _
    have h1 := (Cx.hform (l2c3_y R t F (fun τ => equilibriumSemigroup R.D R.ρβ τ φ) τ)).1
    have h0 := sq_nonneg ‖l2c3_y R t F (fun τ => equilibriumSemigroup R.D R.ρβ τ φ) τ‖
    by_contra h
    push Not at h
    unfold l2c3_Fv at h
    nlinarith [mul_neg_of_pos_of_neg Cx.hκ₁ h]
  have hF0 : l2c3_Fv Cx t F (fun τ => equilibriumSemigroup R.D R.ρβ τ φ) 0 ≤ 0 := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht.le⟩
    have h1 : l2c3_Fv Cx t F (fun τ => equilibriumSemigroup R.D R.ρβ τ φ) 0 ≤
        Cx.κ₂ * ‖l2c3_y R t F (fun τ => equilibriumSemigroup R.D R.ρβ τ φ) 0‖ ^ 2 :=
      (Cx.hform _).2
    have h2 := (hC 0 h0).1
    have hz : (fun x => projMean (withDensityReal R.ρβ) (F (t - 0)) x -
        equilibriumSemigroup R.D R.ρβ 0 φ x) = fun _ => 0 := by
      funext x
      rw [sub_zero, hF.terminal, hSz]
      ring
    rw [hz] at h2
    have h3 : l2Inner (withDensityReal R.ρβ) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) = 0 := by
      simp [l2Inner]
    rw [h3] at h2
    rw [h2] at h1
    simpa using h1
  choose! f hf using hB
  -- the integrand `w`
  set C5 : ℝ := Cm ^ 2 / (R.β⁻¹ * Cx.cP) with hC5
  have hEv : ∀ σ ∈ Set.Icc (0 : ℝ) t, l2c3_Ev R t F
      (fun τ => equilibriumSemigroup R.D R.ρβ τ φ) σ =
      ∫ x, R.ρβ x * ‖Torus.grad (F (t - σ)) x - Torus.grad (Fb (t - σ)) x‖ ^ 2 := by
    intro σ hσ
    unfold l2c3_Ev
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hf1 : Torus.IsCk 1 (projMean (withDensityReal R.ρβ) (F (t - σ))) :=
      isCk_sub_const (l2c3_isCk_of_smooth (hFs _ (hmem σ hσ)) 1) _
    have hg1 : Torus.IsCk 1 (equilibriumSemigroup R.D R.ρβ σ φ) := (hS2 σ hσ).of_le (by norm_num)
    have hsub := grad_sub hf1 hg1 x
    have hgr : Torus.grad (equilibriumSemigroup R.D R.ρβ σ φ) x = Torus.grad (Fb (t - σ)) x := by
      rcases hσ.1.eq_or_lt with h0 | hpos
      · subst h0
        rw [sub_zero, hFb.terminal, hSz, MFSemigroup.grad_projMean]
      · exact congrFun (hSFb σ ⟨hpos, hσ.2⟩) x
    show R.ρβ x * ‖Torus.grad (fun y => projMean (withDensityReal R.ρβ) (F (t - σ)) y -
      equilibriumSemigroup R.D R.ρβ σ φ y) x‖ ^ 2 = _
    rw [hsub, MFSemigroup.grad_projMean, hgr]
  have hEdc : ContinuousOn (fun r => ∫ x, R.ρβ x * ‖Torus.grad (F r) x - Torus.grad (Fb r) x‖ ^ 2)
      (Set.Icc 0 t) := l2c5_diff_cont hF hFb Cx.hρc
  have hcomp : ContinuousOn (fun σ => ∫ x, R.ρβ x *
      ‖Torus.grad (F (t - σ)) x - Torus.grad (Fb (t - σ)) x‖ ^ 2) (Set.Icc 0 t) :=
    hEdc.comp (continuous_const.sub continuous_id).continuousOn (fun σ hσ => hmem σ hσ)
  have hEvc : ContinuousOn (l2c3_Ev R t F (fun τ => equilibriumSemigroup R.D R.ρβ τ φ)) (Set.Icc 0 t) :=
    hcomp.congr fun σ hσ => hEv σ hσ
  have hNc : ContinuousOn (l2c3_Nn R t F) (Set.Icc 0 t) := l2c3_Nn_cont hF
  have hexpc : Continuous fun σ : ℝ => Real.exp (-2 * κ * (t - σ)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hwc : ContinuousOn (fun σ => R.β⁻¹ * l2c3_Ev R t F
      (fun τ => equilibriumSemigroup R.D R.ρβ τ φ) σ -
      C5 * (Real.exp (-2 * κ * (t - σ)) * l2c3_Nn R t F σ)) (Set.Icc 0 t) :=
    (continuousOn_const.mul hEvc).sub (continuousOn_const.mul (hexpc.continuousOn.mul hNc))
  have hd : ∀ σ ∈ Set.Ioo (0 : ℝ) t, HasDerivAt (l2c3_Fv Cx t F
      (fun τ => equilibriumSemigroup R.D R.ρβ τ φ)) (f σ) σ := fun σ hσ => (hf σ hσ).1
  have hle : ∀ σ ∈ Set.Ioo (0 : ℝ) t, f σ + (R.β⁻¹ * l2c3_Ev R t F
      (fun τ => equilibriumSemigroup R.D R.ρβ τ φ) σ -
      C5 * (Real.exp (-2 * κ * (t - σ)) * l2c3_Nn R t F σ)) ≤ 0 := by
    intro σ hσ
    have hσ' : σ ∈ Set.Icc (0 : ℝ) t := Set.Ioo_subset_Icc_self hσ
    have hb := (hf σ hσ).2
    have h := l2c3_pw3 (ν := R.β⁻¹) (cP := Cx.cP) hν hcP hCm hb (hC σ hσ').2
      (l2c3_Nn_nonneg R t F σ)
    have he : Real.exp (-κ * (t - σ)) ^ 2 = Real.exp (-2 * κ * (t - σ)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [he] at h
    have : C5 * (Real.exp (-2 * κ * (t - σ)) * l2c3_Nn R t F σ) =
        Cm ^ 2 / (R.β⁻¹ * Cx.cP) * Real.exp (-2 * κ * (t - σ)) * l2c3_Nn R t F σ := by
      rw [hC5]; ring
    rw [this]
    linarith
  have hcore := l2c3_core ht.le hA hwc hd hle (τ := t) ⟨ht.le, le_rfl⟩
  have hFt := hFnn t ⟨ht.le, le_rfl⟩
  have hi1 : IntervalIntegrable (fun σ => R.β⁻¹ * l2c3_Ev R t F
      (fun τ => equilibriumSemigroup R.D R.ρβ τ φ) σ) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.le]
    exact (continuousOn_const.mul hEvc).integrableOn_Icc
  have hi2 : IntervalIntegrable (fun σ => C5 * (Real.exp (-2 * κ * (t - σ)) * l2c3_Nn R t F σ))
      volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht.le]
    exact (continuousOn_const.mul (hexpc.continuousOn.mul hNc)).integrableOn_Icc
  rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hcore
  have hcongr : ∫ σ in (0 : ℝ)..t, l2c3_Ev R t F (fun τ => equilibriumSemigroup R.D R.ρβ τ φ) σ =
      ∫ σ in (0 : ℝ)..t, ∫ x, R.ρβ x *
        ‖Torus.grad (F (t - σ)) x - Torus.grad (Fb (t - σ)) x‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [Set.uIcc_of_le ht.le] at hσ
    exact hEv σ hσ
  rw [hcongr] at hcore
  linarith

end HRS.MC.L2C5
