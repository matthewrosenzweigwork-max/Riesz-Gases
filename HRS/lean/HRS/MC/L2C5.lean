import HRS.MC.L2C5Aux5

/-!
# Packet L2C-5: the noise parts of the coupled fields differ by an exponentially small `L²` variance

Relocated proof of `HRS.MC.L2Cov.l2cs_noise_cov_difference` (the frozen statement stays `sorry` in
`HRS/MC/L2CovSpec.lean`; the tie is `HRS/MC/L2C5Tie.lean`).

Route: the combination `Σ₁₁ + Σ₂₂ - 2Σ₁₂` of the three cross noise covariances is `2q ∫_0^t ∫ |√ρ^v∇U - √ρ_β∇Ū|²`.
Pointwise `|√ρ u - √ρ_β w|² ≤ 2(√ρ - √ρ_β)²|u|² + 2ρ_β|u - w|²`.  The first part is `≲ ∫_0^t e^{-2mv} ∫|∇U^{v,t}φ|²`
(`Regime.relax`), the second is the integrated dissipation of the `A_β⁻¹`-Lyapunov functional for the difference
`Q_β(U - Ū)` (Aux3); both are bounded by `e^{-μt}‖Q_βφ‖²` through the weighted energy estimate of L2C-3 (Aux4),
because the energy near `v = 0` (far from the horizon) is damped by the decay of the adjoint.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear HRS.MC.L2C3

namespace HRS.MC.L2C5

variable {d : ℕ}

theorem l2c5_rho_cont' (R : Regime d) (t : ℝ) :
    Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => R.ρ p.1 p.2 :=
  (l2c5_rho_cont R t).comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    (fun p => ⟨p.1.2, Set.mem_univ _⟩)

theorem l2c5_rho_cont_x (R : Regime d) {v : ℝ} (hv : 0 ≤ v) : Continuous (R.ρ v) :=
  (l2c5_rho_cont R v).comp_continuous (continuous_const.prodMk continuous_id)
    (fun x => ⟨⟨hv, le_rfl⟩, Set.mem_univ _⟩)

theorem l2c5_proof (R : Regime d) :
    ∃ C c : ℝ, 0 < c ∧ ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ t : ℝ, 0 ≤ t →
      crossNoiseCov R.D R.D.invβ R.ρ R.ρ t t φ φ +
          crossNoiseCov R.D R.D.invβ (fun _ => R.ρβ) (fun _ => R.ρβ) t t φ φ -
          2 * crossNoiseCov R.D R.D.invβ R.ρ (fun _ => R.ρβ) t t φ φ ≤
        C * Real.exp (-c * t) * PDE.l2NormSq φ := by
  obtain ⟨Cx⟩ := l2c3_ctx R
  obtain ⟨Cm, κ, hCm, hκ, hL⟩ := l2c3_lyap R Cx
  obtain ⟨K1, K2, hK1, hK2, H1⟩ := l2c3_stage1 R Cx hCm hκ hL
  obtain ⟨C5, hC50, Hd⟩ := l2c5_dissipation R Cx hCm hκ hL
  obtain ⟨Cρ, m0, hCρ, hm0, Hρ⟩ := l2c5_sqrt_decay R Cx.hc₀ Cx.hlow'
  obtain ⟨m₀, M₀, hm₀, hbd⟩ := R.bounds
  have hν : 0 < R.β⁻¹ := inv_pos.2 R.hβ
  have hq : R.D.invβ = R.β⁻¹ := R.hDβ
  have hc₀ := Cx.hc₀
  have ha := l2c3_rate_pos R Cx
  set m : ℝ := min m0 κ with hm
  have hmpos : 0 < m := lt_min hm0 hκ
  have hmle : m ≤ κ := min_le_right _ _
  have hmle0 : m ≤ m0 := min_le_left _ _
  set μ : ℝ := min (2 * m) (l2c3_rate R Cx / 2) with hμ
  have hμpos : 0 < μ := lt_min (by positivity) (by positivity)
  set Kc : ℝ := (4 * R.β⁻¹ * Cρ + 4 * C5) * (Cx.c₀⁻¹ * (K2 / R.β⁻¹)) * (2 + 2 * Cx.Λ₀) with hKc
  have hΛ := Cx.hΛ₀
  have hKc0 : 0 ≤ Kc := by positivity
  refine ⟨Kc, μ, hμpos, fun φ hφ t ht => ?_⟩
  have hφ0 : 0 ≤ PDE.l2NormSq φ := integral_nonneg fun x => sq_nonneg _
  have hφc : Continuous φ :=
    Torus.continuous_of_continuous_lift (PDE.MFPair.isCk_of_smooth_ps hφ 0).continuous
  rcases ht.eq_or_lt with h0 | htp
  · subst h0
    have e1 : crossNoiseCov R.D R.D.invβ R.ρ R.ρ 0 0 φ φ = 0 := by simp [crossNoiseCov]
    have e2 : crossNoiseCov R.D R.D.invβ (fun _ => R.ρβ) (fun _ => R.ρβ) 0 0 φ φ = 0 := by
      simp [crossNoiseCov]
    have e3 : crossNoiseCov R.D R.D.invβ R.ρ (fun _ => R.ρβ) 0 0 φ φ = 0 := by simp [crossNoiseCov]
    rw [e1, e2, e3]
    have := mul_nonneg (mul_nonneg hKc0 (Real.exp_pos (-μ * 0)).le) hφ0
    linarith
  -- the classical solutions
  obtain ⟨F, hF, hprop⟩ := l2c3_classical R htp hφ
  have hFs : ∀ s ∈ Set.Icc (0 : ℝ) t, Torus.IsSmooth (F s) := fun s hs => by
    rw [← hprop s hs]; exact (HRS.MC.L2C0.l2c0_proof R φ hφ s t hs.1 hs.2).1
  obtain ⟨Fb, hFb, hpropb, hshift⟩ := HRS.MC.L2C4.l2c4_frozen_classical R htp hφ
  have hFbs : ∀ s ∈ Set.Icc (0 : ℝ) t, Torus.IsSmooth (Fb s) := fun s hs => by
    rw [← hpropb s hs]; exact (HRS.MC.L2C0.l2c0_proof R φ hφ s t hs.1 hs.2).2
  have hSFb : ∀ τ ∈ Set.Ioc (0 : ℝ) t,
      Torus.grad (equilibriumSemigroup R.D R.ρβ τ φ) = Torus.grad (Fb (t - τ)) := by
    intro τ hτ
    have h := hshift (t - τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    rw [sub_sub_cancel] at h
    unfold equilibriumSemigroup
    rw [MFSemigroup.grad_projMean, h]
  -- dissipation and weighted energy
  have hD := Hd htp hφ hF hFs hFb hSFb
  obtain ⟨-, h2⟩ := H1 htp hF hFs
  have hW := h2 t ⟨htp.le, le_rfl⟩
  have hJ := l2c5_weighted_energy R Cx htp hF hFs (m := m) hW
  -- notation
  set Q : ℝ := PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) with hQ
  set J : ℝ := ∫ σ in (0 : ℝ)..t, Real.exp (-2 * m * (t - σ)) * l2c3_Nn R t F σ with hJdef
  set Jk : ℝ := ∫ σ in (0 : ℝ)..t, Real.exp (-2 * κ * (t - σ)) * l2c3_Nn R t F σ with hJk
  set Jd : ℝ := ∫ σ in (0 : ℝ)..t, ∫ x, R.ρβ x *
    ‖Torus.grad (F (t - σ)) x - Torus.grad (Fb (t - σ)) x‖ ^ 2 with hJd
  have hNc : ContinuousOn (l2c3_Nn R t F) (Set.Icc 0 t) := l2c3_Nn_cont hF
  have hJkJ : Jk ≤ J := by
    refine intervalIntegral.integral_mono_on htp.le
      (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le htp.le]
          exact ((Real.continuous_exp.comp (continuous_const.mul
            (continuous_const.sub continuous_id))).continuousOn.mul hNc).integrableOn_Icc)
      (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le htp.le]
          exact ((Real.continuous_exp.comp (continuous_const.mul
            (continuous_const.sub continuous_id))).continuousOn.mul hNc).integrableOn_Icc)
      fun σ hσ => ?_
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (l2c3_Nn_nonneg R t F σ)
    nlinarith [hσ.2]
  have hJdle : Jd ≤ C5 / R.β⁻¹ * J := by
    have h1 : R.β⁻¹ * Jd ≤ C5 * J := hD.trans (mul_le_mul_of_nonneg_left hJkJ hC50)
    rw [div_mul_eq_mul_div, le_div_iff₀ hν]
    linarith
  -- the three noise covariances as integrals over `[0,t]`
  set P1 : ℝ → ℝ := fun v => ∫ x, inner ℝ (Torus.grad (F v) x) (Torus.grad (F v) x) *
    Real.sqrt (R.ρ v x * R.ρ v x) with hP1
  set P2 : ℝ → ℝ := fun v => ∫ x, inner ℝ (Torus.grad (Fb v) x) (Torus.grad (Fb v) x) *
    Real.sqrt (R.ρβ x * R.ρβ x) with hP2
  set P3 : ℝ → ℝ := fun v => ∫ x, inner ℝ (Torus.grad (F v) x) (Torus.grad (Fb v) x) *
    Real.sqrt (R.ρ v x * R.ρβ x) with hP3
  have hA : crossNoiseCov R.D R.D.invβ R.ρ R.ρ t t φ φ = 2 * R.D.invβ * ∫ v in Set.Icc (0 : ℝ) t, P1 v := by
    unfold crossNoiseCov
    rw [min_self]
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun v hv => ?_
    simp only [hprop v hv, hP1]
  have hB : crossNoiseCov R.D R.D.invβ (fun _ => R.ρβ) (fun _ => R.ρβ) t t φ φ =
      2 * R.D.invβ * ∫ v in Set.Icc (0 : ℝ) t, P2 v := by
    unfold crossNoiseCov
    rw [min_self]
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun v hv => ?_
    simp only [hpropb v hv, hP2]
  have hC : crossNoiseCov R.D R.D.invβ R.ρ (fun _ => R.ρβ) t t φ φ =
      2 * R.D.invβ * ∫ v in Set.Icc (0 : ℝ) t, P3 v := by
    unfold crossNoiseCov
    rw [min_self]
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun v hv => ?_
    simp only [hprop v hv, hpropb v hv, hP3]
  -- continuity of the slices
  have hρj := l2c5_rho_cont' R t
  have hρb : Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => R.ρβ p.2 := Cx.hρc.comp continuous_snd
  have hc1 : ContinuousOn P1 (Set.Icc 0 t) :=
    l2c5_cross_cont hF hF (w := fun v x => Real.sqrt (R.ρ v x * R.ρ v x))
      (Real.continuous_sqrt.comp (hρj.mul hρj))
  have hc2 : ContinuousOn P2 (Set.Icc 0 t) :=
    l2c5_cross_cont hFb hFb (w := fun v x => Real.sqrt (R.ρβ x * R.ρβ x))
      (Real.continuous_sqrt.comp (hρb.mul hρb))
  have hc3 : ContinuousOn P3 (Set.Icc 0 t) :=
    l2c5_cross_cont hF hFb (w := fun v x => Real.sqrt (R.ρ v x * R.ρβ x))
      (Real.continuous_sqrt.comp (hρj.mul hρb))
  set Nh : ℝ → ℝ := fun v => ∫ x, ‖Torus.grad (F v) x‖ ^ 2 with hNh
  set Ed : ℝ → ℝ := fun v => ∫ x, R.ρβ x * ‖Torus.grad (F v) x - Torus.grad (Fb v) x‖ ^ 2 with hEd
  have hNhc : ContinuousOn Nh (Set.Icc 0 t) := by
    refine (l2c3_energy_cont hF (w := fun _ => (1 : ℝ)) continuous_const).congr fun r _ => ?_
    simp only [hNh, one_mul]
  have hEdc : ContinuousOn Ed (Set.Icc 0 t) := l2c5_diff_cont hF hFb Cx.hρc
  have hexpv : Continuous fun v : ℝ => Cρ * Real.exp (-2 * m * v) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  -- the pointwise (in `v`) estimate
  have hslice : ∀ v ∈ Set.Icc (0 : ℝ) t,
      P1 v + P2 v - 2 * P3 v ≤ 2 * (Cρ * Real.exp (-2 * m * v)) * Nh v + 2 * Ed v := by
    intro v hv
    have hF1 : Torus.IsCk 1 (F v) := l2c3_isCk_of_smooth (hFs v hv) 1
    have hFb1 : Torus.IsCk 1 (Fb v) := l2c3_isCk_of_smooth (hFbs v hv) 1
    refine l2c5_slice (continuous_grad hF1) (continuous_grad hFb1) (l2c5_rho_cont_x R hv.1) Cx.hρc
      (fun x => hm₀.le.trans (hbd v hv.1 x).1) (fun x => (hc₀.trans_le (Cx.hlow' x)).le)
      (fun x => ?_)
    refine (Hρ v hv.1 x).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCρ)
    nlinarith [hv.1]
  have hint : ∀ {P : ℝ → ℝ}, ContinuousOn P (Set.Icc 0 t) → IntegrableOn P (Set.Icc 0 t) :=
    fun hP => hP.integrableOn_Icc
  have hi12 : IntegrableOn (fun v => P1 v + P2 v) (Set.Icc 0 t) := (hint hc1).add (hint hc2)
  have hi32 : IntegrableOn (fun v => 2 * P3 v) (Set.Icc 0 t) := (hint hc3).const_mul 2
  have hsum : ∫ v in Set.Icc (0 : ℝ) t, (P1 v + P2 v - 2 * P3 v) =
      (∫ v in Set.Icc (0 : ℝ) t, P1 v) + (∫ v in Set.Icc (0 : ℝ) t, P2 v) -
        2 * ∫ v in Set.Icc (0 : ℝ) t, P3 v := by
    rw [integral_sub hi12 hi32, integral_add (hint hc1) (hint hc2), integral_const_mul]
  have hRHSc : ContinuousOn (fun v => 2 * (Cρ * Real.exp (-2 * m * v)) * Nh v + 2 * Ed v)
      (Set.Icc 0 t) :=
    ((continuousOn_const.mul hexpv.continuousOn).mul hNhc).add (continuousOn_const.mul hEdc)
  have hmono : ∫ v in Set.Icc (0 : ℝ) t, (P1 v + P2 v - 2 * P3 v) ≤
      ∫ v in Set.Icc (0 : ℝ) t, (2 * (Cρ * Real.exp (-2 * m * v)) * Nh v + 2 * Ed v) :=
    setIntegral_mono_on (hi12.sub hi32) hRHSc.integrableOn_Icc measurableSet_Icc hslice
  have hsplit : ∫ v in Set.Icc (0 : ℝ) t, (2 * (Cρ * Real.exp (-2 * m * v)) * Nh v + 2 * Ed v) =
      2 * Cρ * (∫ v in Set.Icc (0 : ℝ) t, Real.exp (-2 * m * v) * Nh v) +
        2 * ∫ v in Set.Icc (0 : ℝ) t, Ed v := by
    have c1 : ContinuousOn (fun v => 2 * (Cρ * Real.exp (-2 * m * v)) * Nh v) (Set.Icc 0 t) :=
      (continuousOn_const.mul hexpv.continuousOn).mul hNhc
    have c2 : ContinuousOn (fun v => 2 * Ed v) (Set.Icc 0 t) := continuousOn_const.mul hEdc
    have e1 : ∫ v in Set.Icc (0 : ℝ) t, 2 * (Cρ * Real.exp (-2 * m * v)) * Nh v =
        2 * Cρ * ∫ v in Set.Icc (0 : ℝ) t, Real.exp (-2 * m * v) * Nh v := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Icc fun v _ => by ring
    rw [integral_add c1.integrableOn_Icc c2.integrableOn_Icc, e1, integral_const_mul]
  have hrefl1 : ∫ v in Set.Icc (0 : ℝ) t, Real.exp (-2 * m * v) * Nh v = J := by
    rw [l2c5_reflect htp.le (fun v => Real.exp (-2 * m * v) * Nh v)]
    rfl
  have hrefl2 : ∫ v in Set.Icc (0 : ℝ) t, Ed v = Jd := by
    rw [l2c5_reflect htp.le Ed]
  -- assemble
  have hS : (∫ v in Set.Icc (0 : ℝ) t, P1 v) + (∫ v in Set.Icc (0 : ℝ) t, P2 v) -
      2 * ∫ v in Set.Icc (0 : ℝ) t, P3 v ≤ 2 * Cρ * J + 2 * Jd := by
    rw [← hsum]
    refine hmono.trans ?_
    rw [hsplit, hrefl1, hrefl2]
  have hQb : Q ≤ (2 + 2 * Cx.Λ₀) * PDE.l2NormSq φ :=
    HRS.MC.L2C4.l2c4_Q_bound Cx.hprob Cx.hρc Cx.hup hφc
  rw [hA, hB, hC, hq]
  have hE : 0 < Real.exp (-μ * t) := Real.exp_pos _
  have hJ0 : J ≤ Cx.c₀⁻¹ * (Real.exp (-μ * t) * (K2 * Q / R.β⁻¹)) := hJ
  have hpos : 0 ≤ 4 * R.β⁻¹ * Cρ + 4 * C5 := by positivity
  have hβne : R.β ≠ 0 := R.hβ.ne'
  set I1 := ∫ v in Set.Icc (0 : ℝ) t, P1 v with hI1
  set I2 := ∫ v in Set.Icc (0 : ℝ) t, P2 v with hI2
  set I3 := ∫ v in Set.Icc (0 : ℝ) t, P3 v with hI3
  have hfin : 2 * R.β⁻¹ * I1 + 2 * R.β⁻¹ * I2 - 2 * (2 * R.β⁻¹ * I3) ≤
      Kc * Real.exp (-μ * t) * PDE.l2NormSq φ := by
    calc 2 * R.β⁻¹ * I1 + 2 * R.β⁻¹ * I2 - 2 * (2 * R.β⁻¹ * I3)
        = 2 * R.β⁻¹ * (I1 + I2 - 2 * I3) := by ring
      _ ≤ 2 * R.β⁻¹ * (2 * Cρ * J + 2 * Jd) := mul_le_mul_of_nonneg_left hS (by positivity)
      _ ≤ 2 * R.β⁻¹ * (2 * Cρ * J + 2 * (C5 / R.β⁻¹ * J)) := by gcongr
      _ = (4 * R.β⁻¹ * Cρ + 4 * C5) * J := by field_simp; ring
      _ ≤ (4 * R.β⁻¹ * Cρ + 4 * C5) * (Cx.c₀⁻¹ * (Real.exp (-μ * t) * (K2 * Q / R.β⁻¹))) :=
          mul_le_mul_of_nonneg_left hJ0 hpos
      _ ≤ (4 * R.β⁻¹ * Cρ + 4 * C5) * (Cx.c₀⁻¹ * (Real.exp (-μ * t) *
            (K2 * ((2 + 2 * Cx.Λ₀) * PDE.l2NormSq φ) / R.β⁻¹))) := by gcongr
      _ = Kc * Real.exp (-μ * t) * PDE.l2NormSq φ := by rw [hKc]; ring
  linarith

end HRS.MC.L2C5
