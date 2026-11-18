import HRS.MC.CepE4Aux1
import Mathlib.Analysis.ODE.Gronwall

/-!
# Packet CEPE4, auxiliary 2: Gronwall (copy of `HRS.MD.LT337P8.lt8_gronwall_aff`) and the pathwise identity
-/

open Set Filter Topology MeasureTheory
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE4

open HRS.MC.Cepa

/-- Integral Grönwall inequality with an additive forcing term. -/
theorem e4_gronwall_aff {φ : ℝ → ℝ} {T κ a b : ℝ} (hT : 0 ≤ T) (hκ : 0 ≤ κ) (hb : 0 ≤ b) (ha : 0 ≤ a)
    (hφ : ContinuousOn φ (Set.Icc 0 T))
    (h : ∀ t ∈ Set.Icc 0 T, φ t ≤ a + ∫ r in (0 : ℝ)..t, (κ * φ r + b)) :
    ∀ t ∈ Set.Icc 0 T, φ t ≤ Real.exp (κ * T) * (a + b * T) := by
  set cl : ℝ → ℝ := fun r => max 0 (min r T) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hclm : ∀ r, cl r ∈ Set.Icc (0 : ℝ) T := fun r => ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hcle : ∀ r ∈ Set.Icc (0 : ℝ) T, cl r = r := fun r hr => by
    simp only [hcl]; rw [min_eq_left hr.2]; exact max_eq_right hr.1
  set φt : ℝ → ℝ := fun r => φ (cl r) with hφt
  have hφtc : Continuous φt := hφ.comp_continuous hclc hclm
  set G : ℝ → ℝ := fun t => a + ∫ r in (0 : ℝ)..t, (κ * φt r + b) with hG
  have hGd : ∀ x, HasDerivAt G (κ * φt x + b) x := fun x => by
    have hc : Continuous fun r => κ * φt r + b := (continuous_const.mul hφtc).add continuous_const
    have := (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
    exact this.const_add a
  have hGφ : ∀ t ∈ Set.Icc (0 : ℝ) T, φ t ≤ G t := by
    intro t ht
    have := h t ht
    have e : ∫ r in (0 : ℝ)..t, (κ * φt r + b) = ∫ r in (0 : ℝ)..t, (κ * φ r + b) := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [Set.uIcc_of_le ht.1] at hr
      simp only [hφt]
      rw [hcle r ⟨hr.1, hr.2.trans ht.2⟩]
    simp only [hG]
    rw [e]
    exact this
  have key := le_gronwallBound_of_liminf_deriv_right_le (f := G) (f' := fun x => κ * φt x + b)
    (δ := a) (K := κ) (ε := b) (a := 0) (b := T)
    (fun x _ => (hGd x).continuousAt.continuousWithinAt)
    (fun x _ r hr => (hGd x).hasDerivWithinAt.liminf_right_slope_le hr)
    (by simp [hG]) (fun x hx => by
      have h1 : φt x = φ x := by simp only [hφt]; rw [hcle x ⟨hx.1, hx.2.le⟩]
      have h2 := hGφ x ⟨hx.1, hx.2.le⟩
      rw [h1]
      nlinarith)
  intro t ht
  have h1 := (hGφ t ht).trans (key t ht)
  rw [sub_zero] at h1
  refine h1.trans ?_
  unfold gronwallBound
  have he : 1 ≤ Real.exp (κ * t) := Real.one_le_exp (mul_nonneg hκ ht.1)
  have hmono : Real.exp (κ * t) ≤ Real.exp (κ * T) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 hκ)
  have hbt : b * t ≤ b * T := mul_le_mul_of_nonneg_left ht.2 hb
  split_ifs with hk
  · subst hk
    simp only [zero_mul, Real.exp_zero, one_mul]
    linarith
  · have hkpos : 0 < κ := lt_of_le_of_ne hκ (Ne.symm hk)
    have hexp : Real.exp (κ * t) - 1 ≤ κ * t * Real.exp (κ * t) := by
      have := Real.add_one_le_exp (-(κ * t))
      rw [Real.exp_neg] at this
      have hp : 0 < Real.exp (κ * t) := Real.exp_pos _
      have : 1 - κ * t ≤ (Real.exp (κ * t))⁻¹ := by linarith
      calc Real.exp (κ * t) - 1 = Real.exp (κ * t) * (1 - (Real.exp (κ * t))⁻¹) := by field_simp
        _ ≤ Real.exp (κ * t) * (κ * t) := mul_le_mul_of_nonneg_left (by linarith) hp.le
        _ = _ := by ring
    have h3 : b / κ * (Real.exp (κ * t) - 1) ≤ b * t * Real.exp (κ * t) := by
      calc b / κ * (Real.exp (κ * t) - 1) ≤ b / κ * (κ * t * Real.exp (κ * t)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = b * t * Real.exp (κ * t) := by field_simp
    have h4 : a * Real.exp (κ * t) + b * t * Real.exp (κ * t) = Real.exp (κ * t) * (a + b * t) := by ring
    have h5 : Real.exp (κ * t) * (a + b * t) ≤ Real.exp (κ * T) * (a + b * T) := by
      have : 0 ≤ a + b * t := by have := mul_nonneg hb ht.1; linarith
      exact mul_le_mul hmono (by linarith) this (Real.exp_pos _).le
    linarith

/-- Pathwise identity (no probability): for `Z_s = z₀ + ∫₀ˢ b + σ' w_s` with `b, w` continuous. -/
theorem e4_path_ident {N : ℕ} (b w : ℝ → Ch N) (hb : Continuous b) (hw : Continuous w)
    (z0 ρ : Ch N) (σ' t : ℝ) :
    (1 / 2) * ‖(z0 + ∫ r in (0 : ℝ)..t, b r) + σ' • w t - ρ‖ ^ 2 =
      (1 / 2) * ‖z0 - ρ‖ ^ 2 +
        (∫ s in (0 : ℝ)..t, inner ℝ ((z0 + ∫ r in (0 : ℝ)..s, b r) + σ' • w s - ρ) (b s)) +
        (1 / 2) * σ' ^ 2 * ‖w t‖ ^ 2 + σ' * inner ℝ (z0 - ρ) (w t) +
        σ' * ∫ s in (0 : ℝ)..t, inner ℝ (b s) (w t - w s) := by
  set U : ℝ → Ch N := fun s => z0 + (∫ r in (0 : ℝ)..s, b r) - ρ with hU
  have hUd : ∀ s, HasDerivAt U (b s) s := fun s => by
    have := ((hb.integral_hasStrictDerivAt 0 s).hasDerivAt.const_add z0).sub_const ρ
    exact this
  have hUc : Continuous U := continuous_iff_continuousAt.2 fun s => (hUd s).continuousAt
  have hbw : Continuous fun s => inner ℝ (U s) (b s) := hUc.inner hb
  have h1 : (1 / 2) * ‖U t‖ ^ 2 = (1 / 2) * ‖U 0‖ ^ 2 + ∫ s in (0 : ℝ)..t, inner ℝ (U s) (b s) := by
    have hd : ∀ s ∈ Set.uIcc 0 t, HasDerivAt (fun s => (1 / 2) * ‖U s‖ ^ 2) (inner ℝ (U s) (b s)) s := by
      intro s _
      have := (hUd s).norm_sq
      have h2 := this.const_mul (1 / 2)
      convert h2 using 1
      ring
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hbw.intervalIntegrable _ _)
    linarith
  have hU0 : U 0 = z0 - ρ := by simp [hU]
  -- the cross term
  have hcross : inner ℝ (U t) (w t) = inner ℝ (z0 - ρ) (w t) + ∫ s in (0 : ℝ)..t, inner ℝ (b s) (w t) := by
    have e : U t = (z0 - ρ) + ∫ r in (0 : ℝ)..t, b r := by simp only [hU]; abel
    rw [e, inner_add_left]
    congr 1
    have := (innerSL ℝ (w t)).intervalIntegral_comp_comm (a := 0) (b := t) (f := b) (μ := MeasureTheory.volume)
      (hb.intervalIntegrable _ _)
    simp only [innerSL_apply_apply] at this
    exact (real_inner_comm _ _).trans (this.symm.trans
      (intervalIntegral.integral_congr fun s _ => real_inner_comm _ _))
  have hIs : ∫ s in (0 : ℝ)..t, inner ℝ (U s + σ' • w s) (b s) =
      (∫ s in (0 : ℝ)..t, inner ℝ (U s) (b s)) + σ' * ∫ s in (0 : ℝ)..t, inner ℝ (w s) (b s) := by
    simp only [inner_add_left, real_inner_smul_left]
    rw [intervalIntegral.integral_add (hbw.intervalIntegrable _ _)
      ((show Continuous fun s => σ' * inner ℝ (w s) (b s) from
        continuous_const.mul (hw.inner hb)).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  have hIw : ∫ s in (0 : ℝ)..t, inner ℝ (b s) (w t - w s) =
      (∫ s in (0 : ℝ)..t, inner ℝ (b s) (w t)) - ∫ s in (0 : ℝ)..t, inner ℝ (w s) (b s) := by
    simp only [inner_sub_right]
    rw [intervalIntegral.integral_sub ((hb.inner continuous_const).intervalIntegrable _ _)
      ((hb.inner hw).intervalIntegrable _ _)]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp [real_inner_comm]
  have hZ : ∀ s, (z0 + ∫ r in (0 : ℝ)..s, b r) + σ' • w s - ρ = U s + σ' • w s := fun s => by
    simp only [hU]; abel
  simp only [hZ]
  have hn : ‖U t + σ' • w t‖ ^ 2 = ‖U t‖ ^ 2 + 2 * (σ' * inner ℝ (U t) (w t)) + σ' ^ 2 * ‖w t‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hn, hIs, hIw, hcross]
  rw [hU0] at h1
  linarith [h1]

end HRS.MC.CepE4
