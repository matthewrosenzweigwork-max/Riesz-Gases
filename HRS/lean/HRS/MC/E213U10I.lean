import HRS.MC.E213U10H

/-!
# Packet e213u10, part I: Lipschitz bound and domination of the covariance functional

`u10_FJ_lip_core`: `|FJ(w,z) - FJ(w',z')| ≤ CJ L (CY ‖w-w'‖ ‖z‖ + ‖z-z'‖)`; `u10_FJ_abs_le`: `|FJ(w,z)| ≤ CJ L ‖z‖`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

/-- Comparison of the RS integrals of two summands both dominated by `K |(u,u'] ∩ [b,∞)|`. -/
theorem u10_rs_cmp_const {T : ℝ} (hT : 0 < T) {S₁ S₂ : ℝ → ℝ → ℝ → ℝ} {I₁ I₂ : ℝ} (hS₁ : IsRS T S₁ I₁)
    (hS₂ : IsRS T S₂ I₂) (b K : ℝ) (hK : 0 ≤ K)
    (h : ∀ τ u u' : ℝ, 0 ≤ u → u ≤ τ → τ ≤ u' → u' ≤ T →
      |S₁ τ u u' - S₂ τ u u'| ≤ K * (volume (Set.Ioc u u' ∩ Set.Ici b)).toReal) :
    |I₁ - I₂| ≤ K * (volume (Set.Ioc 0 T ∩ Set.Ici b)).toReal := by
  set g : ℝ → ℝ := Set.indicator (Set.Ici b) (fun _ => K) with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v => Set.indicator_nonneg (fun v _ => hK) v
  have hgi : IntegrableOn g (Set.Ioc 0 T) := by
    have h1 : IntegrableOn (fun _ : ℝ => K) (Set.Ioc 0 T) := integrableOn_const (by simp)
    exact h1.indicator measurableSet_Ici
  have hint : ∀ u u' : ℝ, ∫ v in Set.Ioc u u', g v = K * (volume (Set.Ioc u u' ∩ Set.Ici b)).toReal := by
    intro u u'
    rw [hg, setIntegral_indicator measurableSet_Ici, setIntegral_const, smul_eq_mul, mul_comm]
    rfl
  have key := u10_rs_cmp hT hS₁ hS₂ g hg0 hgi (fun τ u u' hu huτ hτu' hu' => by
    rw [hint]; exact h τ u u' hu huτ hτu' hu')
  rwa [hint] at key

theorem u10_vol_le (a T b L : ℝ) (hL : 0 ≤ L) (hH : a + T ≤ b + L) :
    (volume (Set.Ioc 0 (a + T) ∩ Set.Ici b)).toReal ≤ L := by
  have hsub : Set.Ioc 0 (a + T) ∩ Set.Ici b ⊆ Set.Icc b (b + L) := fun v hv => ⟨hv.2, hv.1.2.trans hH⟩
  have h2 : volume (Set.Icc b (b + L)) ≠ ⊤ := by simp
  have h3 := ENNReal.toReal_mono h2 (measure_mono hsub)
  rwa [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith), add_sub_cancel_left] at h3

theorem u10_FJ_lip_core (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (hcb : cbNorm 5 Φ ≤ 1) (b L : ℝ) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (hH : a + T ≤ b + L) (CJ CY : ℝ) (hCJ0 : 0 ≤ CJ) (hCY0 : 0 ≤ CY) (hJ : U10_JNear hE T a ha b CJ)
    (hCY : U10_PredBound hE T a ha CY)
    (x x' : PathSpace d (rLvl d) L × PathSpace d (rLvl d) L) :
    |u10_FJ hE T a ha Φ b L hL hH x - u10_FJ hE T a ha Φ b L hL hH x'| ≤
      CJ * L * (CY * ‖x.1 - x'.1‖ * ‖x.2‖ + ‖x.2 - x'.2‖) := by
  have hH0 : 0 < a + T := by linarith
  have hK : 0 ≤ CJ * (CY * ‖x.1 - x'.1‖ * ‖x.2‖ + ‖x.2 - x'.2‖) := by positivity
  have key := u10_rs_cmp_const hH0 (u10_SJ_isRS hE T hT a ha Φ hΦ b L hL hH x)
    (u10_SJ_isRS hE T hT a ha Φ hΦ b L hL hH x') b _ hK
    (fun τ u u' hu huτ hτu' hu' =>
      u10_SJ_diff_le hE T hT a ha Φ hΦ hcb b L hb hL hH CJ CY hCJ0 hCY0 hJ hCY x x' hu huτ hτu' hu')
  refine key.trans ?_
  calc CJ * (CY * ‖x.1 - x'.1‖ * ‖x.2‖ + ‖x.2 - x'.2‖) * (volume (Set.Ioc 0 (a + T) ∩ Set.Ici b)).toReal
      ≤ CJ * (CY * ‖x.1 - x'.1‖ * ‖x.2‖ + ‖x.2 - x'.2‖) * L :=
        mul_le_mul_of_nonneg_left (u10_vol_le a T b L hL hH) hK
    _ = _ := by ring

theorem u10_FJ_abs_le (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (hcb : cbNorm 5 Φ ≤ 1) (b L : ℝ) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (hH : a + T ≤ b + L) (CJ : ℝ) (hCJ0 : 0 ≤ CJ) (hJ : U10_JNear hE T a ha b CJ)
    (x : PathSpace d (rLvl d) L × PathSpace d (rLvl d) L) :
    |u10_FJ hE T a ha Φ b L hL hH x| ≤ CJ * L * ‖x.2‖ := by
  have hH0 : 0 < a + T := by linarith
  have hK : 0 ≤ CJ * ‖x.2‖ := by positivity
  have key := u10_rs_cmp_const hH0 (u10_SJ_isRS hE T hT a ha Φ hΦ b L hL hH x) (u10_isRS_zero (a + T)) b _ hK
    (fun τ u u' hu huτ hτu' hu' => by
      simp only [sub_zero]
      exact u10_SJ_abs_le hE T hT a ha Φ hΦ hcb b L hb hL hH CJ hCJ0 hJ x hu huτ hτu' hu')
  rw [sub_zero] at key
  refine key.trans ?_
  calc CJ * ‖x.2‖ * (volume (Set.Ioc 0 (a + T) ∩ Set.Ici b)).toReal ≤ CJ * ‖x.2‖ * L :=
        mul_le_mul_of_nonneg_left (u10_vol_le a T b L hL hH) hK
    _ = _ := by ring

end HRS.MC.E213U10

end
