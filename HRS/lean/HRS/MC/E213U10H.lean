import HRS.MC.E213U10G

/-!
# Packet e213u10, part H: the covariance functional on the path space

`u10_zq b L z v = pathAt z (v - b)`; `u10_cJ` is the near covariance coefficient `nearCoef b (embed ∘ zq)`;
`u10_SJ x`, `u10_FJ x` the covariance summand/integral for `x = (w, z) ∈ 𝒳_{r,L} × 𝒳_{r,L}`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

/-- The coefficient on `[b, b+L]` of a window path (translated). -/
def u10_zq (b L : ℝ) (z : PathSpace d (rLvl d) L) : ℝ → NegSobolev d (rLvl d) := fun v => pathAt z (v - b)

theorem u10_zq_meas (b L : ℝ) (z : PathSpace d (rLvl d) L) : Measurable (u10_zq b L z) :=
  (u10_pathAt_meas z).comp (measurable_sub_const b)

theorem u10_zq_norm_le (b L : ℝ) (z : PathSpace d (rLvl d) L) (v : ℝ) : ‖u10_zq b L z v‖ ≤ ‖z‖ :=
  u10_pathAt_norm_le z _

theorem u10_zq_sub (b L : ℝ) (z z' : PathSpace d (rLvl d) L) (v : ℝ) :
    u10_zq b L (z - z') v = u10_zq b L z v - u10_zq b L z' v :=
  u10_pathAt_sub z z' _

/-- The near covariance coefficient of a window path. -/
def u10_cJ (b L : ℝ) (m : ℝ) (z : PathSpace d (rLvl d) L) : ℝ → NegSobolev d m :=
  nearCoef b (fun v => NegSobolev.embed m (u10_zq b L z v))

section Defs

variable (hE : EdgeworthHyp S β₀ m) (T : ℝ) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (b L : ℝ)
  (hL : 0 ≤ L) (hH : a + T ≤ b + L)

/-- The covariance summand on the pair space. -/
def u10_SJ (x : PathSpace d (rLvl d) L × PathSpace d (rLvl d) L) : ℝ → ℝ → ℝ → ℝ :=
  rsSumJ (Ucan hE T a ha Φ) (u10_Y hE T a ha b L hL hH x.1)
    (fun u u' => winJ (regime S β₀ hE) m T a ha (u10_cJ b L m x.2) (Set.Ioc u u'))

/-- The covariance integral on the pair space. -/
def u10_FJ (x : PathSpace d (rLvl d) L × PathSpace d (rLvl d) L) : ℝ :=
  rsLim (a + T) (u10_SJ hE T a ha Φ b L hL hH x)

end Defs

theorem u10_SJ_isRS (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (b L : ℝ) (hL : 0 ≤ L) (hH : a + T ≤ b + L)
    (x : PathSpace d (rLvl d) L × PathSpace d (rLvl d) L) :
    IsRS (a + T) (u10_SJ hE T a ha Φ b L hL hH x) (u10_FJ hE T a ha Φ b L hL hH x) := by
  have hH0 : 0 < a + T := by linarith
  have hreg := HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ
  have hY := HRS.MC.E213U7.e213u7_Y_cont hE T hT a ha (u10_liftW hE b L (a + T) hL hH x.1)
  have hMc := HRS.MC.E213U7.e213u7_iFD_cont hE T a ha Φ hreg _ hY 2 le_rfl
  obtain ⟨I, hI⟩ := HRS.MC.E213U7.e213u7_J_exists hE T hT a ha _ hMc (u10_cJ b L m x.2)
    (nearCoef 0 (nearCoef b (u10_zq b L x.2)))
    (fun v hv => by
      rw [HRS.MC.E213U7.e213u7_nc0_apply _ hv]
      exact congrFun (HRS.MC.E213U7.e213u7_near_embed hE b (u10_zq b L x.2)) v)
    (u10_nearCoef0_meas b (u10_zq_meas b L x.2)) ‖x.2‖
    (fun u _ => (HRS.MC.E213U7.e213u7_norm_near_le 0 _ u).trans
      ((HRS.MC.E213U7.e213u7_norm_near_le b _ u).trans (u10_zq_norm_le b L x.2 u)))
  have hI' : IsRS (a + T) (u10_SJ hE T a ha Φ b L hL hH x) I := hI
  have : u10_FJ hE T a ha Φ b L hL hH x = I := HRS.MC.E213U7.e213u7_rsLim_eq hH0 hI'
  rw [this]
  exact hI'

/-- Splitting of the near covariance coefficient: `c_z = c_{z'} + c_{z - z'}`. -/
theorem u10_cJ_split (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (b L : ℝ)
    (z z' : PathSpace d (rLvl d) L) {u u' : ℝ} (hu : 0 ≤ u) (huu' : u ≤ u') (hu' : u' ≤ a + T) :
    winJ (regime S β₀ hE) m T a ha (u10_cJ b L m z) (Set.Ioc u u') =
      winJ (regime S β₀ hE) m T a ha (u10_cJ b L m z') (Set.Ioc u u') +
      winJ (regime S β₀ hE) m T a ha (u10_cJ b L m (z - z')) (Set.Ioc u u') := by
  have hadd := HRS.MC.E213U2.winJ_add_proof hE T hT a ha (nearCoef b (u10_zq b L z'))
    (nearCoef b (u10_zq b L (z - z')))
    (u10_nearCoef0_meas b (u10_zq_meas b L z')) (u10_nearCoef0_meas b (u10_zq_meas b L (z - z'))) ‖z'‖ ‖z - z'‖
    (fun v _ => (HRS.MC.E213U7.e213u7_norm_near_le b _ v).trans (u10_zq_norm_le b L z' v))
    (fun v _ => (HRS.MC.E213U7.e213u7_norm_near_le b _ v).trans (u10_zq_norm_le b L (z - z') v)) u u' hu huu' hu'
  have e1 : (fun v => NegSobolev.embed m (nearCoef b (u10_zq b L z') v + nearCoef b (u10_zq b L (z - z')) v)) =
      u10_cJ b L m z := by
    funext v
    unfold u10_cJ nearCoef
    by_cases h : b ≤ v
    · simp only [if_pos h]
      congr 1
      rw [u10_zq_sub]
      abel
    · simp only [if_neg h, add_zero]
      exact HRS.MC.E213U7.e213u7_embed_zero hE
  have e2 : (fun v => NegSobolev.embed m (nearCoef b (u10_zq b L z') v)) = u10_cJ b L m z' :=
    (HRS.MC.E213U7.e213u7_near_embed hE b (u10_zq b L z')).symm
  have e3 : (fun v => NegSobolev.embed m (nearCoef b (u10_zq b L (z - z')) v)) = u10_cJ b L m (z - z') :=
    (HRS.MC.E213U7.e213u7_near_embed hE b (u10_zq b L (z - z'))).symm
  rw [e1, e2, e3] at hadd
  exact hadd

theorem u10_SJ_abs_le (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (hcb : cbNorm 5 Φ ≤ 1) (b L : ℝ) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (hH : a + T ≤ b + L) (CJ : ℝ) (hCJ0 : 0 ≤ CJ) (hJ : U10_JNear hE T a ha b CJ)
    (x : PathSpace d (rLvl d) L × PathSpace d (rLvl d) L) {τ u u' : ℝ} (hu : 0 ≤ u) (huτ : u ≤ τ) (hτu' : τ ≤ u')
    (hu' : u' ≤ a + T) :
    |u10_SJ hE T a ha Φ b L hL hH x τ u u'| ≤ CJ * ‖x.2‖ * (volume (Set.Ioc u u' ∩ Set.Ici b)).toReal := by
  have hτ : τ ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hu.trans huτ, hτu'.trans hu'⟩
  have hreg := HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ
  have huu' : u ≤ u' := huτ.trans hτu'
  have hJn := u10_winJ_near_sharp hE T a ha b CJ hb hCJ0 hJ (u10_zq b L x.2)
    (u10_nearCoef_meas 0 (u10_zq_meas b L x.2)) ‖x.2‖ (norm_nonneg _)
    (fun v _ => u10_zq_norm_le b L x.2 v) hu huu' hu'
  have hH2 := u10_iFD2_norm_le hE T a ha Φ hreg hτ (u10_Y hE T a ha b L hL hH x.1 τ)
  unfold u10_SJ rsSumJ
  rw [← Real.norm_eq_abs]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  calc ‖winJ (regime S β₀ hE) m T a ha (u10_cJ b L m x.2) (Set.Ioc u u')‖ *
        ‖iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ) (u10_Y hE T a ha b L hL hH x.1 τ)‖
      ≤ (CJ * ‖x.2‖ * (volume (Set.Ioc u u' ∩ Set.Ici b)).toReal) * 1 :=
        mul_le_mul hJn (hH2.trans hcb) (norm_nonneg _) (mul_nonneg (mul_nonneg hCJ0 (norm_nonneg _)) ENNReal.toReal_nonneg)
    _ = _ := mul_one _

theorem u10_SJ_diff_le (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (hcb : cbNorm 5 Φ ≤ 1) (b L : ℝ) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (hH : a + T ≤ b + L) (CJ CY : ℝ) (hCJ0 : 0 ≤ CJ) (hCY0 : 0 ≤ CY) (hJ : U10_JNear hE T a ha b CJ)
    (hCY : U10_PredBound hE T a ha CY)
    (x x' : PathSpace d (rLvl d) L × PathSpace d (rLvl d) L) {τ u u' : ℝ} (hu : 0 ≤ u) (huτ : u ≤ τ)
    (hτu' : τ ≤ u') (hu' : u' ≤ a + T) :
    |u10_SJ hE T a ha Φ b L hL hH x τ u u' - u10_SJ hE T a ha Φ b L hL hH x' τ u u'| ≤
      CJ * (CY * ‖x.1 - x'.1‖ * ‖x.2‖ + ‖x.2 - x'.2‖) * (volume (Set.Ioc u u' ∩ Set.Ici b)).toReal := by
  have hτ : τ ∈ Set.Icc (0 : ℝ) (a + T) := ⟨hu.trans huτ, hτu'.trans hu'⟩
  have hreg := HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ
  have huu' : u ≤ u' := huτ.trans hτu'
  have hsplit := u10_cJ_split hE T hT a ha b L x.2 x'.2 hu huu' hu'
  set V : ℝ := (volume (Set.Ioc u u' ∩ Set.Ici b)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set Jz := winJ (regime S β₀ hE) m T a ha (u10_cJ b L m x.2) (Set.Ioc u u') with hJz
  set Jz' := winJ (regime S β₀ hE) m T a ha (u10_cJ b L m x'.2) (Set.Ioc u u') with hJz'
  set Jδ := winJ (regime S β₀ hE) m T a ha (u10_cJ b L m (x.2 - x'.2)) (Set.Ioc u u') with hJδ
  have hJzn : ‖Jz‖ ≤ CJ * ‖x.2‖ * V :=
    u10_winJ_near_sharp hE T a ha b CJ hb hCJ0 hJ (u10_zq b L x.2)
      (u10_nearCoef_meas 0 (u10_zq_meas b L x.2)) ‖x.2‖ (norm_nonneg _)
      (fun v _ => u10_zq_norm_le b L x.2 v) hu huu' hu'
  have hJδn : ‖Jδ‖ ≤ CJ * ‖x.2 - x'.2‖ * V :=
    u10_winJ_near_sharp hE T a ha b CJ hb hCJ0 hJ (u10_zq b L (x.2 - x'.2))
      (u10_nearCoef_meas 0 (u10_zq_meas b L (x.2 - x'.2))) ‖x.2 - x'.2‖ (norm_nonneg _)
      (fun v _ => u10_zq_norm_le b L (x.2 - x'.2) v) hu huu' hu'
  set A := iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ) (u10_Y hE T a ha b L hL hH x.1 τ) with hAdef
  set A' := iteratedFDeriv ℝ 2 (Ucan hE T a ha Φ τ) (u10_Y hE T a ha b L hL hH x'.1 τ) with hA'def
  have hA' : ‖A'‖ ≤ 1 := (u10_iFD2_norm_le hE T a ha Φ hreg hτ _).trans hcb
  have hAA' : ‖A - A'‖ ≤ CY * ‖x.1 - x'.1‖ := by
    refine (u10_iFD2_lip hE T a ha Φ hreg hτ _ _).trans ?_
    have h := u10_Y_sub_norm_le hE T hT a ha b L hL hH CY hCY0 hCY x.1 x'.1 hτ
    calc cbNorm 5 Φ * ‖u10_Y hE T a ha b L hL hH x.1 τ - u10_Y hE T a ha b L hL hH x'.1 τ‖
        ≤ 1 * (CY * ‖x.1 - x'.1‖) := mul_le_mul hcb h (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hdiff : Jz - Jz' = Jδ := by rw [hsplit]; abel
  unfold u10_SJ rsSumJ
  have e : Jz A - Jz' A' = Jz (A - A') + Jδ A' := by
    rw [← hdiff, ContinuousLinearMap.sub_apply, map_sub]; ring
  rw [e]
  calc |Jz (A - A') + Jδ A'| ≤ |Jz (A - A')| + |Jδ A'| := abs_add_le _ _
    _ ≤ ‖Jz‖ * ‖A - A'‖ + ‖Jδ‖ * ‖A'‖ := by
        rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
        exact add_le_add (Jz.le_opNorm _) (Jδ.le_opNorm _)
    _ ≤ (CJ * ‖x.2‖ * V) * (CY * ‖x.1 - x'.1‖) + (CJ * ‖x.2 - x'.2‖ * V) * 1 := by
        refine add_le_add (mul_le_mul hJzn hAA' (norm_nonneg _) (by positivity)) ?_
        exact mul_le_mul hJδn hA' (norm_nonneg _) (by positivity)
    _ = _ := by ring

end HRS.MC.E213U10

end
