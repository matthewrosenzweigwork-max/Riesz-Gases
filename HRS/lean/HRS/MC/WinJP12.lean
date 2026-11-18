import HRS.MC.WinJSpecDefs
import HRS.MC.WinJP10
import HRS.MC.WinJP11

/-!
# WJ12: P12 `p12a_winJ_eq_of_SJW`, `p_assembly`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.WinJ

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan HRS.MC.Sec7.PID HRS.MC.E213U3

section Packets

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

set_option maxSynthPendingDepth 3

theorem p12a_winJ_eq_of_SJW (R : Regime d) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (zr : ℝ → NegSobolev d (rLvl d)) (hzm : Measurable (nearCoef 0 zr))
    (hint : IntegrableOn (fun v => ‖zr v‖) (Set.Ioc 0 (a + T)))
    (X : TensorDual (PathSpace d m T) 2)
    (hX : SJW R (rLvl d) m T a (nearCoef 0 zr) (Set.Ioc 0 (a + T)) X) :
    winJ R m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T)) = X := by
  classical
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr : rLvl d = 2 * (d : ℝ) + 6 := rfl
  have hG : 0 < a + T := by linarith
  obtain ⟨CL, hCL0, hL⟩ := u3_L1 R (rLvl d) hr m hm (a + T) hG
  have hint' : IntegrableOn (fun v => ‖nearCoef 0 zr v‖) (Set.Ioc 0 (a + T)) :=
    hint.congr_fun (fun v hv => by simp [nearCoef, hv.1.le]) measurableSet_Ioc
  obtain ⟨J0, hJ0, -⟩ := hL 0 le_rfl (nearCoef 0 zr) hzm 0 (a + T) le_rfl le_rfl hint'
  have hJ0' : SJ R (rLvl d) m (a + T) (nearCoef 0 zr) (Set.Ioc 0 (a + T)) J0 :=
    u3_SJ_shift_zero R _ _ _ le_rfl hJ0
  have hIJ := u3_SJ_isJValue R (rLvl d) hr m hm (a + T) hG measurableSet_Ioc hJ0'
  have hIJ' : IsJValue R.D R.ρ m (a + T) (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T)) J0 := by
    refine u3_IsJValue_congr R.D R.ρ m (a + T) measurableSet_Ioc (fun v hv hv0 => ?_) hIJ
    simp only [nearCoef, hv0, if_true]
    rfl
  have hex : ∃ J, IsJValue R.D R.ρ m (a + T) (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T)) J :=
    ⟨J0, hIJ'⟩
  have hjT : jTensor R.D R.ρ m (a + T) (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T)) = J0 := by
    unfold jTensor
    rw [dif_pos hex]
    exact HRS.MC.Sec7.S7PIC.s7_PI_C_J_unique_proof R m (a + T) _ _ _ _ hex.choose_spec hIJ'
  have hwin : winJ R m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T)) =
      tensorPow' 2 (winRestr a ha) J0 := by
    unfold winJ; rw [hjT]
  rw [hwin]
  exact u3_SJW_unique R _ m T a (u3_SJ_toSJW R _ m T a ha hJ0') hX

theorem p_assembly (sd : StatDatum S β₀ m hE) (T : ℝ) (hT : 0 < T) :
    ∃ C c κ : ℝ, 0 < C ∧ 0 < c ∧ 0 < κ ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (zr : ℝ → NegSobolev d (rLvl d)),
      Measurable (nearCoef 0 zr) →
      IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖zr v‖) (Set.Ioc 0 (a + T)) →
      ‖winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T)) -
          winJ (regime sd.Ss S.β sd.hEs) m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T))‖ ≤
        C * ∫ v in Set.Ioc 0 (a + T), Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖zr v‖ := by
  obtain ⟨C, c, κ, hC, hc, hκ, h⟩ := p11c_decay_diff sd T hT
  refine ⟨C + 1, c, κ, by linarith, hc, hκ, fun a ha zr hzm hint => ?_⟩
  have hm : 3 * (d : ℝ) + 8 < m := hE.m_gt
  have hmeas : AEStronglyMeasurable (fun v => ‖nearCoef 0 zr v‖) (volume.restrict (Set.Ioc 0 (a + T))) :=
    hzm.norm.aestronglyMeasurable
  have hint' : IntegrableOn (fun v => ‖nearCoef 0 zr v‖) (Set.Ioc 0 (a + T)) := by
    refine Integrable.mono' (hint.const_mul (Real.exp (c * a))) hmeas ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun v hv => ?_
    have hv0 : 0 ≤ v := hv.1.le
    have hnc : nearCoef 0 zr v = zr v := by simp [nearCoef, hv0]
    rw [hnc, Real.norm_of_nonneg (norm_nonneg _), ← mul_assoc, ← Real.exp_add]
    have h1 : 1 ≤ Real.exp (c * a + -c * (a - v)) := by
      rw [Real.one_le_exp_iff]; nlinarith
    nlinarith [norm_nonneg (zr v)]
  obtain ⟨X, X', hX, hX', hXX⟩ := h a ha (nearCoef 0 zr) hzm 0 (a + T) le_rfl (by linarith) le_rfl hint'
  have e1 := p12a_winJ_eq_of_SJW (regime S β₀ hE) hm T hT a ha zr hzm
    (hint'.congr_fun (fun v hv => by simp [nearCoef, hv.1.le]) measurableSet_Ioc) X hX
  have e2 := p12a_winJ_eq_of_SJW (regime sd.Ss S.β sd.hEs) hm T hT a ha zr hzm
    (hint'.congr_fun (fun v hv => by simp [nearCoef, hv.1.le]) measurableSet_Ioc) X' hX'
  rw [e1, e2]
  have hI : ∫ v in Set.Ioc 0 (a + T), Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖nearCoef 0 zr v‖ =
      ∫ v in Set.Ioc 0 (a + T), Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖zr v‖ := by
    refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    simp [nearCoef, hv.1.le]
  rw [hI] at hXX
  refine hXX.trans ?_
  have hnn : 0 ≤ ∫ v in Set.Ioc 0 (a + T), Real.exp (-c * (a - v)) * Real.exp (-κ * v) * ‖zr v‖ :=
    setIntegral_nonneg measurableSet_Ioc fun v _ => by positivity
  nlinarith

end Packets

end HRS.MC.WinJ

end
