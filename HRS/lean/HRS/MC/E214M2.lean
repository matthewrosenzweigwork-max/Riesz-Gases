import HRS.MC.E214PD
import HRS.MC.E213U3G
import HRS.MC.E213U1b
import HRS.MC.E213U2

/-!
# Packet e214m, file 2: the weighted `L¹` bounds over the whole range `(0, a+T]`

`winDrift_L1_proof`, `winJ_L1_proof` (statements of `E214Plan`, relocated): `winDrift_far_proof` / `winJ_far_proof`
with `b = a + T + 1` (so `farCoef b f = f` on `(0, a+T]`), `u = 0`, `u' = a + T`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

set_option maxSynthPendingDepth 3

namespace HRS.MC.E214M

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final

variable {d : ℕ}

theorem m_Ioc_inter_Iio {a T : ℝ} :
    Set.Ioc (0 : ℝ) (a + T) ∩ Set.Iio (a + T + 1) = Set.Ioc 0 (a + T) :=
  Set.inter_eq_left.2 fun v hv => by simp only [Set.mem_Iio]; linarith [hv.2]

theorem m_farCoef_eq_on {m : ℝ} {a T : ℝ} (f : ℝ → NegSobolev d m) :
    ∀ u ∈ Set.Ioc (0 : ℝ) (a + T), farCoef (a + T + 1) f u = f u := by
  intro u hu
  unfold farCoef
  rw [if_pos (by linarith [hu.2])]

theorem m_winDrift_far_eq {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m) (T : ℝ)
    (a : ℝ) (ha : 0 ≤ a) (f : ℝ → NegSobolev d m) :
    winDrift (regime S β₀ hE) m T a ha (farCoef (a + T + 1) f) 0 (a + T) =
      winDrift (regime S β₀ hE) m T a ha f 0 (a + T) := by
  unfold winDrift driftInc
  congr 2
  funext t
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  rw [m_farCoef_eq_on f u ⟨hu.1, hu.2.trans (min_le_left _ _)⟩]

theorem winDrift_L1_proof {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (bq : ℝ → NegSobolev d (rLvl d)),
      Measurable (nearCoef 0 bq) →
      IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖bq v‖) (Set.Ioc 0 (a + T)) →
      ‖winDrift (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (bq v)) 0 (a + T)‖ ≤
        C * ∫ v in Set.Ioc 0 (a + T), Real.exp (-c * (a - v)) * ‖bq v‖ := by
  obtain ⟨C, c, hC, hc, hF⟩ := HRS.MC.E213U1.winDrift_far_proof hE T hT
  refine ⟨C, c, hC, hc, fun a ha bq hbm hbi => ?_⟩
  have hb : 0 ≤ a + T + 1 := by linarith
  have hmin : min (a + T + 1) (a + T) = a + T := min_eq_right (by linarith)
  have hint : IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖bq v‖)
      (Set.Ioc 0 (min (a + T + 1) (a + T))) := by rw [hmin]; exact hbi
  have h := hF a ha (a + T + 1) hb bq hbm hint 0 (a + T) le_rfl (by linarith) le_rfl
  rw [m_winDrift_far_eq hE T a ha, m_Ioc_inter_Iio] at h
  exact h

theorem winJ_L1_proof {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (zr : ℝ → NegSobolev d (rLvl d)),
      Measurable (nearCoef 0 zr) →
      IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖zr v‖) (Set.Ioc 0 (a + T)) →
      (∃ J, IsJValue (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + T)
          (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T)) J) ∧
      ‖winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T))‖ ≤
        C * ∫ v in Set.Ioc 0 (a + T), Real.exp (-c * (a - v)) * ‖zr v‖ := by
  obtain ⟨C, c, hC, hc, hF⟩ := HRS.MC.E213U3.winJ_far_proof hE T hT
  refine ⟨C, c, hC, hc, fun a ha zr hzm hzi => ?_⟩
  have hb : 0 ≤ a + T + 1 := by linarith
  have hmin : min (a + T + 1) (a + T) = a + T := min_eq_right (by linarith)
  have hint : IntegrableOn (fun v => Real.exp (-c * (a - v)) * ‖zr v‖)
      (Set.Ioc 0 (min (a + T + 1) (a + T))) := by rw [hmin]; exact hzi
  obtain ⟨⟨J, hJ⟩, hn⟩ := hF a ha (a + T + 1) hb zr hzm hint 0 (a + T) le_rfl (by linarith) le_rfl
  have hJ' : IsJValue (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + T)
      (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T)) J :=
    HRS.MC.E213U3.u3_IsJValue_congr _ _ m (a + T) measurableSet_Ioc
      (fun u hu _ => m_farCoef_eq_on (fun v => NegSobolev.embed m (zr v)) u hu) hJ
  refine ⟨⟨J, hJ'⟩, ?_⟩
  have heq : winJ (regime S β₀ hE) m T a ha (farCoef (a + T + 1) (fun v => NegSobolev.embed m (zr v)))
        (Set.Ioc 0 (a + T)) =
      winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc 0 (a + T)) := by
    unfold winJ
    rw [HRS.MC.E213U2.e213u2_jTensor_eq _ m (a + T) _ _ J hJ,
      HRS.MC.E213U2.e213u2_jTensor_eq _ m (a + T) _ _ J hJ']
  rw [heq, m_Ioc_inter_Iio] at hn
  exact hn

end HRS.MC.E214M
end
