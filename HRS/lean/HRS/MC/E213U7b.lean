import HRS.MC.E213U7
import HRS.MC.E213U5b

/-!
# Packet e213u7 (part b): `rs_split_drift_proof`, `rs_split_J_proof`

Relocations of `rs_split_drift`, `rs_split_J` of `HRS.MC.E213Plan`: the cores of `HRS.MC.E213U7` applied to the
regularity of the window heat function (`HRS.MC.E213U5.Ucan_regular_proof`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U7

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

variable {S : PreparedData d} {β₀ m : ℝ}

theorem rs_split_drift_proof (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (w : PathSpace d m (a + T))
    (bq : ℝ → NegSobolev d (rLvl d)) (hbm : Measurable (nearCoef 0 bq))
    (hbi : IntegrableOn (fun v => ‖bq v‖) (Set.Icc 0 (a + T))) (b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    IsRS (a + T)
      (rsSumD (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha w τ)
        (fun u u' => winDrift (regime S β₀ hE) m T a ha (nearCoef b (fun v => NegSobolev.embed m (bq v))) u u'))
      (rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (nearCoef b (fun v => NegSobolev.embed m (bq v)))) ∧
    IsRS (a + T)
      (rsSumD (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha w τ)
        (fun u u' => winDrift (regime S β₀ hE) m T a ha (farCoef b (fun v => NegSobolev.embed m (bq v))) u u'))
      (rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (farCoef b (fun v => NegSobolev.embed m (bq v)))) ∧
    rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (fun v => NegSobolev.embed m (bq v)) =
      rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (nearCoef b (fun v => NegSobolev.embed m (bq v))) +
      rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (farCoef b (fun v => NegSobolev.embed m (bq v))) :=
  e213u7_rs_split_drift_core hE T hT a ha Φ (HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ) w bq hbm hbi b hb hba

theorem rs_split_J_proof (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (w : PathSpace d m (a + T))
    (zq : ℝ → NegSobolev d (rLvl d)) (hzm : Measurable (nearCoef 0 zq)) (M : ℝ) (hM : ∀ v ∈ Set.Icc 0 (a + T), ‖zq v‖ ≤ M)
    (b : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) :
    IsRS (a + T)
      (rsSumJ (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha w τ)
        (fun u u' => winJ (regime S β₀ hE) m T a ha (nearCoef b (fun v => NegSobolev.embed m (zq v))) (Set.Ioc u u')))
      (rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (nearCoef b (fun v => NegSobolev.embed m (zq v)))) ∧
    IsRS (a + T)
      (rsSumJ (Ucan hE T a ha Φ) (fun τ => winPred (regime S β₀ hE) m T a ha w τ)
        (fun u u' => winJ (regime S β₀ hE) m T a ha (farCoef b (fun v => NegSobolev.embed m (zq v))) (Set.Ioc u u')))
      (rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (farCoef b (fun v => NegSobolev.embed m (zq v)))) ∧
    rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (fun v => NegSobolev.embed m (zq v)) =
      rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (nearCoef b (fun v => NegSobolev.embed m (zq v))) +
      rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) w (farCoef b (fun v => NegSobolev.embed m (zq v))) :=
  e213u7_rs_split_J_core hE T hT a ha Φ (HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ) w zq hzm M hM b hb hba

end HRS.MC.E213U7

end
