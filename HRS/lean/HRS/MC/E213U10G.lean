import HRS.MC.E213U10F
import HRS.MC.E213U2

/-!
# Packet e213u10, part G: the covariance functional on the path space

`u10_zq b z v = pathAt z (v - b)`; `u10_cJ` is the near covariance coefficient `nearCoef b (embed ∘ zq)`;
`u10_SJ x`, `u10_FJ x` the covariance summand/integral for `x = (w, z) ∈ 𝒳_{r,L} × 𝒳_{r,L}`.
The sharp near bound `‖𝒥(nearCoef b z; (u,u'])‖ ≤ C M |(u,u'] ∩ [b,∞)|` is derived from `winJ_near` by shrinking the interval.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

theorem u10_pathAt_meas {m T : ℝ} (w : PathSpace d m T) : Measurable (fun t => pathAt w t) := by
  by_cases hT : 0 ≤ T
  · have hc : Continuous fun t : ℝ => w.at' (Set.projIcc 0 T hT t) :=
      (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w).continuous.comp continuous_projIcc
    have e : (fun t => pathAt w t) = Set.indicator (Set.Icc 0 T) fun t : ℝ =>
        w.at' (Set.projIcc 0 T hT t) := by
      funext t
      unfold pathAt
      by_cases ht : t ∈ Set.Icc (0 : ℝ) T
      · rw [dif_pos ht, Set.indicator_of_mem ht]
        have : Set.projIcc 0 T hT t = ⟨t, ht⟩ := Set.projIcc_of_mem hT ht
        rw [this]
      · rw [dif_neg ht, Set.indicator_of_notMem ht]
    rw [e]
    exact hc.measurable.indicator measurableSet_Icc
  · have e : (fun t => pathAt w t) = fun _ => (0 : NegSobolev d m) := by
      funext t
      unfold pathAt
      rw [dif_neg (fun h => hT (h.1.trans h.2))]
    rw [e]
    exact measurable_const

theorem u10_winJ_empty (R : Regime d) (m T a : ℝ) (ha : 0 ≤ a) (z : ℝ → NegSobolev d m) :
    winJ R m T a ha z ∅ = 0 := by
  have h0 : IsJValue R.D R.ρ m (a + T) z ∅ 0 := by
    refine ⟨Submodule.zero_mem _, ?_⟩
    intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
    simp
  have := HRS.MC.E213U2.e213u2_jTensor_eq R m (a + T) z ∅ 0 h0
  unfold winJ
  rw [this, map_zero]

/-- The conclusion of `winJ_near` for fixed `a, b` and constant `CJ`. -/
def U10_JNear (hE : EdgeworthHyp S β₀ m) (T a : ℝ) (ha : 0 ≤ a) (b CJ : ℝ) : Prop :=
  ∀ (zr : ℝ → NegSobolev d (rLvl d)), Measurable (nearCoef 0 zr) → ∀ M : ℝ,
    (∀ v ∈ Set.Icc b (a + T), ‖zr v‖ ≤ M) →
    ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ a + T →
      ‖winJ (regime S β₀ hE) m T a ha (nearCoef b (fun v => NegSobolev.embed m (zr v))) (Set.Ioc u u')‖ ≤
        CJ * M * (u' - u)

theorem u10_winJ_near_sharp (hE : EdgeworthHyp S β₀ m) (T a : ℝ) (ha : 0 ≤ a) (b CJ : ℝ) (hb : 0 ≤ b)
    (hCJ0 : 0 ≤ CJ) (hJ : U10_JNear hE T a ha b CJ) (zr : ℝ → NegSobolev d (rLvl d))
    (hzm : Measurable (nearCoef 0 zr)) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ v ∈ Set.Icc b (a + T), ‖zr v‖ ≤ M)
    {u u' : ℝ} (hu : 0 ≤ u) (huu' : u ≤ u') (hu' : u' ≤ a + T) :
    ‖winJ (regime S β₀ hE) m T a ha (nearCoef b (fun v => NegSobolev.embed m (zr v))) (Set.Ioc u u')‖ ≤
      CJ * M * (volume (Set.Ioc u u' ∩ Set.Ici b)).toReal := by
  have hne : ∀ᵐ v : ℝ ∂volume, v ∉ ({b} : Set ℝ) := (Set.countable_singleton b).ae_notMem volume
  have hz0 : ∀ v : ℝ, v < b →
      nearCoef b (fun v => NegSobolev.embed m (zr v)) v = 0 := fun v hv => by simp [nearCoef, not_le.2 hv]
  by_cases hub : u' ≤ b
  · have hshr := u10_winJ_shrink (regime S β₀ hE) m T a ha
      (z := nearCoef b (fun v => NegSobolev.embed m (zr v))) (I := Set.Ioc u u') (I' := ∅) measurableSet_Ioc
      (Set.empty_subset _) (by
        filter_upwards [hne] with v hv hvI _
        have hvb : v ≠ b := fun e => hv (by simp [e])
        exact hz0 v (lt_of_le_of_ne (hvI.2.trans hub) hvb))
    rw [hshr, u10_winJ_empty]
    refine le_trans (le_of_eq ?_) (mul_nonneg (mul_nonneg hCJ0 hM0) ENNReal.toReal_nonneg : (0:ℝ) ≤ _)
    exact ContinuousLinearMap.opNorm_zero
  · have hub' : b < u' := not_le.1 hub
    have hu0 : 0 ≤ max u b := le_max_of_le_left hu
    have hu0' : max u b ≤ u' := max_le huu' hub'.le
    rw [u10_winJ_shrink (regime S β₀ hE) m T a ha (I := Set.Ioc u u') (I' := Set.Ioc (max u b) u') measurableSet_Ioc
      (Set.Ioc_subset_Ioc_left (le_max_left _ _)) ?_]
    · refine (hJ zr hzm M hM _ u' hu0 hu0' hu').trans ?_
      have hvol : u' - max u b ≤ (volume (Set.Ioc u u' ∩ Set.Ici b)).toReal := by
        have h1 : Set.Ioc (max u b) u' ⊆ Set.Ioc u u' ∩ Set.Ici b := fun v hv =>
          ⟨⟨lt_of_le_of_lt (le_max_left _ _) hv.1, hv.2⟩, (le_max_right _ _).trans hv.1.le⟩
        have h2 : volume (Set.Ioc u u' ∩ Set.Ici b) ≠ ⊤ :=
          ne_top_of_le_ne_top (by simp) (measure_mono (Set.inter_subset_left : Set.Ioc u u' ∩ Set.Ici b ⊆ Set.Ioc u u'))
        have h3 := ENNReal.toReal_mono h2 (measure_mono h1)
        rwa [Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 hu0')] at h3
      have : 0 ≤ CJ * M := mul_nonneg hCJ0 hM0
      exact mul_le_mul_of_nonneg_left hvol this
    · filter_upwards [hne] with v hv hvI hnot
      have hvb : v ≠ b := fun e => hv (by simp [e])
      have hle : v ≤ b := by
        by_contra hvb'
        exact hnot ⟨max_lt hvI.1 (not_le.1 hvb'), hvI.2⟩
      exact hz0 v (lt_of_le_of_ne hle hvb)

end HRS.MC.E213U10

end
