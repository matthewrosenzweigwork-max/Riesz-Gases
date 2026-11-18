import HRS.MC.E214N5

/-!
# E214N6: the window covariance tensor at `a + h` against the shifted one at `a`

`‖𝒥_{a+h,η}((0,a+h+T]) - 𝒥_{a,η(h+·)}((0,a+T])‖ ≤ C ∫_{(0,a+h+T] ∩ (-∞,h)} e^{-c(a+h-v)} ‖η_v‖ dv`
(for a continuous bounded coefficient): the near part is identified through the transfer lemma `e213u2_transfer` (with the
shifted regime equal to the regime, by stationarity of the density), the far part is `winJ_far`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214N

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final

variable {d : ℕ}

section JShift

variable {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m)

theorem winRestr_comp_shiftOp {a h T : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (hG : 0 ≤ a + T)
    (hHG : a + h + T ≤ h + (a + T)) :
    (winRestr (d := d) (m := m) (T := T) (a + h) (add_nonneg ha hh)).comp
      (HRS.MC.E213U2.e213u2_shiftOp m h (a + T) (a + h + T) hG hHG) = winRestr a ha := by
  refine ContinuousLinearMap.ext (fun w => e213o_ext (fun t => ?_))
  rw [ContinuousLinearMap.comp_apply, winRestr_at', HRS.MC.E213U2.e213u2_shiftOp_at', winRestr_at']
  congr 1
  apply Subtype.ext
  show max ((a + h + (t : ℝ)) - h) 0 = a + (t : ℝ)
  rw [show a + h + (t : ℝ) - h = a + (t : ℝ) by ring]
  exact max_eq_left (by have := t.2.1; linarith)

/-- Near-part identity of the covariance tensor (time-homogeneity). -/
theorem winJ_near_shift (hρ : ∀ t t', (regime S β₀ hE).ρ t = (regime S β₀ hE).ρ t') {a h T : ℝ} (hT : 0 < T)
    (ha : 0 ≤ a) (hh : 0 ≤ h) (zr : ℝ → NegSobolev d (rLvl d)) (hcont : Continuous zr) (M : ℝ)
    (hM : ∀ v, ‖zr v‖ ≤ M) :
    winJ (regime S β₀ hE) m T (a + h) (add_nonneg ha hh) (nearCoef h (fun v => NegSobolev.embed m (zr v)))
        (Set.Ioc 0 (a + h + T)) =
      winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (zr (h + v))) (Set.Ioc 0 (a + T)) := by
  classical
  set R := regime S β₀ hE with hR
  have hG : 0 < a + T := by linarith
  have hHG : a + h + T ≤ h + (a + T) := by linarith
  obtain ⟨K₁, K₂, c, -, -, -, hbd⟩ := HRS.MC.E213U11.u11_winJ_bound (S := S) (β₀ := β₀) hE T hT
  have hz'cont : Continuous (fun v => zr (h + v)) := hcont.comp (continuous_const.add continuous_id)
  obtain ⟨⟨J₀, hJ₀⟩, -⟩ := hbd a ha (fun v => zr (h + v))
    (HRS.MC.E213U11.u11_measurable_nearCoef_of_continuous hz'cont) M M (fun v _ => hM _) (fun v _ => hM _)
  have hJb : IsJValue R.D (fun t => R.ρ (h + t)) m (a + T)
      (fun w => NegSobolev.embed m (HRS.MC.E213U2.e213u2_cut h h (a + h + T) zr w))
      (Set.Ioc (max (h - h) 0) (max (a + h + T - h) 0)) J₀ := by
    have hfun : (fun t => R.ρ (h + t)) = R.ρ := funext fun t => hρ _ _
    rw [hfun, sub_self, max_self, show a + h + T - h = a + T by ring, max_eq_left hG.le]
    refine HRS.MC.E213U3.u3_IsJValue_congr R.D R.ρ m (a + T) measurableSet_Ioc (fun u hu hu0 => ?_) hJ₀
    have : HRS.MC.E213U2.e213u2_cut h h (a + h + T) zr u = zr (h + u) := by
      unfold HRS.MC.E213U2.e213u2_cut
      rw [if_pos ⟨⟨by linarith [hu.1], by linarith [hu.2]⟩, hu.1⟩]
    show NegSobolev.embed m (zr (h + u)) = NegSobolev.embed m (HRS.MC.E213U2.e213u2_cut h h (a + h + T) zr u)
    rw [this]
  have htr := HRS.MC.E213U2.e213u2_transfer R m hh hG hHG zr h (a + h + T) J₀ hJb
  set P := HRS.MC.E213U2.e213u2_shiftOp (d := d) m h (a + T) (a + h + T) hG.le hHG with hP
  have hJn : IsJValue R.D R.ρ m (a + h + T) (nearCoef h (fun v => NegSobolev.embed m (zr v)))
      (Set.Ioc 0 (a + h + T)) (tensorPow' 2 P J₀) := by
    refine HRS.MC.E213U11.u11_isJValue_enlarge R.D R.ρ m (a + h + T) (I' := Set.Ioc h (a + h + T))
      (Set.Ioc_subset_Ioc_left hh) measurableSet_Ioc measurableSet_Ioc ?_ htr
    have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ h := by
      have := (Set.countable_singleton h).ae_notMem (volume : Measure ℝ)
      filter_upwards [this] with u hu
      simpa using hu
    filter_upwards [hne] with u hu hmem _
    have hle : u ≤ h := by
      by_contra hcon
      exact hmem.2 ⟨not_le.1 hcon, hmem.1.2⟩
    unfold nearCoef
    rw [if_neg (not_le.2 (lt_of_le_of_ne hle hu))]
  have hjT : jTensor R.D R.ρ m (a + h + T) (nearCoef h (fun v => NegSobolev.embed m (zr v)))
      (Set.Ioc 0 (a + h + T)) = tensorPow' 2 P J₀ :=
    HRS.MC.E213U2.e213u2_jTensor_eq R m _ _ _ _ hJn
  have hjT0 : jTensor R.D R.ρ m (a + T) (fun v => NegSobolev.embed m (zr (h + v))) (Set.Ioc 0 (a + T)) = J₀ :=
    HRS.MC.E213U2.e213u2_jTensor_eq R m _ _ _ _ hJ₀
  unfold winJ
  rw [hjT, hjT0, ← tensorPow'_comp, winRestr_comp_shiftOp ha hh hG.le hHG]

/-- The shifted covariance tensor is close to the original one. -/
theorem winJ_shift_bound (hρ : ∀ t t', (regime S β₀ hE).ρ t = (regime S β₀ hE).ρ t') (T : ℝ) (hT : 0 < T) :
    ∃ Cf c : ℝ, 0 < Cf ∧ 0 < c ∧ ∀ {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (zr : ℝ → NegSobolev d (rLvl d)),
      Continuous zr → ∀ M : ℝ, (∀ v, ‖zr v‖ ≤ M) →
      ‖winJ (regime S β₀ hE) m T (a + h) (add_nonneg ha hh) (fun v => NegSobolev.embed m (zr v))
            (Set.Ioc 0 (a + h + T)) -
          winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (zr (h + v))) (Set.Ioc 0 (a + T))‖ ≤
        Cf * ∫ v in Set.Ioc 0 (a + h + T) ∩ Set.Iio h, Real.exp (-c * (a + h - v)) * ‖zr v‖ := by
  obtain ⟨Cf, c, hCf, hc, hfar⟩ := HRS.MC.E213U3.winJ_far_proof hE T hT
  refine ⟨Cf, c, hCf, hc, fun {a h} ha hh zr hcont M hM => ?_⟩
  have hrm := rLvl_le hE
  have ha' : 0 ≤ a + h := add_nonneg ha hh
  have hH : (0 : ℝ) ≤ a + h + T := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hzm : Measurable (nearCoef 0 zr) := HRS.MC.E213U11.u11_measurable_nearCoef_of_continuous hcont
  have hm1 : Measurable (nearCoef 0 (nearCoef h zr)) := HRS.MC.E213U11.u11_measurable_nearCoef_near hzm hh
  have hm2 : Measurable (nearCoef 0 (farCoef h zr)) := HRS.MC.E213U11.u11_measurable_nearCoef_far hzm h
  have hb1 : ∀ v ∈ Set.Icc (0 : ℝ) (a + h + T), ‖nearCoef h zr v‖ ≤ M := fun v _ => by
    unfold nearCoef; split_ifs
    · exact hM v
    · rw [norm_zero]; exact hM0
  have hb2 : ∀ v ∈ Set.Icc (0 : ℝ) (a + h + T), ‖farCoef h zr v‖ ≤ M := fun v _ => by
    unfold farCoef; split_ifs
    · exact hM v
    · rw [norm_zero]; exact hM0
  have hsplit : (fun v => NegSobolev.embed m (zr v)) =
      fun v => NegSobolev.embed m (nearCoef h zr v + farCoef h zr v) := by
    funext v
    have := congrFun (nearCoef_add_farCoef h zr) v
    rw [this]
  have hadd := HRS.MC.E213U2.winJ_add_proof hE T hT (a + h) ha' (nearCoef h zr) (farCoef h zr) hm1 hm2 M M hb1 hb2
    0 (a + h + T) le_rfl hH le_rfl
  have hnear := winJ_near_shift hE hρ hT ha hh zr hcont M hM
  rw [← HRS.MC.E213U11.u11_nearCoef_embed hrm] at hadd
  rw [hsplit, hadd, hnear,
    show ∀ x y : TensorDual (PathSpace d m T) 2, x + y - x = y from fun x y => by abel,
    ← HRS.MC.E213U11.u11_farCoef_embed hrm]
  have hgc : Continuous fun v : ℝ => Real.exp (-c * (a + h - v)) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hint : IntegrableOn (fun v => Real.exp (-c * (a + h - v)) * ‖zr v‖) (Set.Ioc 0 (min h (a + h + T))) :=
    (hgc.mul hcont.norm).integrableOn_Ioc
  exact (hfar (a + h) ha' h hh zr hzm hint 0 (a + h + T) le_rfl hH le_rfl).2

end JShift

end HRS.MC.E214N

end
