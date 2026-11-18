import HRS.MS.S111K4J01G

/-!
# S11.1 / J01 piece: continuity, additivity in the interval and coordinates of the drift path of an `L¹` coefficient path (S11K4)
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

section drift
variable {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw) {C : WholeCoeff d} {c0 S T u : ℝ}
  {b : MultiIndex d → ℝ}
  (hdata : ∀ q : TimeCoeff (u + T),
    S111k2Drift C (wholeSpaceIndex d : ℝ) c0 r b S T u Pw (zq E q))

include hdata in
theorem Dq_interval_add (q : TimeCoeff (u + T)) {a b' c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b') (hbc : b' ≤ c)
    (hc : c ≤ u + T) : Dq E hdata q a c = Dq E hdata q a b' + Dq E hdata q b' c := by
  refine ContinuousMap.ext fun τ => ?_
  show OscPath.at' (Dq E hdata q a c) τ =
    OscPath.at' (Dq E hdata q a b') τ + OscPath.at' (Dq E hdata q b' c) τ
  rw [Dq_at E hdata ha (hab.trans hbc) hc, Dq_at E hdata ha hab (hbc.trans hc),
    Dq_at E hdata (ha.trans hab) hbc hc]
  exact s111k2_Dfun_add (hdata q) τ.2 ha hab hbc hc

theorem Dq_self (q : TimeCoeff (u + T)) {a : ℝ} (ha : 0 ≤ a) (hb : a ≤ u + T) :
    Dq E hdata q a a = 0 := by
  refine ContinuousMap.ext fun τ => ?_
  show OscPath.at' (Dq E hdata q a a) τ = 0
  rw [Dq_at E hdata ha le_rfl hb]
  exact s111k2_Dfun_self _ _ _ _ _ _

theorem Dq_zero (hc0 : 0 < c0) {a b' : ℝ} (ha : 0 ≤ a) (hab : a ≤ b') (hb : b' ≤ u + T) :
    Dq E hdata (0 : TimeCoeff (u + T)) a b' = 0 := by
  have h := Dq_enorm_le E hdata (0 : TimeCoeff (u + T)) ha hab hb hc0
  have h0 : ∫⁻ v in Set.Ioc a b', ENNReal.ofReal (s111k2_age c0 u v) *
      ‖((0 : TimeCoeff (u + T)) : ℝ → Coeff) v‖ₑ = 0 := by
    have hsub : Set.Ioc a b' ⊆ Set.Icc (0 : ℝ) (u + T) :=
      fun v hv => ⟨ha.trans hv.1.le, hv.2.trans hb⟩
    have hae : ∀ᵐ v ∂(volume.restrict (Set.Ioc a b')), ((0 : TimeCoeff (u + T)) : ℝ → Coeff) v = 0 :=
      ae_restrict_of_ae_restrict_of_subset hsub (Lp.coeFn_zero _ _ _)
    rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞)) (hae.mono fun v hv => by rw [hv]; simp)]
    simp
  rw [h0, mul_zero, nonpos_iff_eq_zero] at h
  exact enorm_eq_zero.1 h

theorem Dq_cont (hc0 : 0 < c0) (q : TimeCoeff (u + T)) :
    ContinuousOn (fun v => Dq E hdata q 0 v) (Set.Icc (0 : ℝ) (u + T)) := by
  have hint : ∫⁻ v in Set.Icc (0 : ℝ) (u + T), ‖(q : ℝ → Coeff) v‖ₑ < ⊤ :=
    (Lp.memLp q |>.integrable le_rfl).2
  have hfin : ∫⁻ v in Set.Icc (0 : ℝ) (u + T), ENNReal.ofReal (s111k2_Kdrift d r Pw S) *
      (ENNReal.ofReal (s111k2_age c0 u v) * ‖(q : ℝ → Coeff) v‖ₑ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal (s111k2_Kdrift d r Pw S) *
      ∫⁻ v in Set.Icc (0 : ℝ) (u + T), ‖(q : ℝ → Coeff) v‖ₑ) ?_ ?_
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hint.ne
    · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun v => mul_le_mul' le_rfl ?_
      calc ENNReal.ofReal (s111k2_age c0 u v) * ‖(q : ℝ → Coeff) v‖ₑ ≤ 1 * ‖(q : ℝ → Coeff) v‖ₑ :=
            mul_le_mul' (by simpa using ENNReal.ofReal_le_ofReal (s111k2_age_le_one hc0 u v)) le_rfl
        _ = _ := one_mul _
  exact (s111k2_interval_bv (fun a b' => Dq E hdata q a b')
    (fun v => ENNReal.ofReal (s111k2_Kdrift d r Pw S) *
      (ENNReal.ofReal (s111k2_age c0 u v) * ‖(q : ℝ → Coeff) v‖ₑ)) hfin
    (fun a b' c ha hab hbc hc => Dq_interval_add E hdata q ha hab hbc hc)
    (fun a b' ha hab hb => by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact Dq_enorm_le E hdata q ha hab hb hc0)).1

include hdata in
theorem Dq_coordinate (q : TimeCoeff (u + T))
    (hq0 : ∀ᵐ v ∂(volume.restrict (Set.Icc (0 : ℝ) (u + T))),
      inner ℝ ((q : ℝ → Coeff) v) (massVec E) = 0)
    {a b' : ℝ} (ha : 0 ≤ a) (hab : a ≤ b') (hb : b' ≤ u + T) (τ : Set.Icc (0 : ℝ) T)
    {φ : Euc d → ℝ} (hφ : IsR2DualCombo (wholeSpaceIndex d : ℝ) φ) :
    OscDual.eval (OscPath.at' (Dq E hdata q a b') τ) φ =
      ∫ v in Set.Ioc a b' ∩ Set.Icc 0 (u + τ),
        coefficientField E (q : ℝ → Coeff) v (propagatorW C v (u + τ) φ) := by
  rw [Dq_at E hdata ha hab hb, s111k2_Dfun_eval (hdata q) τ.2 ha hab hb hφ]
  have hsub : Set.Ioc a b' ∩ Set.Icc 0 (u + (τ : ℝ)) ⊆ Set.Icc (0 : ℝ) (u + T) := fun v hv =>
    ⟨ha.trans hv.1.1.le, hv.1.2.trans hb⟩
  refine setIntegral_congr_ae (measurableSet_Ioc.inter measurableSet_Icc) ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hq0] with v hv hvS
  unfold zq coefficientField qr
  rw [PM_of_inner_zero E (hv (hsub hvS))]

end drift

end HRS.MS.S111K4J01
