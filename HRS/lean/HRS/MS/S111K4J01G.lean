import HRS.MS.S111K4J01F

/-!
# S11.1 / J01 piece: linearity and norm bound of the drift interval map in the coefficient path (S11K4)
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
theorem Dq_lin {q q' q'' : TimeCoeff (u + T)} {c : ℝ}
    (hlin : ∀ᵐ v ∂(volume.restrict (Set.Icc (0 : ℝ) (u + T))),
      (q'' : ℝ → Coeff) v = (q : ℝ → Coeff) v + c • (q' : ℝ → Coeff) v)
    {a b' : ℝ} (ha : 0 ≤ a) (hab : a ≤ b') (hb : b' ≤ u + T) :
    Dq E hdata q'' a b' = Dq E hdata q a b' + c • Dq E hdata q' a b' := by
  refine ContinuousMap.ext fun τ => ?_
  show OscPath.at' (Dq E hdata q'' a b') τ =
    OscPath.at' (Dq E hdata q a b') τ + c • OscPath.at' (Dq E hdata q' a b') τ
  rw [Dq_at E hdata ha hab hb, Dq_at E hdata ha hab hb, Dq_at E hdata ha hab hb]
  unfold s111k2_Dfun
  have hi1 := s111k2_W_integrable (hdata q) τ.2 ha hab hb
  have hi2 : IntegrableOn (fun v => c • s111k2_W C (wholeSpaceIndex d : ℝ) (zq E q') u v τ)
      (Set.Ioc a b') := (s111k2_W_integrable (hdata q') τ.2 ha hab hb).smul c
  rw [integral_congr_ae (W_lin E hdata hlin ha hb τ), integral_add hi1 hi2, integral_smul]

theorem Dq_enorm_le (q : TimeCoeff (u + T)) {a b' : ℝ} (ha : 0 ≤ a) (hab : a ≤ b') (hb : b' ≤ u + T)
    (hc0 : 0 < c0) :
    ‖Dq E hdata q a b'‖ₑ ≤ ENNReal.ofReal (s111k2_Kdrift d r Pw S) *
      ∫⁻ v in Set.Ioc a b', ENNReal.ofReal (s111k2_age c0 u v) * ‖(q : ℝ → Coeff) v‖ₑ := by
  have hsub : Set.Ioc a b' ⊆ Set.Icc (0 : ℝ) (u + T) := fun v hv => ⟨ha.trans hv.1.le, hv.2.trans hb⟩
  have hint : ∫⁻ v in Set.Icc (0 : ℝ) (u + T), ‖(q : ℝ → Coeff) v‖ₑ < ⊤ :=
    (Lp.memLp q |>.integrable le_rfl).2
  have hPhi : ∀ v, s111k2_Phi c0 u r Pw (zq E q) v ≤
      ENNReal.ofReal (s111k2_age c0 u v) * ‖(q : ℝ → Coeff) v‖ₑ := fun v => by
    unfold s111k2_Phi
    refine mul_le_mul' le_rfl ((dualNormE_coefficientField_le E (qr E q) v).trans ?_)
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (PM_norm_le E _)
  have hle : ∫⁻ v in Set.Ioc a b', ENNReal.ofReal (s111k2_age c0 u v) * ‖(q : ℝ → Coeff) v‖ₑ ≤
      ∫⁻ v in Set.Icc (0 : ℝ) (u + T), ‖(q : ℝ → Coeff) v‖ₑ := by
    refine (lintegral_mono_set hsub).trans' ?_
    refine lintegral_mono fun v => ?_
    calc ENNReal.ofReal (s111k2_age c0 u v) * ‖(q : ℝ → Coeff) v‖ₑ ≤ 1 * ‖(q : ℝ → Coeff) v‖ₑ :=
          mul_le_mul' (by simpa using ENNReal.ofReal_le_ofReal (s111k2_age_le_one hc0 u v)) le_rfl
      _ = _ := one_mul _
  have hfin : ENNReal.ofReal (s111k2_Kdrift d r Pw S) *
      ∫⁻ v in Set.Ioc a b', ENNReal.ofReal (s111k2_age c0 u v) * ‖(q : ℝ → Coeff) v‖ₑ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top hint.ne hle)
  refine s111k2_enorm_path_le hfin fun τ => ?_
  show ‖OscPath.at' (Dq E hdata q a b') τ‖ₑ ≤ _
  rw [Dq_at E hdata ha hab hb]
  refine (s111k2_Dfun_bound (hdata q) τ.2 ha hab hb).trans ?_
  exact mul_le_mul' le_rfl (lintegral_mono hPhi)

end drift

end HRS.MS.S111K4J01
