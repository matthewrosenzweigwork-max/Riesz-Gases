import HRS.MS.UniqE3d

/-!
# E3 of `UniqPlan.md`, part 5: commutator integrals (T, remainder)

* `e3_real_sq_le`: real `L²` mass from a `lintegral` mass bound.
* `e3_ball_of_unit`: from unit balls to balls of radius `r`.
* `e3_comm_integral_bound`: `|∫ u [η_ε*, a] F| ≤ ε L (½ ∫_S (η_ε*|u|)² + ½ ∫_S F²)` for `a` `L`-Lipschitz,
  `F ∈ C` vanishing off the compact set `S`, `LocMass u`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3

variable {d : ℕ}

theorem e3_real_sq_le {s : Set (Euc d)} {g : Euc d → ℝ} (hg : Continuous g) {M : ℝ} (hM : 0 ≤ M)
    (h : ∫⁻ x in s, ‖g x‖ₑ ^ 2 ≤ ENNReal.ofReal M) : ∫ x in s, g x ^ 2 ≤ M := by
  have h1 : ∫ x in s, g x ^ 2 = (∫⁻ x in s, ENNReal.ofReal (g x ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
      (hg.pow 2).aestronglyMeasurable
  rw [h1]
  refine ENNReal.toReal_le_of_le_ofReal hM ?_
  simpa only [enorm_sq_eq] using h

/-- From unit balls to balls of radius `r`. -/
theorem e3_ball_of_unit (d : ℕ) (r : ℝ) :
    ∃ N : ℕ, ∀ (f : Euc d → ℝ≥0∞) (M : ℝ≥0∞), (∀ c : Euc d, ∫⁻ x in ball c 1, f x ≤ M) →
      ∀ c : Euc d, ∫⁻ x in ball c r, f x ≤ (N : ℝ≥0∞) * M := by
  obtain ⟨s, hs⟩ := exists_unit_cover d r
  refine ⟨s.card, fun f M hf c => ?_⟩
  calc ∫⁻ x in ball c r, f x ≤ ∫⁻ x in ⋃ y ∈ s, ball (c + y) 1, f x := lintegral_mono_set (hs c)
    _ ≤ ∑ y ∈ s, ∫⁻ x in ball (c + y) 1, f x := by
        rw [show (⋃ y ∈ s, ball (c + y) 1) = ⋃ y : s, ball (c + (y : Euc d)) 1 by ext; simp]
        refine (lintegral_iUnion_le _ _).trans ?_
        rw [tsum_fintype]
        exact (Finset.sum_coe_sort s fun y => ∫⁻ x in ball (c + y) 1, f x).le
    _ ≤ ∑ y ∈ s, M := Finset.sum_le_sum fun y _ => hf _
    _ = _ := by simp

theorem e3_nat_mul_ofReal (N : ℕ) {M : ℝ} :
    (N : ℝ≥0∞) * ENNReal.ofReal M = ENNReal.ofReal (N * M) := by
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg N), ENNReal.ofReal_natCast]

theorem e3_comm_integral_bound {ε : ℝ} (hε : 0 < ε) {B : ℝ} {u : Euc d → ℝ} (hu : LocMass B u)
    {L : ℝ} (hL : 0 ≤ L) {a F : Euc d → ℝ} (ha : ∀ x y : Euc d, |a x - a y| ≤ L * ‖x - y‖)
    (hF : Continuous F) {S : Set (Euc d)} (hS : IsCompact S) (hFS : ∀ x, x ∉ S → F x = 0) :
    |∫ x, u x * comm d ε a F x| ≤
      ε * L * ((1 / 2) * (∫ x in S, moll d ε (fun y => ‖u y‖) x ^ 2) +
        (1 / 2) * ∫ x in S, F x ^ 2) := by
  have hFc : HasCompactSupport F := e3_hasCompactSupport_of_zero hS hFS
  have hFli : LocallyIntegrable F volume := hF.locallyIntegrable
  have hac : Continuous a := m3_continuous_of_lip hL ha
  have hG : LocMass B (fun y => ‖u y‖) := ⟨hu.1.norm, fun c' => by simpa only [enorm_norm] using hu.2 c'⟩
  have hnF : Continuous (fun x => ‖F x‖) := hF.norm
  have hnFc : HasCompactSupport (fun x => ‖F x‖) := hFc.norm
  have hmF : Continuous (moll d ε F) := e3_moll_continuous hε hFli
  have haF : Continuous (fun x => a x * F x) := hac.mul hF
  have hcomm_c : Continuous (comm d ε a F) :=
    (e3_moll_continuous hε haF.locallyIntegrable).sub (hac.mul hmF)
  have hcomm_cs : HasCompactSupport (comm d ε a F) :=
    (e3_moll_hasCompactSupport hε (hFc.mul_left (f := a))).sub
      ((e3_moll_hasCompactSupport hε hFc).mul_left (f := a))
  have hnorm_mF : Continuous (moll d ε (fun x => ‖F x‖)) :=
    e3_moll_continuous hε hnF.locallyIntegrable
  have hint : Integrable (fun x => (ε * L) * (‖u x‖ * moll d ε (fun y => ‖F y‖) x)) volume :=
    (e3_integrable_mul hG.locallyIntegrable hnorm_mF (e3_moll_hasCompactSupport hε hnFc)).const_mul _
  rw [← Real.norm_eq_abs]
  have step1 : ‖∫ x, u x * comm d ε a F x‖ ≤
      ∫ x, (ε * L) * (‖u x‖ * moll d ε (fun y => ‖F y‖) x) := by
    refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs (comm d ε a F x)]
    have h1 := m3_comm_abs_le hε hL ha hFli x
    calc ‖u x‖ * |comm d ε a F x| ≤ ‖u x‖ * (ε * L * moll d ε (fun y => ‖F y‖) x) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = _ := by ring
  have step2 : ∫ x, (ε * L) * (‖u x‖ * moll d ε (fun y => ‖F y‖) x) =
      (ε * L) * ∫ x, moll d ε (fun y => ‖u y‖) x * ‖F x‖ := by
    rw [integral_const_mul, e3_integral_mul_moll hε hG hnF hnFc]
  refine step1.trans ?_
  rw [step2]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hε.le hL)
  -- bound ∫ m ‖F‖ by the half-squares over S
  have hm : Continuous (moll d ε (fun y => ‖u y‖)) := e3_moll_continuous hε hG.locallyIntegrable
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have e1 : ∫ x, moll d ε (fun y => ‖u y‖) x * ‖F x‖ =
      ∫ x in S, moll d ε (fun y => ‖u y‖) x * ‖F x‖ := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    simp [hFS x hx]
  have i1 : IntegrableOn (fun x => moll d ε (fun y => ‖u y‖) x ^ 2) S volume :=
    (hm.pow 2).continuousOn.integrableOn_compact hS
  have i2 : IntegrableOn (fun x => F x ^ 2) S volume :=
    (hF.pow 2).continuousOn.integrableOn_compact hS
  have i3 : IntegrableOn (fun x => moll d ε (fun y => ‖u y‖) x * ‖F x‖) S volume :=
    (hm.mul hnF).continuousOn.integrableOn_compact hS
  rw [e1]
  calc ∫ x in S, moll d ε (fun y => ‖u y‖) x * ‖F x‖
      ≤ ∫ x in S, ((1 / 2) * moll d ε (fun y => ‖u y‖) x ^ 2 + (1 / 2) * F x ^ 2) := by
        refine setIntegral_mono_on i3 ((i1.const_mul _).add (i2.const_mul _)) hSm fun x _ => ?_
        have : ‖F x‖ ^ 2 = F x ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
        nlinarith [sq_nonneg (moll d ε (fun y => ‖u y‖) x - ‖F x‖)]
    _ = _ := by
        rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]

end HRS.MS.UniqE3
