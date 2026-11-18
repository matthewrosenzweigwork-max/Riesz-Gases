import HRS.MS.UniqN0c

/-!
# N3b, part B: weighted mass of `F²` from the unit-ball mass `LocMass A F`

* `n3b_int_le`: conversion from a bound on `∫⁻ ofReal g` to integrability and a bound on `∫ g`.
* `n3b_decay_mass`: `∫ w F² ≤ K Cw A²` when `0 ≤ w ≤ Cw (1+‖x‖)^{-κ}`, `κ > d` (`K = K(d,κ)`).
* `n3b_ball_mass`: `∫ w F² ≤ N A²` when `0 ≤ w ≤ 1` is supported in `ball a r` (`N = N(d,r)`).
Both are uniform in the centre / the function.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal

namespace HRS.MS.UniqN3b

open HRS.MS.UniqM1 HRS.MS.UniqN0

variable {d : ℕ}

theorem n3b_int_le {g : Euc d → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hgm : AEStronglyMeasurable g volume)
    {K : ℝ} (hK : 0 ≤ K) (h : ∫⁻ x, ENNReal.ofReal (g x) ≤ ENNReal.ofReal K) :
    Integrable g volume ∧ ∫ x, g x ≤ K := by
  have hfin : Integrable g volume := by
    refine ⟨hgm, ?_⟩
    have : ∫⁻ x, ‖g x‖ₑ = ∫⁻ x, ENNReal.ofReal (g x) := by
      refine lintegral_congr fun x => ?_
      rw [Real.enorm_eq_ofReal (hg0 x)]
    rw [HasFiniteIntegral, this]
    exact h.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hfin, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0) hgm]
  calc (∫⁻ x, ENNReal.ofReal (g x)).toReal ≤ (ENNReal.ofReal K).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = K := ENNReal.toReal_ofReal hK

theorem n3b_decay_mass {κ : ℝ} (hκ : (d : ℝ) < κ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ) (F : Euc d → ℝ), 0 ≤ A → Measurable F → LocMass A F →
      ∀ (w : Euc d → ℝ) (Cw : ℝ), 0 ≤ Cw → AEStronglyMeasurable w volume →
      (∀ x, 0 ≤ w x ∧ w x ≤ Cw * (1 + ‖x‖) ^ (-κ)) →
      Integrable (fun x => w x * F x ^ 2) volume ∧ ∫ x, w x * F x ^ 2 ≤ K * Cw * A ^ 2 := by
  have hκ0 : 0 ≤ κ := le_trans (Nat.cast_nonneg d) hκ.le
  set V : ℝ≥0∞ := volume (ball (0 : Euc d) 1) with hV
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos volume (0 : Euc d) one_pos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  have hVr : 0 < V.toReal := ENNReal.toReal_pos hV0 hVt
  set I0 : ℝ := ∫ w : Euc d, (1 + ‖w‖) ^ (-κ) with hI0
  have hI0nn : 0 ≤ I0 := integral_nonneg fun w => by positivity
  refine ⟨V.toReal⁻¹ * 2 ^ κ * I0, by positivity, fun A F hA hFm hF w Cw hCw hwm hw => ?_⟩
  have hL : ∀ c : Euc d, ∫⁻ y in ball c 1, ‖F y ^ 2‖ₑ ≤ ENNReal.ofReal (A ^ 2) := by
    intro c
    have := hF.2 c
    simpa [enorm_pow] using this
  have hcore := n0_decay_core hκ (0 : Euc d) (fun y => F y ^ 2) (hFm.pow_const 2) _ hL
  have hint := n0_decay_integrable hκ (0 : Euc d)
  have hIw : ∫⁻ w : Euc d, ENNReal.ofReal ((1 + ‖w - 0‖) ^ (-κ)) = ENNReal.ofReal I0 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w => by positivity)]
    simp [hI0]
  rw [hIw] at hcore
  have h1 := (ENNReal.mul_le_iff_le_inv hV0 hVt).1 hcore
  have hVinv : V⁻¹ = ENNReal.ofReal V.toReal⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hVr, ENNReal.ofReal_toReal hVt]
  have h2 : ∫⁻ y, ‖F y ^ 2‖ₑ * ENNReal.ofReal ((1 + ‖y - 0‖) ^ (-κ)) ≤
      ENNReal.ofReal (V.toReal⁻¹ * 2 ^ κ * I0 * A ^ 2) := by
    refine h1.trans ?_
    rw [hVinv, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    ring
  have hpt : ∀ x, ENNReal.ofReal (w x * F x ^ 2) ≤
      ENNReal.ofReal Cw * (‖F x ^ 2‖ₑ * ENNReal.ofReal ((1 + ‖x - 0‖) ^ (-κ))) := by
    intro x
    rw [Real.enorm_eq_ofReal (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hCw]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [sub_zero]
    have := (hw x).2
    calc w x * F x ^ 2 ≤ (Cw * (1 + ‖x‖) ^ (-κ)) * F x ^ 2 := by gcongr
      _ = _ := by ring
  have hmain : ∫⁻ x, ENNReal.ofReal (w x * F x ^ 2) ≤
      ENNReal.ofReal (V.toReal⁻¹ * 2 ^ κ * I0 * Cw * A ^ 2) := by
    calc ∫⁻ x, ENNReal.ofReal (w x * F x ^ 2)
        ≤ ∫⁻ x, ENNReal.ofReal Cw * (‖F x ^ 2‖ₑ * ENNReal.ofReal ((1 + ‖x - 0‖) ^ (-κ))) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal Cw * ∫⁻ x, ‖F x ^ 2‖ₑ * ENNReal.ofReal ((1 + ‖x - 0‖) ^ (-κ)) :=
          lintegral_const_mul' _ _ (by simp)
      _ ≤ ENNReal.ofReal Cw * ENNReal.ofReal (V.toReal⁻¹ * 2 ^ κ * I0 * A ^ 2) :=
          mul_le_mul' le_rfl h2
      _ = _ := by
          rw [← ENNReal.ofReal_mul hCw]; congr 1; ring
  refine ⟨?_, ?_⟩
  · refine (n3b_int_le (fun x => mul_nonneg (hw x).1 (sq_nonneg _))
      (hwm.mul (hFm.pow_const 2).aestronglyMeasurable) (by positivity) hmain).1
  · have := (n3b_int_le (fun x => mul_nonneg (hw x).1 (sq_nonneg _))
      (hwm.mul (hFm.pow_const 2).aestronglyMeasurable) (by positivity) hmain).2
    linarith

theorem n3b_ball_mass (d : ℕ) (r : ℝ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ (A : ℝ) (F : Euc d → ℝ), 0 ≤ A → Measurable F → LocMass A F →
      ∀ (a : Euc d) (w : Euc d → ℝ), AEStronglyMeasurable w volume →
      (∀ x, 0 ≤ w x ∧ w x ≤ 1) → (∀ x, x ∉ ball a r → w x = 0) →
      Integrable (fun x => w x * F x ^ 2) volume ∧ ∫ x, w x * F x ^ 2 ≤ N * A ^ 2 := by
  obtain ⟨N, hN⟩ := n0_ball_bound d r
  refine ⟨N, Nat.cast_nonneg N, fun A F hA hFm hF a w hwm hw0 hws => ?_⟩
  have hb := hN (fun y => ‖F y‖ₑ ^ 2) (ENNReal.ofReal (A ^ 2)) (fun c => hF.2 c) a
  have hmain : ∫⁻ x, ENNReal.ofReal (w x * F x ^ 2) ≤ ENNReal.ofReal (N * A ^ 2) := by
    calc ∫⁻ x, ENNReal.ofReal (w x * F x ^ 2)
        ≤ ∫⁻ x, (ball a r).indicator (fun y => ‖F y‖ₑ ^ 2) x := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ ball a r
          · rw [Set.indicator_of_mem hx, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
              sq_abs]
            exact ENNReal.ofReal_le_ofReal (by
              have := (hw0 x)
              nlinarith [sq_nonneg (F x)])
          · rw [Set.indicator_of_notMem hx, hws x hx]; simp
      _ = ∫⁻ x in ball a r, ‖F x‖ₑ ^ 2 := lintegral_indicator measurableSet_ball _
      _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal (A ^ 2) := hb
      _ = _ := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
  have hm := (hwm.mul (hFm.pow_const 2).aestronglyMeasurable)
  have hnn : ∀ x, 0 ≤ w x * F x ^ 2 := fun x => mul_nonneg (hw0 x).1 (sq_nonneg _)
  exact n3b_int_le hnn hm (by positivity) hmain

end HRS.MS.UniqN3b
