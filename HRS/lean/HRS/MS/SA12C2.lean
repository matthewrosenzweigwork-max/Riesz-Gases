import HRS.MS.SA12C1
import HRS.MS.SA16PForce1

/-!
# S.A.12(c), packet E7.02: uniform `L²(Q_L)` bound of a periodic density with periodic decay

`sa12c_density_l2`: if every point has a lattice point `Lk` with `⟨x - Lk⟩^{d+3} |μ(x)| ≤ Λ` then
`∫_{Q_L} μ² ≤ C₀ Λ²` with `C₀` depending only on `d` (independent of `L`).  Uses `|x| ≤ |x - Lk|` on the centred cube.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

/-- on the centred cube the origin is a nearest lattice point -/
theorem sa12c_nearest {L : ℝ} (hL : 0 < L) {x : Euc d} (hx : x ∈ centeredBox d L) (k : Fin d → ℤ) :
    ‖x‖ ≤ ‖x - L • latticePt k‖ := by
  have hcoord : ∀ i, |x i| ≤ |(x - L • latticePt k) i| := by
    intro i
    have h1 := hx i
    have hk : (x - L • latticePt k) i = x i - L * (k i : ℝ) := by simp [latticePt]
    rw [hk]
    rcases eq_or_ne (k i) 0 with h0 | h0
    · simp [h0]
    · have hk1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
        have : (1 : ℤ) ≤ |k i| := Int.one_le_abs h0
        exact_mod_cast this
      have hxi : |x i| ≤ L / 2 := abs_le.2 ⟨h1.1, h1.2.le⟩
      calc |x i| ≤ L / 2 := hxi
        _ ≤ |L * (k i : ℝ)| - |x i| := by
          have : L ≤ |L * (k i : ℝ)| := by
            rw [abs_mul, abs_of_pos hL]; nlinarith
          linarith
        _ ≤ |x i - L * (k i : ℝ)| := by
          have := abs_sub_abs_le_abs_sub (L * (k i : ℝ)) (x i)
          rw [abs_sub_comm] at this
          linarith
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  simpa [sq_abs] using sq_le_sq' (by linarith [abs_nonneg (x i), hcoord i, abs_nonneg ((x - L • latticePt k) i)]) (hcoord i)

/-- the pointwise decay bound `μ(x)² ≤ Λ² 2^{d+3} (1+|x|)^{-(d+3)}` on the centred cube -/
theorem sa12c_density_pt {L : ℝ} (hL : 0 < L) {μ : Euc d → ℝ} {Λ : ℝ}
    (hdec : ∀ x : Euc d, ∃ k : Fin d → ℤ, jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * |μ x| ≤ Λ)
    {x : Euc d} (hx : x ∈ centeredBox d L) :
    μ x ^ 2 ≤ Λ ^ 2 * (2 ^ (d + 3) * HRS.Whole.AppendixA.Phase2SA16P.sa16p_w d x) := by
  obtain ⟨k, hk⟩ := hdec x
  have hjb : jbracket x ≤ jbracket (x - L • latticePt k) := by
    unfold jbracket
    refine Real.sqrt_le_sqrt ?_
    have := sa12c_nearest hL hx k
    nlinarith [norm_nonneg x]
  have hcast : ((d : ℝ) + 3) = ((d + 3 : ℕ) : ℝ) := by push_cast; ring
  have hj0 : 0 < jbracket x := by unfold jbracket; positivity
  set p : ℝ := jbracket x ^ (d + 3) with hp
  have hp0 : 0 < p := by positivity
  have h1 : p * |μ x| ≤ Λ := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)) hk
    rw [hcast, Real.rpow_natCast]
    exact pow_le_pow_left₀ hj0.le hjb _
  have hΛ : 0 ≤ Λ := le_trans (by positivity) h1
  have h2 : μ x ^ 2 * p ^ 2 ≤ Λ ^ 2 := by
    have : (p * |μ x|) ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    rw [mul_pow, sq_abs] at this
    linarith
  have hp2 : p ^ 2 = (1 + ‖x‖ ^ 2) ^ (d + 3) := by
    rw [hp, ← pow_mul, mul_comm, pow_mul]
    congr 1
    unfold jbracket
    rw [Real.sq_sqrt (by positivity)]
  have hq : (1 + ‖x‖) ^ (d + 3) ≤ 2 ^ (d + 3) * p ^ 2 := by
    rw [hp2, ← mul_pow]
    have h3 : (1 + ‖x‖) ≤ 2 * (1 + ‖x‖ ^ 2) := by nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1)]
    have h4 : (1 + ‖x‖) ^ (d + 3) ≤ (2 * (1 + ‖x‖ ^ 2)) ^ (d + 3) := pow_le_pow_left₀ (by positivity) h3 _
    exact h4
  have hw : HRS.Whole.AppendixA.Phase2SA16P.sa16p_w d x = ((1 + ‖x‖) ^ (d + 3))⁻¹ := by
    unfold HRS.Whole.AppendixA.Phase2SA16P.sa16p_w
    rw [hcast, Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [hw]
  have hpos : 0 < (1 + ‖x‖) ^ (d + 3) := by positivity
  rw [← div_eq_mul_inv, mul_div_assoc', le_div_iff₀ hpos]
  calc μ x ^ 2 * (1 + ‖x‖) ^ (d + 3) ≤ μ x ^ 2 * (2 ^ (d + 3) * p ^ 2) :=
        mul_le_mul_of_nonneg_left hq (sq_nonneg _)
    _ = 2 ^ (d + 3) * (μ x ^ 2 * p ^ 2) := by ring
    _ ≤ 2 ^ (d + 3) * Λ ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Λ ^ 2 * 2 ^ (d + 3) := by ring

theorem sa12c_density_l2 (d : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {L : ℝ}, 0 < L → ∀ {μ : Euc d → ℝ} {Λ : ℝ}, Continuous μ →
      (∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x) →
      (∀ x : Euc d, ∃ k : Fin d → ℤ, jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * |μ x| ≤ Λ) →
      ∫ x in periodBox d L, μ x ^ 2 ≤ C₀ * Λ ^ 2 := by
  refine ⟨2 ^ (d + 3) * ∫ y, HRS.Whole.AppendixA.Phase2SA16P.sa16p_w d y, ?_, fun {L} hL {μ} {Λ} hc hper hdec => ?_⟩
  · exact mul_nonneg (by positivity) (integral_nonneg fun y => (HRS.Whole.AppendixA.Phase2SA16P.sa16p_w_pos y).le)
  rw [← sa12v_centered_eq L hL (Φ := fun x => μ x ^ 2) (fun x k => by simp [hper x k])]
  have hwi := HRS.Whole.AppendixA.Phase2SA16P.sa16p_w_integrable (d := d)
  have hcm : MeasurableSet (centeredBox d L) := sa12v_centered_meas L
  calc ∫ x in centeredBox d L, μ x ^ 2 ≤ ∫ x in centeredBox d L, Λ ^ 2 * (2 ^ (d + 3) *
        HRS.Whole.AppendixA.Phase2SA16P.sa16p_w d x) := by
        have hdom : IntegrableOn (fun x => Λ ^ 2 * (2 ^ (d + 3) *
            HRS.Whole.AppendixA.Phase2SA16P.sa16p_w d x)) (centeredBox d L) :=
          ((hwi.const_mul (2 ^ (d + 3))).const_mul (Λ ^ 2)).integrableOn
        refine setIntegral_mono_on ?_ hdom hcm (fun x hx => sa12c_density_pt hL hdec hx)
        refine Integrable.mono' hdom (hc.pow 2).aestronglyMeasurable
          ((ae_restrict_iff' hcm).2 (Eventually.of_forall fun x hx => ?_))
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sa12c_density_pt hL hdec hx
    _ ≤ ∫ x, Λ ^ 2 * (2 ^ (d + 3) * HRS.Whole.AppendixA.Phase2SA16P.sa16p_w d x) :=
        setIntegral_le_integral ((hwi.const_mul (2 ^ (d + 3))).const_mul (Λ ^ 2))
          (Eventually.of_forall fun x => by
            have := HRS.Whole.AppendixA.Phase2SA16P.sa16p_w_pos (d := d) x
            positivity)
    _ = 2 ^ (d + 3) * (∫ y, HRS.Whole.AppendixA.Phase2SA16P.sa16p_w d y) * Λ ^ 2 := by
        rw [integral_const_mul, integral_const_mul]; ring

end HRS.MH.AdjointRd.Phase2SA12C

end
