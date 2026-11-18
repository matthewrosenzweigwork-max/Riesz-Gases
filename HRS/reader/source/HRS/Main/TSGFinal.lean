import HRS.Main.SpecSW2

/-!
# Proof of the torus gradient clause of Lemma C.6 (packet TSG)

Relocated proof of `HRS.Main.SpecSW2.torus_sqrt_gradient_le`; the statement below is copied verbatim.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.Main

/-- Squared directional derivative bound for `a` with `‖∇²a‖ ≤ L`: `(∂_h a)² ≤ 2 L a ‖h‖²`. -/
theorem tsg_sq_fderiv_le {d : ℕ} {a : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L) (ha : ∀ x, 0 ≤ a x)
    (hC11 : PDE.IsC11 L a) (x h : Euc d) :
    (fderiv ℝ (Torus.lift a) x h) ^ 2 ≤ 2 * L * (Torus.lift a) x * ‖h‖ ^ 2 :=
  HRS.sqrtLip_grad (Torus.lift a) hC11.1 (fun _ => ha _) L hL hC11.2 x h

/-- Pointwise gradient bound: `‖∇√a(x)‖ ≤ √(L/2)` at every point, with `√a` the lift. -/
theorem tsg_norm_fderiv_le {d : ℕ} {a : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L) (ha : ∀ x, 0 ≤ a x)
    (hC11 : PDE.IsC11 L a) (x : Euc d) :
    ‖fderiv ℝ (Torus.lift fun y => Real.sqrt (a y)) x‖ ≤ Real.sqrt (L / 2) := by
  have hCd : ContDiff ℝ 1 (Torus.lift a) := hC11.1
  have hAd : HasFDerivAt (Torus.lift a) (fderiv ℝ (Torus.lift a) x) x :=
    ((hCd.differentiable (by norm_num)) x).hasFDerivAt
  have hnn : 0 ≤ (Torus.lift a) x := ha _
  rcases hnn.eq_or_lt with h0 | hpos
  · -- a(x) = 0: `x` is a global minimum of `√(a ∘ mk)`, so the derivative vanishes
    have hmin : IsLocalMin (fun y => Real.sqrt ((Torus.lift a) y)) x := by
      refine Filter.Eventually.of_forall fun y => ?_
      show Real.sqrt ((Torus.lift a) x) ≤ Real.sqrt ((Torus.lift a) y)
      rw [← h0, Real.sqrt_zero]
      exact Real.sqrt_nonneg _
    have hz : fderiv ℝ (Torus.lift fun y => Real.sqrt (a y)) x = 0 :=
      IsLocalMin.fderiv_eq_zero hmin
    rw [hz, norm_zero]
    exact Real.sqrt_nonneg _
  · -- a(x) > 0: chain rule for `√`, then the Taylor bound on `∇a`
    have hs_pos : 0 < Real.sqrt ((Torus.lift a) x) := Real.sqrt_pos.mpr hpos
    have hs_ne : Real.sqrt ((Torus.lift a) x) ≠ 0 := hs_pos.ne'
    have hs_sq : Real.sqrt ((Torus.lift a) x) ^ 2 = (Torus.lift a) x := Real.sq_sqrt hpos.le
    have hr_sq : Real.sqrt (L / 2) ^ 2 = L / 2 := Real.sq_sqrt (by positivity)
    have hs : HasFDerivAt (fun y => Real.sqrt ((Torus.lift a) y))
        ((1 / (2 * Real.sqrt ((Torus.lift a) x))) • fderiv ℝ (Torus.lift a) x) x :=
      hAd.sqrt hpos.ne'
    have hfg : fderiv ℝ (Torus.lift fun y => Real.sqrt (a y)) x =
        (1 / (2 * Real.sqrt ((Torus.lift a) x))) • fderiv ℝ (Torus.lift a) x := hs.fderiv
    have hc : 0 < 1 / (2 * Real.sqrt ((Torus.lift a) x)) := by
      apply div_pos one_pos
      linarith
    have hD : ‖fderiv ℝ (Torus.lift a) x‖ ≤ 2 * Real.sqrt ((Torus.lift a) x) * Real.sqrt (L / 2) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
      have hsq := tsg_sq_fderiv_le hL ha hC11 x h
      have h2 : (fderiv ℝ (Torus.lift a) x h) ^ 2 ≤
          (2 * Real.sqrt ((Torus.lift a) x) * Real.sqrt (L / 2) * ‖h‖) ^ 2 := by
        have e : (2 * Real.sqrt ((Torus.lift a) x) * Real.sqrt (L / 2) * ‖h‖) ^ 2 =
            2 * L * (Torus.lift a) x * ‖h‖ ^ 2 := by
          linear_combination (4 * Real.sqrt ((Torus.lift a) x) ^ 2 * ‖h‖ ^ 2) * hr_sq
            + (2 * L * ‖h‖ ^ 2) * hs_sq
        rw [e]
        exact hsq
      rw [Real.norm_eq_abs]
      exact abs_le_of_sq_le_sq h2 (by positivity)
    rw [hfg, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    calc 1 / (2 * Real.sqrt ((Torus.lift a) x)) * ‖fderiv ℝ (Torus.lift a) x‖
        ≤ 1 / (2 * Real.sqrt ((Torus.lift a) x)) *
            (2 * Real.sqrt ((Torus.lift a) x) * Real.sqrt (L / 2)) :=
          mul_le_mul_of_nonneg_left hD hc.le
      _ = Real.sqrt (L / 2) := by field_simp

/-- **Lemma C.6 `M:B:lem:sqrt-lipschitz`, gradient clause on `𝕋^d`** (proof of
`HRS.Main.SpecSW2.torus_sqrt_gradient_le`; statement copied verbatim). -/
theorem torus_sqrt_gradient_le_proof {d : ℕ} {a : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L) (ha : ∀ x, 0 ≤ a x)
    (hC11 : PDE.IsC11 L a) :
    (∀ x : Euc d, DifferentiableAt ℝ (Torus.lift fun y => Real.sqrt (a y)) x →
        ‖fderiv ℝ (Torus.lift fun y => Real.sqrt (a y)) x‖ ≤ Real.sqrt (L / 2)) ∧
    (∀ᵐ x : Euc d ∂volume, DifferentiableAt ℝ (Torus.lift fun y => Real.sqrt (a y)) x) ∧
    eLpNormEssSup (fun x => fderiv ℝ (Torus.lift fun y => Real.sqrt (a y)) x) volume
      ≤ ENNReal.ofReal (Real.sqrt (L / 2)) := by
  have hLip : LipschitzWith (Real.toNNReal (Real.sqrt (L / 2)))
      (Torus.lift fun y => Real.sqrt (a y)) :=
    HRS.sqrt_lipschitz (E := Euc d) (Torus.lift a) hC11.1 (fun y => ha _) L hL hC11.2
  have hae : ∀ᵐ x : Euc d ∂volume, DifferentiableAt ℝ (Torus.lift fun y => Real.sqrt (a y)) x :=
    hLip.ae_differentiableAt
  refine ⟨fun x _ => tsg_norm_fderiv_le hL ha hC11 x, hae, ?_⟩
  refine eLpNormEssSup_le_of_ae_bound ?_
  filter_upwards [hae] with x _
  exact tsg_norm_fderiv_le hL ha hC11 x

example := (@torus_sqrt_gradient_le_proof : type_of% @HRS.Main.SpecSW2.torus_sqrt_gradient_le)

end HRS.Main
