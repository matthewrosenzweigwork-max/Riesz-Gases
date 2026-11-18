import HRS.MS.UniqM1Fin

/-!
# M3 of `UniqPlan.md`: elementary commutator bounds for the mollifier

For `a : Euc d → ℝ` and `F : Euc d → ℝ` put
`comm d ε a F y := moll d ε (fun x => a x * F x) y - a y * moll d ε F y`.
Since `∫ η_ε = 1`, `η_ε ≥ 0` and `supp η_ε ⊆ ball 0 ε`, this equals
`∫ η_ε(y - x) (a x - a y) F x dx`, and the Lipschitz bound gives the pointwise estimate
`|comm d ε a F y| ≤ ε L · moll d ε (‖F‖) y`.

Hypotheses (stated explicitly in each theorem):
* `a` is Lipschitz with constant `L ≥ 0`: `∀ x y, |a x - a y| ≤ L * ‖x - y‖`.
  No boundedness of `a` is assumed; continuity of `a` is derived from the Lipschitz bound.
* `ε > 0`.
* `F` locally integrable (`comm_abs_le`) or `LocMass B F` (`comm_lintegral_ball_le`).

Main results:
* `comm_abs_le` (1): pointwise bound `|comm d ε a F y| ≤ ε * L * moll d ε (fun x => ‖F x‖) y`.
* `comm_lintegral_ball_le` (2): `∫⁻ x in ball c r, ‖comm d ε a F x‖ₑ ^ 2 ≤ ofReal ((ε * L) ^ 2) * ∫⁻ y in ball c (r + ε), ‖F y‖ₑ ^ 2`.
* (3) is covered by (1) and (2): they assume only the Lipschitz bound, with no boundedness.
* (4) and (5) are not proved here.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqM3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqM1

variable {d : ℕ}

/-- The commutator `comm d ε a F y = η_ε * (a F) (y) - a(y) (η_ε * F)(y)`. -/
def comm (d : ℕ) (ε : ℝ) (a : Euc d → ℝ) (F : Euc d → ℝ) (y : Euc d) : ℝ :=
  moll d ε (fun x => a x * F x) y - a y * moll d ε F y

/-- A Lipschitz function (constant `L ≥ 0`) is continuous. -/
theorem m3_continuous_of_lip {L : ℝ} (hL : 0 ≤ L) {a : Euc d → ℝ}
    (ha : ∀ x y : Euc d, |a x - a y| ≤ L * ‖x - y‖) : Continuous a := by
  refine (LipschitzWith.of_dist_le_mul (K := L.toNNReal) fun x y => ?_).continuous
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL]
  exact ha x y

/-- `x ↦ η_ε(y - x) G(x)` is integrable for locally integrable `G`. -/
theorem m3_kernel_integrable {ε : ℝ} (hε : 0 < ε) (y : Euc d) {G : Euc d → ℝ}
    (hG : LocallyIntegrable G volume) :
    Integrable (fun x => eta d ε (y - x) * G x) volume := by
  have hco : Continuous fun x => eta d ε (y - x) :=
    eta_contDiff.continuous.comp (continuous_const.sub continuous_id)
  have hcs : HasCompactSupport fun x => eta d ε (y - x) :=
    (eta_hasCompactSupport hε).comp_homeomorph (Homeomorph.subLeft y)
  have h := hG.integrable_smul_left_of_hasCompactSupport hco hcs
  simpa only [smul_eq_mul] using h

/-- `x ↦ η_ε(y - x) (a x * G x)` is integrable for continuous `a` and locally integrable `G`. -/
theorem m3_kernel_mul_integrable {ε : ℝ} (hε : 0 < ε) (y : Euc d) {a : Euc d → ℝ}
    (ha : Continuous a) {G : Euc d → ℝ} (hG : LocallyIntegrable G volume) :
    Integrable (fun x => eta d ε (y - x) * (a x * G x)) volume := by
  have hco : Continuous fun x => eta d ε (y - x) * a x :=
    (eta_contDiff.continuous.comp (continuous_const.sub continuous_id)).mul ha
  have hcs : HasCompactSupport fun x => eta d ε (y - x) * a x :=
    ((eta_hasCompactSupport hε).comp_homeomorph (Homeomorph.subLeft y)).mul_right
  have h := hG.integrable_smul_left_of_hasCompactSupport hco hcs
  simpa only [smul_eq_mul, mul_assoc] using h

/-- Integral form: `comm d ε a F y = ∫ η_ε(y - x) (a x - a y) F x dx` (for continuous `a`). -/
theorem m3_comm_eq_integral {ε : ℝ} (hε : 0 < ε) {a F : Euc d → ℝ} (ha : Continuous a)
    (hF : LocallyIntegrable F volume) (y : Euc d) :
    comm d ε a F y = ∫ x, eta d ε (y - x) * (a x - a y) * F x := by
  have hf := m3_kernel_mul_integrable hε y ha hF
  have hg := (m3_kernel_integrable hε y hF).const_mul (a y)
  unfold comm moll
  rw [← integral_const_mul, ← integral_sub hf hg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  ring

/-- **(1)** Pointwise commutator bound. Only the Lipschitz bound on `a` is assumed (no boundedness),
`F` locally integrable, `ε > 0`, `L ≥ 0`:
`|comm d ε a F y| ≤ ε * L * moll d ε (fun x => ‖F x‖) y`. -/
theorem m3_comm_abs_le {ε : ℝ} (hε : 0 < ε) {L : ℝ} (hL : 0 ≤ L) {a F : Euc d → ℝ}
    (ha : ∀ x y : Euc d, |a x - a y| ≤ L * ‖x - y‖) (hF : LocallyIntegrable F volume)
    (y : Euc d) :
    |comm d ε a F y| ≤ ε * L * moll d ε (fun x => ‖F x‖) y := by
  have hc := m3_continuous_of_lip hL ha
  have hG : LocallyIntegrable (fun x => ‖F x‖) volume := by
    rw [← locallyIntegrableOn_univ] at hF ⊢
    exact hF.norm
  have hint := (m3_kernel_integrable hε y hG).const_mul (ε * L)
  rw [m3_comm_eq_integral hε hc hF y, ← Real.norm_eq_abs]
  calc ‖∫ x, eta d ε (y - x) * (a x - a y) * F x‖
      ≤ ∫ x, (ε * L) * (eta d ε (y - x) * ‖F x‖) := by
        refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun x => ?_)
        by_cases hx : eta d ε (y - x) = 0
        · simp [hx]
        · have hmem : y - x ∈ Function.support (eta d ε) := Function.mem_support.2 hx
          have hball : ‖y - x‖ < ε := mem_ball_zero_iff.1 (eta_support hε hmem)
          have hxy : ‖x - y‖ ≤ ε := by rw [norm_sub_rev]; exact hball.le
          have h1 : |a x - a y| ≤ ε * L := by
            have := (ha x y).trans (mul_le_mul_of_nonneg_left hxy hL)
            linarith [mul_comm L ε]
          have he : 0 ≤ eta d ε (y - x) := eta_nonneg hε _
          have key : ‖eta d ε (y - x) * (a x - a y) * F x‖
              = eta d ε (y - x) * |a x - a y| * ‖F x‖ := by
            rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg he]
          rw [key]
          calc eta d ε (y - x) * |a x - a y| * ‖F x‖
              ≤ eta d ε (y - x) * (ε * L) * ‖F x‖ :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 he) (norm_nonneg _)
            _ = (ε * L) * (eta d ε (y - x) * ‖F x‖) := by ring
    _ = ε * L * moll d ε (fun x => ‖F x‖) y := by
        rw [integral_const_mul]
        rfl

/-- **(2)** The `L²` bound on balls. Assumptions: `ε > 0`, `L ≥ 0`, `a` Lipschitz with constant `L`
(no boundedness), `F` with `LocMass B F` (uniform local `L²` mass), any centre `c` and radius `r`:
`∫⁻ x in ball c r, ‖comm d ε a F x‖ₑ ^ 2 ≤ ENNReal.ofReal ((ε * L) ^ 2) * ∫⁻ y in ball c (r + ε), ‖F y‖ₑ ^ 2`. -/
theorem m3_comm_lintegral_ball_le {ε : ℝ} (hε : 0 < ε) {L : ℝ} (hL : 0 ≤ L) {a F : Euc d → ℝ}
    (ha : ∀ x y : Euc d, |a x - a y| ≤ L * ‖x - y‖) {B : ℝ} (hF : LocMass B F) (c : Euc d)
    (r : ℝ) :
    ∫⁻ x in ball c r, ‖comm d ε a F x‖ₑ ^ 2
      ≤ ENNReal.ofReal ((ε * L) ^ 2) * ∫⁻ y in ball c (r + ε), ‖F y‖ₑ ^ 2 := by
  have hG : LocMass B (fun x => ‖F x‖) :=
    ⟨hF.1.norm, fun c' => by simpa only [enorm_norm] using hF.2 c'⟩
  have hpt : ∀ x, ‖comm d ε a F x‖ₑ ^ 2
      ≤ ENNReal.ofReal (ε * L) ^ 2 * ‖moll d ε (fun z => ‖F z‖) x‖ₑ ^ 2 := by
    intro x
    have hm : 0 ≤ moll d ε (fun z => ‖F z‖) x :=
      integral_nonneg fun z => mul_nonneg (eta_nonneg hε _) (norm_nonneg _)
    have h1 : ‖comm d ε a F x‖ₑ ≤ ENNReal.ofReal (ε * L) * ‖moll d ε (fun z => ‖F z‖) x‖ₑ := by
      rw [Real.enorm_eq_ofReal_abs (comm d ε a F x),
        Real.enorm_eq_ofReal_abs (moll d ε (fun z => ‖F z‖) x), abs_of_nonneg hm,
        ← ENNReal.ofReal_mul (mul_nonneg hε.le hL)]
      exact ENNReal.ofReal_le_ofReal (m3_comm_abs_le hε hL ha hF.locallyIntegrable x)
    calc ‖comm d ε a F x‖ₑ ^ 2
        ≤ (ENNReal.ofReal (ε * L) * ‖moll d ε (fun z => ‖F z‖) x‖ₑ) ^ 2 := by gcongr
      _ = _ := mul_pow _ _ _
  calc ∫⁻ x in ball c r, ‖comm d ε a F x‖ₑ ^ 2
      ≤ ∫⁻ x in ball c r, ENNReal.ofReal (ε * L) ^ 2 * ‖moll d ε (fun z => ‖F z‖) x‖ₑ ^ 2 :=
        lintegral_mono fun x => hpt x
    _ = ENNReal.ofReal (ε * L) ^ 2 * ∫⁻ x in ball c r, ‖moll d ε (fun z => ‖F z‖) x‖ₑ ^ 2 :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal (ε * L) ^ 2 * ∫⁻ y in ball c (r + ε), ‖F y‖ₑ ^ 2 := by
        have h : ∫⁻ x in ball c r, ‖moll d ε (fun z => ‖F z‖) x‖ₑ ^ 2
            ≤ ∫⁻ y in ball c (r + ε), ‖F y‖ₑ ^ 2 := by
          simpa only [enorm_norm] using moll_mass_le hε hG c r
        exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = ENNReal.ofReal ((ε * L) ^ 2) * ∫⁻ y in ball c (r + ε), ‖F y‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_pow (mul_nonneg hε.le hL)]

end HRS.MS.UniqM3
