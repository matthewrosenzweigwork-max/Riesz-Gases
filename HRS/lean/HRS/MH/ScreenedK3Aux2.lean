import HRS.MH.ScreenedK3Aux1

/-! Packet K3 (`gk_weak`), auxiliary 2: the mollified identity
`∫ g_ε(x-y) ∂_iφ(x) = -∫ ∂_i g_ε(x-y) φ(x)` for `0 < ε ≤ 1`, with its integrability hypotheses. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

lemma k3_fderiv_gEps (s ε : ℝ) (hε : 0 < ε) (y x v : Euc d) :
    fderiv ℝ (fun z => movtr_gEps d s ε (z - y)) x v = movtr_dEps d s ε v (x - y) := by
  have hu : 0 < ‖x - y‖ ^ 2 + ε ^ 2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hε 2)
  have h := (movtr_gEps_hasFDerivAt s ε (x - y) hu).comp x ((hasFDerivAt_id x).sub_const y)
  rw [show (fun z => movtr_gEps d s ε (z - y)) = movtr_gEps d s ε ∘ (fun z => id z - y) from rfl,
    h.fderiv]
  simp [movtr_dEps, innerSL_apply_apply, inner_sub_left]

lemma k3_dEps_bound {s : ℝ} (hs0 : 0 ≤ s) {ε : ℝ} (hε : 0 ≤ ε) (e : Euc d) (he : ‖e‖ ≤ 1) (z : Euc d) :
    |movtr_dEps d s ε e z| ≤ movtr_sigma s * ‖z‖ ^ (-s - 1) := by
  have hσ : 0 ≤ movtr_sigma s := by unfold movtr_sigma; split_ifs <;> linarith
  by_cases hz : z = 0
  · subst hz
    rw [movtr_dEps, inner_zero_left, mul_zero, abs_zero]
    exact mul_nonneg hσ (Real.rpow_nonneg (norm_nonneg _) _)
  · exact movtr_dEps_abs_le_z hs0 hε e z he hz

lemma k3_gEps_dom {s : ℝ} (hs0 : 0 ≤ s) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (y x : Euc d)
    (hx : x ≠ y) (c : ℝ) :
    ‖movtr_gEps d s ε (x - y) * c‖ ≤
      2 * (‖x - y‖ ^ (-movtr_sp s) * ‖c‖) + (‖x‖ * ‖c‖ + (‖y‖ + 1) * ‖c‖) := by
  have hz : x - y ≠ 0 := sub_ne_zero.mpr hx
  have h1 := movtr_gEps_abs_le (d := d) hs0 hε0 hε1 hz
  have hc := norm_nonneg c
  have hn : ‖x - y‖ * ‖c‖ ≤ (‖x‖ + ‖y‖) * ‖c‖ := mul_le_mul_of_nonneg_right (norm_sub_le x y) hc
  rw [norm_mul, Real.norm_eq_abs (movtr_gEps d s ε (x - y))]
  have h2 : |movtr_gEps d s ε (x - y)| * ‖c‖ ≤ (2 * ‖x - y‖ ^ (-movtr_sp s) + ‖x - y‖ + 1) * ‖c‖ :=
    mul_le_mul_of_nonneg_right h1 hc
  nlinarith

lemma k3_gEps_dom_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (y : Euc d)
    {h : Euc d → ℝ} (hc : Continuous h) (hb : ∃ M, ∀ x, ‖h x‖ ≤ M)
    (h0 : Integrable fun x => ‖h x‖) (h1 : Integrable fun x => ‖x‖ * ‖h x‖) :
    Integrable fun x => 2 * (‖x - y‖ ^ (-movtr_sp s) * ‖h x‖) + (‖x‖ * ‖h x‖ + (‖y‖ + 1) * ‖h x‖) := by
  have hsp : movtr_sp s < d := movtr_sp_lt hsd hd
  have hspos : 0 < movtr_sp s := movtr_sp_pos hs0
  have hA := k3_integrable_rpow hd (a := -movtr_sp s) (by linarith) (by linarith) y hc hb h0
  exact (hA.const_mul 2).add (h1.add (h0.const_mul (‖y‖ + 1)))

lemma k3_gEps_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (y : Euc d) {h : Euc d → ℝ} (hc : Continuous h) (hb : ∃ M, ∀ x, ‖h x‖ ≤ M)
    (h0 : Integrable fun x => ‖h x‖) (h1 : Integrable fun x => ‖x‖ * ‖h x‖) :
    Integrable fun x => movtr_gEps d s ε (x - y) * h x := by
  refine Integrable.mono' (k3_gEps_dom_integrable hd hs0 hsd y hc hb h0 h1) ?_ ?_
  · exact ((((movtr_gEps_measurable (d := d) s ε).comp (measurable_id.sub_const y))).mul
      hc.measurable).aestronglyMeasurable
  · exact (k3_ae_ne hd y).mono (fun x hx => k3_gEps_dom hs0 hε0 hε1 y x hx (h x))

lemma k3_dEps_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s + 1 < d) {ε : ℝ} (hε0 : 0 ≤ ε)
    (e : Euc d) (he : ‖e‖ ≤ 1) (y : Euc d) {h : Euc d → ℝ} (hc : Continuous h)
    (hb : ∃ M, ∀ x, ‖h x‖ ≤ M) (h0 : Integrable fun x => ‖h x‖) :
    Integrable fun x => movtr_dEps d s ε e (x - y) * h x := by
  have hσ : 0 ≤ movtr_sigma s := by unfold movtr_sigma; split_ifs <;> linarith
  have hG := k3_integrable_rpow hd (a := -s - 1) (by linarith) (by linarith) y hc hb h0
  refine Integrable.mono' (hG.const_mul (movtr_sigma s)) ?_ ?_
  · have hm : Measurable fun z : Euc d => movtr_dEps d s ε e z := by
      unfold movtr_dEps
      fun_prop
    exact (((hm.comp (measurable_id.sub_const y))).mul hc.measurable).aestronglyMeasurable
  · refine Eventually.of_forall (fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs (movtr_dEps d s ε e (x - y))]
    calc |movtr_dEps d s ε e (x - y)| * ‖h x‖
        ≤ (movtr_sigma s * ‖x - y‖ ^ (-s - 1)) * ‖h x‖ :=
          mul_le_mul_of_nonneg_right (k3_dEps_bound hs0 hε0 e he (x - y)) (norm_nonneg (h x))
      _ = movtr_sigma s * (‖x - y‖ ^ (-s - 1) * ‖h x‖) := by ring

/-- Schwartz test functions: continuity, boundedness, and the two moment integrability facts. -/
lemma k3_sch_props (φ : SchwartzMap (Euc d) ℝ) :
    Continuous φ ∧ (∃ M, ∀ x, ‖φ x‖ ≤ M) ∧ Integrable (fun x => ‖φ x‖) ∧
      Integrable (fun x => ‖x‖ * ‖φ x‖) := by
  refine ⟨φ.continuous, ⟨SchwartzMap.seminorm ℝ 0 0 φ, fun x => SchwartzMap.norm_le_seminorm ℝ φ x⟩,
    φ.integrable.norm, ?_⟩
  simpa using SchwartzMap.integrable_pow_mul volume φ 1

/-- The partial derivative `∂_i φ` of a Schwartz function: the same four properties. -/
lemma k3_sch_deriv_props (φ : SchwartzMap (Euc d) ℝ) (i : Fin d) :
    Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) ∧
      (∃ M, ∀ x, ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ ≤ M) ∧
      Integrable (fun x => ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖) ∧
      Integrable (fun x => ‖x‖ * ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖) := by
  set D := SchwartzMap.fderivCLM ℝ (Euc d) ℝ φ with hD
  have hDx : ∀ x, fderiv ℝ φ x = D x := fun x => by
    rw [hD, SchwartzMap.fderivCLM_apply]
  have hsing : ∀ x, ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖ ≤ ‖D x‖ := fun x => by
    rw [hDx x]
    have := (D x).le_opNorm (EuclideanSpace.single i (1 : ℝ))
    simpa using this
  have hD0 : Integrable (fun x => ‖D x‖) := by
    simpa using SchwartzMap.integrable_pow_mul volume D 0
  have hD1 : Integrable (fun x => ‖x‖ * ‖D x‖) := by
    simpa using SchwartzMap.integrable_pow_mul volume D 1
  have hcont : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    have : (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        fun x => D x (EuclideanSpace.single i 1) := funext fun x => by rw [hDx x]
    rw [this]
    exact (D.continuous).clm_apply continuous_const
  refine ⟨hcont, ⟨SchwartzMap.seminorm ℝ 0 0 D, fun x => ?_⟩, ?_, ?_⟩
  · exact (hsing x).trans (SchwartzMap.norm_le_seminorm ℝ D x)
  · exact hD0.mono' hcont.norm.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [norm_norm]; exact hsing x)
  · refine hD1.mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact (measurable_norm.mul (hcont.measurable.norm)).aestronglyMeasurable
    · rw [norm_mul, norm_norm, norm_norm]
      exact mul_le_mul_of_nonneg_left (hsing x) (norm_nonneg _)

end HRS.MH.Screened
