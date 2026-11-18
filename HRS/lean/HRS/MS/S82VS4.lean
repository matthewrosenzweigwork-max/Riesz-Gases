import HRS.MS.S82VS3

/-!
# S8.2 A02 (S82V), part 9: stationarity of the local generator against a row of `Q`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82V
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

/-- The hypotheses of the stationarity lemma for the row `Q (·, y)`. -/
lemma s82v_row_hyps {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (y : Euc d) :
    ContDiffOn ℝ 2 (fun x => Q x y) {x | x ≠ y} ∧ 0 ≤ max A 0 * jbracket y ^ M ∧
    (∀ x, x ≠ y → ‖gradient (fun x => Q x y) x‖ ≤
      (max A 0 * jbracket y ^ M) * jbracket x ^ (max M 0) *
        (1 + HRS.MS.S82N.s82n_smallRadius x y ^ (1 - HRS.MS.S82N.s82n_critS d))) ∧
    (∀ x, x ≠ y → ‖fderiv ℝ (fderiv ℝ (fun x => Q x y)) x‖ ≤
      (max A 0 * jbracket y ^ M) * jbracket x ^ (max M 0) * HRS.MS.S82N.s82n_pole x y) := by
  have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have hjb : ∀ z : Euc d, 0 < jbracket z := HRS.MS.S82N.s82n_jb_pos
  have hv : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (hjb y).le _
  have hu : ∀ x : Euc d, jbracket x ^ M ≤ jbracket x ^ (max M 0) := fun x =>
    Real.rpow_le_rpow_of_exponent_le (HRS.MS.S82N.s82n_jb_one_le x) (le_max_left _ _)
  have hu0 : ∀ x : Euc d, 0 ≤ jbracket x ^ M := fun x => Real.rpow_nonneg (hjb x).le _
  have hcomb : ∀ (x : Euc d) (T : ℝ), 0 ≤ T →
      A * (jbracket x ^ M * jbracket y ^ M) * T ≤
        (max A 0 * jbracket y ^ M) * jbracket x ^ (max M 0) * T := by
    intro x T hT
    refine mul_le_mul_of_nonneg_right ?_ hT
    have h1 : A * (jbracket x ^ M * jbracket y ^ M) ≤ max A 0 * (jbracket x ^ M * jbracket y ^ M) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg (hu0 x) hv)
    have h2 : max A 0 * (jbracket x ^ M * jbracket y ^ M) ≤
        max A 0 * (jbracket x ^ (max M 0) * jbracket y ^ M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hu x) hv) (le_max_right _ _)
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ = _ := by ring
  have hsr : ∀ x : Euc d, ∀ e : ℝ, 0 ≤ 1 + HRS.MS.S82N.s82n_smallRadius x y ^ e := fun x e => by
    have := Real.rpow_nonneg (HRS.MS.S82P.s82p_smallRadius_nonneg x y) e; linarith
  refine ⟨?_, mul_nonneg (le_max_right _ _) hv, fun x hx => ?_, fun x hx => ?_⟩
  · have hmaps : Set.MapsTo (fun x : Euc d => (x, y)) {x | x ≠ y} {p : Euc d × Euc d | p.1 ≠ p.2} :=
      fun x hx => hx
    have := hQ.smooth.comp (contDiff_id.prodMk contDiff_const).contDiffOn hmaps
    exact (this.of_le (by norm_num))
  · have h1 := hQ.gradient x y hx
    have h2 : ‖gradient (fun x => Q x y) x‖ ≤ ‖pairGradX Q x y‖ + ‖pairGradY Q x y‖ := by
      have : ‖gradient (fun x => Q x y) x‖ = ‖pairGradX Q x y‖ := rfl
      rw [this]; linarith [norm_nonneg (pairGradY Q x y)]
    refine h2.trans (h1.trans ?_)
    exact hcomb x _ (hsr x _)
  · have h1 := hQ.hessian x y hx
    have h2 : ‖fderiv ℝ (fderiv ℝ (fun x => Q x y)) x‖ ≤
        ‖iteratedFDeriv ℝ 2 (Function.uncurry Q) (x, y)‖ :=
      s82v_hess_comp (Function.uncurry Q) hopen (hQ.smooth.of_le (by norm_num)) x y hx
    refine h2.trans (h1.trans ?_)
    exact hcomb x _ (hsr x _)

end HRS.MS.S82V

end
