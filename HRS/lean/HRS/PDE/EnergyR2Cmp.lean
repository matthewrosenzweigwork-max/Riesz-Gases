import HRS.PDE.EnergyR2K

/-!
# Regime R2b: the weighted comparison `B(w,w) ≤ λ₀⁻¹ B(√μ w,√μ w) + C‖w‖²`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.R2Aux

variable {d : ℕ}

theorem coeffOf_sub_smul {u v : Torus d → ℝ} (hu : Continuous u) (hv : Continuous v) (c : ℝ)
    (k : Lattice d) :
    coeffOf (fun x => u x - c * v x) k = coeffOf u k - (c : ℂ) * coeffOf v k := by
  rw [coeffOf_eq, coeffOf_eq, coeffOf_eq]
  have hi1 : Integrable fun x : Torus d => Torus.mode (-k) x * (u x : ℂ) :=
    integrable_of_continuous' ((Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp hu))
  have hi2 : Integrable fun x : Torus d => Torus.mode (-k) x * (v x : ℂ) :=
    integrable_of_continuous' ((Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp hv))
  have e : ∀ x : Torus d, Torus.mode (-k) x * ((u x - c * v x : ℝ) : ℂ) =
      Torus.mode (-k) x * (u x : ℂ) - (c : ℂ) * (Torus.mode (-k) x * (v x : ℂ)) := by
    intro x; push_cast; ring
  simp_rw [e]
  rw [integral_sub hi1 (hi2.const_mul _), integral_const_mul]

theorem mulCoeff_sub_const {n : ℕ} {μ : Torus d → ℝ} (hμ : Continuous μ) (c : ℝ) {w : Coeff d}
    (hw : IsRealCoeff w) (hwt : IsTrigPoly n w) (k : Lattice d) :
    mulCoeff (coeffOf fun x => μ x - c) w k = mulCoeff (coeffOf μ) w k - (c : ℂ) * w k := by
  have hfc : Continuous (toFun w) := continuous_toFun_trig hw hwt
  have hcw : coeffOf (toFun w) = w := coeffOf_toFun_trig hw hwt
  have hμc : Continuous fun x => μ x - c := hμ.sub continuous_const
  have h1 : mulCoeff (coeffOf fun x => μ x - c) w =
      coeffOf (fun x => (μ x - c) * toFun w x) := by
    rw [coeffOf_mul _ _ (memLp_of_continuous_real hμc) (memLp_of_continuous_real hfc), hcw]
  have h2 : mulCoeff (coeffOf μ) w = coeffOf (fun x => μ x * toFun w x) := by
    rw [coeffOf_mul _ _ (memLp_of_continuous_real hμ) (memLp_of_continuous_real hfc), hcw]
  have e : (fun x => (μ x - c) * toFun w x) = fun x => μ x * toFun w x - c * toFun w x := by
    funext x; ring
  rw [h1, h2, e, coeffOf_sub_smul (u := fun x => μ x * toFun w x) (v := toFun w) (hμ.mul hfc) hfc c k, hcw]

theorem quadForm_eq_box {n : ℕ} (𝔪 : Lattice d → ℝ) {w : Coeff d} (hwt : IsTrigPoly n w) :
    quadForm 𝔪 w = ∑ k ∈ boxFin d n, 𝔪 k * ‖w k‖ ^ 2 := by
  unfold quadForm
  refine tsum_eq_sum fun k hk => ?_
  rw [eq_zero_of_isTrigPoly hwt hk]; simp

theorem isC11_sub_const {L : ℝ} {μ : Torus d → ℝ} (h : IsC11 L μ) (c : ℝ) :
    IsC11 L (fun x => μ x - c) := by
  obtain ⟨h1, h2⟩ := h
  have e : Torus.lift (fun x => μ x - c) = fun y => Torus.lift μ y - c := rfl
  refine ⟨?_, ?_⟩
  · unfold Torus.IsCk
    rw [e]
    exact h1.sub contDiff_const
  · rw [e]
    have : (fun x => fderiv ℝ (fun y => Torus.lift μ y - c) x) =
        fun x => fderiv ℝ (Torus.lift μ) x := by
      funext x
      exact fderiv_sub_const c
    rw [this]
    exact h2

/-- Lemma C.3(iv) in the form used in (ii): for `μ ≥ λ₀ > 0`,
`B_q(w,w) ≤ λ₀⁻¹ B_q(√μ w, √μ w) + C ‖w‖²_{L²}`, uniformly in the unit vector `q`. -/
theorem compare_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : (d : ℝ) - 2 < s) (hsd : s < d) (lam0 : ℝ)
    (hl : 0 < lam0) (Λ : ℝ) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (q : Euc d), ‖q‖ ≤ 1 → ∀ (μ : Torus d → ℝ), (∀ x, lam0 ≤ μ x) →
      Torus.IsCk 2 μ → Torus.cbNorm 2 μ ≤ Λ → ∀ (n : ℕ) (w : Coeff d), IsRealCoeff w →
      IsTrigPoly n w →
      quadForm (symbolK d s q) w ≤ lam0⁻¹ * quadForm (symbolK d s q)
          (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w) + Cc * hsNormSq 0 w := by
  have hd1 : 1 ≤ d := hd
  obtain ⟨Cw, hCw0, hCw⟩ := weighted_bound hd s hs0 hs1 hsd
  refine ⟨lam0⁻¹ * (2 * (Cw * (3 / 2 * |Λ|))), by positivity, ?_⟩
  intro q hq μ hμl hμ2 hΛ n w hw hwt
  have hμ0 : ∀ x, 0 ≤ μ x := fun x => hl.le.trans (hμl x)
  have hμc : Continuous μ := continuous_of_lift' hμ2.continuous
  set a₂ : Torus d → ℝ := fun x => μ x - lam0 with ha₂
  have ha₂c : Continuous a₂ := hμc.sub continuous_const
  have ha₂0 : ∀ x, 0 ≤ a₂ x := fun x => by simp only [ha₂]; linarith [hμl x]
  have hΛ0 : 0 ≤ Λ := (cbNorm_nonneg' 2 μ).trans hΛ
  have hΛa : |Λ| = Λ := abs_of_nonneg hΛ0
  set f := toFun w with hf
  have hfc : Continuous f := continuous_toFun_trig hw hwt
  have hf1 : Torus.IsCk 1 f := isCk_toFun_trig hw hwt 1
  have hfS : MemSobolev (thetaOrder d s / 2) f := memSobolev_toFun_trig hw hwt _
  have hl2 : l2NormSq f = hsNormSq 0 w := by
    rw [l2NormSq_eq_hsNormSq hfc, hf, coeffOf_toFun_trig hw hwt]
  set N0 := hsNormSq 0 w with hN0
  have hN0nn : 0 ≤ N0 := hsNormSq_nonnegE 0 w
  have hC11 : IsC11 (Torus.cbNorm 2 μ) μ := isC11_of_cbNorm hμ2
  have hE : Cw * (Torus.cbNorm 2 μ / 2 + Λ) * N0 ≤ Cw * (3 / 2 * |Λ|) * N0 := by
    rw [hΛa]; gcongr; linarith
  -- the two weighted symmetrisations
  have hμΛ : ∀ x, μ x ≤ Λ := fun x => (le_abs_self _).trans ((abs_le_cbNorm hμ2 x).trans hΛ)
  have h1 := hCw q hq (Torus.cbNorm 2 μ) Λ μ f (cbNorm_nonneg' 2 μ) hμ0 hμΛ hC11 hf1 hfS
  have h2 := hCw q hq (Torus.cbNorm 2 μ) Λ a₂ f (cbNorm_nonneg' 2 μ) ha₂0
    (fun x => by simp only [ha₂]; linarith [hμΛ x]) (isC11_sub_const hC11 lam0) hf1 hfS
  rw [hl2] at h1 h2
  -- identification of the forms
  have hq1 : symbolForm (symbolK d s q) (fun x => Real.sqrt (μ x) * f x)
      (fun x => Real.sqrt (μ x) * f x) = quadForm (symbolK d s q)
        (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w) :=
    quadForm_eq_symbolForm _ _ hμc.sqrt hw hwt
  have hq2 : 0 ≤ symbolForm (symbolK d s q) (fun x => Real.sqrt (a₂ x) * f x)
      (fun x => Real.sqrt (a₂ x) * f x) := by
    rw [quadForm_eq_symbolForm _ _ ha₂c.sqrt hw hwt]
    exact quadForm_symbolK_nonneg' hd1 hs0 hsd q _
  have hPμ := re_PK_eq (symbolK d s q) μ hμc hw hwt
  have hPa := re_PK_eq (symbolK d s q) a₂ ha₂c hw hwt
  have hdiff : symbolForm (symbolK d s q) (fun x => μ x * f x) f -
      symbolForm (symbolK d s q) (fun x => a₂ x * f x) f =
      lam0 * quadForm (symbolK d s q) w := by
    rw [← hPμ, ← hPa, ← Complex.sub_re, ← Finset.sum_sub_distrib, quadForm_eq_box _ hwt,
      Finset.mul_sum]
    have : ∀ k ∈ boxFin d n,
        conj (w k) * (((symbolK d s q k : ℝ) : ℂ) * mulCoeff (coeffOf μ) w k) -
          conj (w k) * (((symbolK d s q k : ℝ) : ℂ) * mulCoeff (coeffOf a₂) w k) =
        ((lam0 * (symbolK d s q k * ‖w k‖ ^ 2) : ℝ) : ℂ) := by
      intro k _
      rw [ha₂, mulCoeff_sub_const hμc lam0 hw hwt k]
      have h := Complex.mul_conj' (w k)
      push_cast
      linear_combination (((symbolK d s q k : ℝ) : ℂ) * (lam0 : ℂ)) * h
    rw [Finset.sum_congr rfl this, ← Complex.ofReal_sum, Complex.ofReal_re]
  have hbw : lam0 * quadForm (symbolK d s q) w ≤
      quadForm (symbolK d s q) (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w) +
        2 * (Cw * (3 / 2 * |Λ|) * N0) := by
    have := (abs_le.mp h1).2
    have h3 := (abs_le.mp h2).1
    linarith
  have hli : 0 < lam0⁻¹ := inv_pos.mpr hl
  have := mul_le_mul_of_nonneg_left hbw hli.le
  calc quadForm (symbolK d s q) w = lam0⁻¹ * (lam0 * quadForm (symbolK d s q) w) := by
        field_simp
    _ ≤ lam0⁻¹ * (quadForm (symbolK d s q)
          (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w) + 2 * (Cw * (3 / 2 * |Λ|) * N0)) :=
        mul_le_mul_of_nonneg_left hbw hli.le
    _ = _ := by ring

end HRS.PDE.R2Aux
