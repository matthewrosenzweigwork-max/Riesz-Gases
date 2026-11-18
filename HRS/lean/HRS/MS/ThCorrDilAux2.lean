import HRS.MS.ThCorrDilAux1

/-!
# TC-Q (part 2): the dilation lemma `tcq_affine_poisson_higher`
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
open HRS HRS.Whole

noncomputable section

namespace HRS.MS.TcQ

variable {d : ℕ}

/-- the dilation `x ↦ c • x` (`c ≠ 0`) as a measurable equivalence. -/
def tcq_dilEquiv (c : ℝ) (hc : c ≠ 0) : Euc d ≃ᵐ Euc d :=
  (Homeomorph.smulOfNeZero c hc).toMeasurableEquiv

theorem tcq_dilEquiv_apply (c : ℝ) (hc : c ≠ 0) (x : Euc d) : tcq_dilEquiv c hc x = c • x := rfl

theorem tcq_integrable_map {c : ℝ} (hc : c ≠ 0) {μ : Measure (Euc d)} {g : Euc d → ℝ} :
    Integrable g (μ.map fun x => c • x) ↔ Integrable (fun x => g (c • x)) μ := by
  have := integrable_map_equiv (tcq_dilEquiv (d := d) c hc) g (μ := μ)
  exact this

theorem tcq_integral_map {c : ℝ} (hc : c ≠ 0) {μ : Measure (Euc d)} (g : Euc d → ℝ) :
    ∫ y, g y ∂(μ.map fun x => c • x) = ∫ x, g (c • x) ∂μ := by
  have := integral_map_equiv (tcq_dilEquiv (d := d) c hc) g (μ := μ)
  exact this

theorem tcq_prob_map {c : ℝ} (hc : c ≠ 0) {μ : Measure (Euc d)} (h : IsProbabilityMeasure μ) :
    IsProbabilityMeasure (μ.map fun x => c • x) := by
  have : Measurable (fun x : Euc d => c • x) := (tcq_dilEquiv (d := d) c hc).measurable
  exact (Measure.isProbabilityMeasure_map_iff this.aemeasurable).2 h

/-- invariance is preserved: `μ̃ = (lam⁻¹ • ·)_* μ` is invariant for `b̃ = lam b(lam ·) = -qm y + lam B(lam y)`. -/
theorem tcq_invariant {q qm lam : ℝ} {B : Euc d → Euc d} {μ : Measure (Euc d)} (hlam : 0 < lam)
    (hq : qm = lam ^ 2 * q) (h : IsInvariantMeasure (fun x => -q • x + B x) μ) :
    IsInvariantMeasure (fun y => -qm • y + lam • B (lam • y)) (μ.map fun x => lam⁻¹ • x) := by
  have hc : lam⁻¹ ≠ 0 := inv_ne_zero hlam.ne'
  have hl0 : lam ≠ 0 := hlam.ne'
  refine ⟨tcq_prob_map hc h.1, fun φ hφ hφc => ?_⟩
  rw [tcq_integral_map hc]
  have hψ : ContDiff ℝ ∞ (fun x => φ (lam⁻¹ • x)) := hφ.comp (contDiff_const_smul lam⁻¹)
  have hψc : HasCompactSupport (fun x => φ (lam⁻¹ • x)) :=
    hφc.comp_homeomorph (Homeomorph.smulOfNeZero lam⁻¹ hc)
  have hint := h.2 _ hψ hψc
  have hφ2 : ContDiff ℝ 2 φ := (contDiff_infty.mp hφ) 2
  have key : ∀ x : Euc d, Laplacian.laplacian φ (lam⁻¹ • x) +
      inner ℝ (-qm • (lam⁻¹ • x) + lam • B (lam • lam⁻¹ • x)) (gradient φ (lam⁻¹ • x))
      = lam ^ 2 * (Laplacian.laplacian (fun x => φ (lam⁻¹ • x)) x +
        inner ℝ (-q • x + B x) (gradient (fun x => φ (lam⁻¹ • x)) x)) := by
    intro x
    have e : lam • lam⁻¹ • x = x := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    rw [tcq_laplacian_dil hφ2, tcq_gradient_dil _ _ (hφ.differentiable (by simp)).differentiableAt, e]
    simp only [inner_add_left, inner_smul_left, inner_smul_right, RCLike.conj_to_real, hq]
    field_simp
  simp only [key]
  rw [integral_const_mul, hint, mul_zero]

theorem tcq_transfer {q qm lam Λ C0 : ℝ} {B : Euc d → Euc d} {μ : Measure (Euc d)} {r χ : Euc d → ℝ}
    (hlam : 0 < lam) (hl1 : lam ≤ 1) (hq : qm = lam ^ 2 * q) (hΛ : lam⁻¹ ≤ Λ) (hr : MemCb 2 r)
    (hsol : IsPoissonSolution (fun y => -qm • y + lam • B (lam • y)) (μ.map fun x => lam⁻¹ • x)
      (fun y => lam ^ 2 * r (lam • y)) C0 χ) :
    IsPoissonSolution (fun x => -q • x + B x) μ r (|C0| * Λ ^ 2 * (1 + Real.log Λ))
      (fun x => χ (lam⁻¹ • x)) := by
  obtain ⟨h2, hint, hmean, heq, hlog, hder⟩ := hsol
  have hl0 : lam ≠ 0 := hlam.ne'
  have hc : lam⁻¹ ≠ 0 := inv_ne_zero hl0
  have hc1 : 1 ≤ lam⁻¹ := one_le_inv₀ hlam |>.2 hl1
  have hΛ1 : 1 ≤ Λ := hc1.trans hΛ
  have hcl : lam⁻¹ * lam = 1 := inv_mul_cancel₀ hl0
  have hcb : cbNorm 2 (fun y => lam ^ 2 * r (lam • y)) ≤ cbNorm 2 r :=
    (tcq_memCb_dil hr (a := lam ^ 2) (by rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ hlam.le hl1)
      hlam.le hl1).2
  have hcb0 : 0 ≤ cbNorm 2 (fun y => lam ^ 2 * r (lam • y)) := PoisFinal.rf_cb_nonneg _
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ1
  have hC0 : |C0| * Λ ^ 2 * (1 + Real.log Λ) ≥ 0 := by positivity
  refine ⟨h2.comp (contDiff_const_smul lam⁻¹), ?_, ?_, ?_, ?_, ?_⟩
  · exact (tcq_integrable_map hc).1 hint
  · rw [← tcq_integral_map hc]; exact hmean
  · intro x
    have e : lam • lam⁻¹ • x = x := by rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
    have hpo := heq (lam⁻¹ • x)
    have hχ2 : ContDiff ℝ 2 χ := h2
    unfold poissonOp at hpo ⊢
    rw [tcq_laplacian_dil hχ2, tcq_gradient_dil _ _ (hχ2.differentiable (by simp)).differentiableAt] 
    beta_reduce at hpo ⊢
    rw [e] at hpo
    simp only [inner_add_left, inner_smul_left, inner_smul_right, RCLike.conj_to_real, hq] at hpo ⊢
    generalize Laplacian.laplacian χ (lam⁻¹ • x) = L at hpo ⊢
    generalize inner ℝ x (gradient χ (lam⁻¹ • x)) = X at hpo ⊢
    generalize inner ℝ (B x) (gradient χ (lam⁻¹ • x)) = Y at hpo ⊢
    apply mul_left_cancel₀ (pow_ne_zero 2 hl0)
    rw [← hpo]
    field_simp
  · intro x
    have hb := hlog (lam⁻¹ • x)
    set cb := cbNorm 2 r with hcbdef
    set cbt := cbNorm 2 (fun y => lam ^ 2 * r (lam • y)) with hcbt
    have hn : ‖lam⁻¹ • x‖ = lam⁻¹ * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 hlam.le)]
    have hl0' : 0 ≤ Real.log (2 + ‖x‖) :=
      Real.log_nonneg (by linarith [norm_nonneg x])
    have hpos : 0 < 2 + ‖x‖ := by positivity
    have h1 : 2 + ‖lam⁻¹ • x‖ ≤ lam⁻¹ * (2 + ‖x‖) := by
      rw [hn]; nlinarith [norm_nonneg x]
    have h2' : Real.log (2 + ‖lam⁻¹ • x‖) ≤ Real.log Λ + Real.log (2 + ‖x‖) := by
      have hpos' : 0 < 2 + ‖lam⁻¹ • x‖ := by positivity
      calc Real.log (2 + ‖lam⁻¹ • x‖) ≤ Real.log (lam⁻¹ * (2 + ‖x‖)) := Real.log_le_log hpos' h1
        _ = Real.log lam⁻¹ + Real.log (2 + ‖x‖) := Real.log_mul (inv_ne_zero hl0) hpos.ne'
        _ ≤ _ := by gcongr
    have hpos2 : 0 ≤ 1 + Real.log (2 + ‖lam⁻¹ • x‖) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + ‖lam⁻¹ • x‖ by linarith [norm_nonneg (lam⁻¹ • x)])
      linarith
    have h3 : 1 + Real.log (2 + ‖lam⁻¹ • x‖) ≤ (1 + Real.log Λ) * (1 + Real.log (2 + ‖x‖)) := by
      nlinarith [mul_nonneg hlogΛ hl0']
    have h4 : C0 * cbt ≤ |C0| * cb := by
      calc C0 * cbt ≤ |C0| * cbt := mul_le_mul_of_nonneg_right (le_abs_self _) hcb0
        _ ≤ |C0| * cb := mul_le_mul_of_nonneg_left hcb (abs_nonneg _)
    have hcb' : 0 ≤ cb := hcb0.trans hcb
    calc |χ (lam⁻¹ • x)| ≤ C0 * cbt * (1 + Real.log (2 + ‖lam⁻¹ • x‖)) := hb
      _ ≤ |C0| * cb * (1 + Real.log (2 + ‖lam⁻¹ • x‖)) := mul_le_mul_of_nonneg_right h4 hpos2
      _ ≤ |C0| * cb * ((1 + Real.log Λ) * (1 + Real.log (2 + ‖x‖))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ (|C0| * Λ ^ 2 * (1 + Real.log Λ)) * cb * (1 + Real.log (2 + ‖x‖)) := by
          have : 1 ≤ Λ ^ 2 := one_le_pow₀ hΛ1
          have hq0 : 0 ≤ |C0| * cb * ((1 + Real.log Λ) * (1 + Real.log (2 + ‖x‖))) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left this hq0]
  · intro x y
    have hd := hder (lam⁻¹ • x) (lam⁻¹ • y)
    have hχ2 : ContDiff ℝ 2 χ := h2
    set cb := cbNorm 2 r with hcbdef
    set cbt := cbNorm 2 (fun y => lam ^ 2 * r (lam • y)) with hcbt
    have g1 : ‖gradient (fun x => χ (lam⁻¹ • x)) x‖ = lam⁻¹ * ‖gradient χ (lam⁻¹ • x)‖ := by
      rw [tcq_gradient_dil _ _ (hχ2.differentiable (by simp)).differentiableAt, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 hlam.le)]
    have g2 : ‖iteratedFDeriv ℝ 2 (fun x => χ (lam⁻¹ • x)) y‖
        ≤ lam⁻¹ ^ 2 * ‖iteratedFDeriv ℝ 2 χ (lam⁻¹ • y)‖ := by
      have := tcq_norm_iter_dil hχ2 (le_refl 2) 1 lam⁻¹ y
      simpa [abs_of_nonneg (inv_nonneg.2 hlam.le)] using this
    have h4 : C0 * cbt ≤ |C0| * cb := by
      calc C0 * cbt ≤ |C0| * cbt := mul_le_mul_of_nonneg_right (le_abs_self _) hcb0
        _ ≤ |C0| * cb := mul_le_mul_of_nonneg_left hcb (abs_nonneg _)
    have hc2 : lam⁻¹ ≤ lam⁻¹ ^ 2 := by nlinarith
    have hΛ2 : lam⁻¹ ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hlam.le) hΛ 2
    have hn1 := norm_nonneg (gradient χ (lam⁻¹ • x))
    have hn2 := norm_nonneg (iteratedFDeriv ℝ 2 χ (lam⁻¹ • y))
    have hΛ3 : 1 ≤ 1 + Real.log Λ := by linarith
    have hcb' : 0 ≤ cb := hcb0.trans hcb
    calc ‖gradient (fun x => χ (lam⁻¹ • x)) x‖ + ‖iteratedFDeriv ℝ 2 (fun x => χ (lam⁻¹ • x)) y‖
        ≤ lam⁻¹ * ‖gradient χ (lam⁻¹ • x)‖ + lam⁻¹ ^ 2 * ‖iteratedFDeriv ℝ 2 χ (lam⁻¹ • y)‖ := by
          rw [g1]; exact add_le_add le_rfl g2
      _ ≤ lam⁻¹ ^ 2 * (‖gradient χ (lam⁻¹ • x)‖ + ‖iteratedFDeriv ℝ 2 χ (lam⁻¹ • y)‖) := by
          nlinarith [mul_le_mul_of_nonneg_right hc2 hn1]
      _ ≤ Λ ^ 2 * (C0 * cbt) := by
          calc _ ≤ lam⁻¹ ^ 2 * (C0 * cbt) := mul_le_mul_of_nonneg_left hd (by positivity)
            _ ≤ Λ ^ 2 * (C0 * cbt) := by
              by_cases hs : 0 ≤ C0 * cbt
              · exact mul_le_mul_of_nonneg_right hΛ2 hs
              · exfalso
                have : 0 ≤ ‖gradient χ (lam⁻¹ • x)‖ + ‖iteratedFDeriv ℝ 2 χ (lam⁻¹ • y)‖ := by positivity
                linarith
      _ ≤ Λ ^ 2 * (|C0| * cb) := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ |C0| * Λ ^ 2 * (1 + Real.log Λ) * cb := by
          have : 0 ≤ |C0| * Λ ^ 2 * cb := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hΛ3 this]

/-- **TC-Q.** `affine_poisson_higher` with the constants uniform for `q ∈ [qm, qp]`
(quantified before `q`, `B`, `μ`, `r`), by the dilation `λ = √(qm/q) ≤ 1`.  The statement is the frozen
`HRS.Whole.affine_poisson_higher` with `hq : 0 < q` replaced by `q ∈ Set.Icc qm qp` and `0 < qm`. -/
theorem tcq_affine_poisson_higher (hd : 1 ≤ d) (qm qp Mb m₂ : ℝ) (hqm : 0 < qm) (m : ℕ) (hm : 2 ≤ m) :
    ∃ C Cm : ℝ, ∀ q ∈ Set.Icc qm qp, ∀ B : Euc d → Euc d, HasCbBound m Mb B → ∀ μ : Measure (Euc d),
      IsInvariantMeasure (fun x => -q • x + B x) μ → Integrable (fun x => ‖x‖ ^ 2) μ →
      ∫ x, ‖x‖ ^ 2 ∂μ ≤ m₂ → ∀ r : Euc d → ℝ, MemCb m r → Integrable r μ → ∫ x, r x ∂μ = 0 →
        ∃ χ : Euc d → ℝ, IsPoissonSolution (fun x => -q • x + B x) μ r C χ ∧
          ContDiff ℝ m χ ∧
          ∀ x : Fin m → Euc d, ∑ j : Fin m, ‖iteratedFDeriv ℝ ((j : ℕ) + 1) χ (x j)‖ ≤ Cm * cbNorm m r := by
  obtain ⟨C0, Cm0, h⟩ := PoisFinal.affine_poisson_higher_proof hd qm Mb (qp / qm * m₂) hqm m hm
  set Λ : ℝ := Real.sqrt (qp / qm) with hΛdef
  refine ⟨|C0| * Λ ^ 2 * (1 + Real.log Λ), Λ ^ m * |Cm0|, fun q hq B hB μ hμ hμ2 hm2 r hr hrint hrc => ?_⟩
  have hq0 : 0 < q := hqm.trans_le hq.1
  have hqpq : 0 < qp := hq0.trans_le hq.2
  have hΛsq : Λ ^ 2 = qp / qm := Real.sq_sqrt (by positivity)
  obtain ⟨lam, hlam, hl1, hqe, hΛ⟩ : ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧ qm = lam ^ 2 * q ∧ lam⁻¹ ≤ Λ := by
    refine ⟨Real.sqrt (qm / q), Real.sqrt_pos.2 (by positivity), ?_, ?_, ?_⟩
    · rw [Real.sqrt_le_one]; exact (div_le_one hq0).2 hq.1
    · rw [Real.sq_sqrt (by positivity)]; field_simp
    · rw [← Real.sqrt_inv, inv_div]
      exact Real.sqrt_le_sqrt (by gcongr; exact hq.2)
  have hl0 : lam ≠ 0 := hlam.ne'
  have hc : lam⁻¹ ≠ 0 := inv_ne_zero hl0
  have hc1 : 1 ≤ lam⁻¹ := (one_le_inv₀ hlam).2 hl1
  have hΛ1 : 1 ≤ Λ := hc1.trans hΛ
  have hcΛ : lam⁻¹ ^ 2 ≤ qp / qm := hΛsq ▸ pow_le_pow_left₀ (inv_nonneg.2 hlam.le) hΛ 2
  have hmap : ∀ y : Euc d, lam • lam⁻¹ • y = y := fun y => by
    rw [smul_smul, mul_inv_cancel₀ hl0, one_smul]
  have hm20 : 0 ≤ m₂ := (integral_nonneg fun x => by positivity).trans hm2
  have ha : |lam ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ hlam.le hl1
  have hrcb := tcq_memCb_dil hr (a := lam ^ 2) ha hlam.le hl1
  have hBt := tcq_hasCb_dil hB hlam.le hl1
  have hinv := tcq_invariant hlam hqe hμ
  have hint2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) (μ.map fun x => lam⁻¹ • x) := by
    rw [tcq_integrable_map hc]
    have : (fun x : Euc d => ‖lam⁻¹ • x‖ ^ 2) = fun x => lam⁻¹ ^ 2 * ‖x‖ ^ 2 := by
      ext x; rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [this]; exact hμ2.const_mul _
  have hmom : ∫ x, ‖x‖ ^ 2 ∂(μ.map fun x => lam⁻¹ • x) ≤ qp / qm * m₂ := by
    rw [tcq_integral_map hc]
    have : (fun x : Euc d => ‖lam⁻¹ • x‖ ^ 2) = fun x => lam⁻¹ ^ 2 * ‖x‖ ^ 2 := by
      ext x; rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [this, integral_const_mul]
    have h0 : 0 ≤ ∫ x, ‖x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
    calc lam⁻¹ ^ 2 * ∫ x, ‖x‖ ^ 2 ∂μ ≤ (qp / qm) * ∫ x, ‖x‖ ^ 2 ∂μ :=
          mul_le_mul_of_nonneg_right hcΛ h0
      _ ≤ qp / qm * m₂ := mul_le_mul_of_nonneg_left hm2 (by positivity)
  have hrint' : Integrable (fun y : Euc d => lam ^ 2 * r (lam • y)) (μ.map fun x => lam⁻¹ • x) := by
    rw [tcq_integrable_map hc]
    have : (fun x : Euc d => lam ^ 2 * r (lam • lam⁻¹ • x)) = fun x => lam ^ 2 * r x := by
      ext x; rw [hmap]
    rw [this]; exact hrint.const_mul _
  have hrmean : ∫ y, lam ^ 2 * r (lam • y) ∂(μ.map fun x => lam⁻¹ • x) = 0 := by
    rw [tcq_integral_map hc]
    have : (fun x : Euc d => lam ^ 2 * r (lam • lam⁻¹ • x)) = fun x => lam ^ 2 * r x := by
      ext x; rw [hmap]
    rw [this, integral_const_mul, hrc, mul_zero]
  obtain ⟨χ, hsol, hcd, hder⟩ := h _ hBt _ hinv hint2 hmom _ hrcb.1 hrint' hrmean
  refine ⟨fun x => χ (lam⁻¹ • x), tcq_transfer hlam hl1 hqe hΛ (PoisFinal.rf_memCb_two hm hr) hsol,
    hcd.comp (contDiff_const_smul lam⁻¹), fun x => ?_⟩
  have hcbm0 : 0 ≤ cbNorm m (fun y => lam ^ 2 * r (lam • y)) := PoisFinal.rf_cb_nonneg _
  have hterm : ∀ j : Fin m, ‖iteratedFDeriv ℝ ((j : ℕ) + 1) (fun x => χ (lam⁻¹ • x)) (x j)‖
      ≤ Λ ^ m * ‖iteratedFDeriv ℝ ((j : ℕ) + 1) χ (lam⁻¹ • x j)‖ := fun j => by
    have h1 := tcq_norm_iter_dil hcd (n := m) (i := (j : ℕ) + 1) (by omega) 1 lam⁻¹ (x j)
    simp only [one_smul, abs_one, one_mul] at h1
    refine h1.trans ?_
    rw [abs_of_nonneg (inv_nonneg.2 hlam.le)]
    have : lam⁻¹ ^ ((j : ℕ) + 1) ≤ Λ ^ m :=
      calc lam⁻¹ ^ ((j : ℕ) + 1) ≤ Λ ^ ((j : ℕ) + 1) := pow_le_pow_left₀ (inv_nonneg.2 hlam.le) hΛ _
        _ ≤ Λ ^ m := pow_le_pow_right₀ hΛ1 (by omega)
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  calc ∑ j : Fin m, ‖iteratedFDeriv ℝ ((j : ℕ) + 1) (fun x => χ (lam⁻¹ • x)) (x j)‖
      ≤ ∑ j : Fin m, Λ ^ m * ‖iteratedFDeriv ℝ ((j : ℕ) + 1) χ (lam⁻¹ • x j)‖ :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = Λ ^ m * ∑ j : Fin m, ‖iteratedFDeriv ℝ ((j : ℕ) + 1) χ (lam⁻¹ • x j)‖ := by
        rw [Finset.mul_sum]
    _ ≤ Λ ^ m * (Cm0 * cbNorm m (fun y => lam ^ 2 * r (lam • y))) :=
        mul_le_mul_of_nonneg_left (hder fun j => lam⁻¹ • x j) (by positivity)
    _ ≤ Λ ^ m * (|Cm0| * cbNorm m r) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc Cm0 * cbNorm m (fun y => lam ^ 2 * r (lam • y)) ≤ |Cm0| * cbNorm m (fun y => lam ^ 2 * r (lam • y)) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) hcbm0
          _ ≤ |Cm0| * cbNorm m r := mul_le_mul_of_nonneg_left hrcb.2 (abs_nonneg _)
    _ = Λ ^ m * |Cm0| * cbNorm m r := by ring

end HRS.MS.TcQ

end
