import HRS.MS.ThCorrDefs
import HRS.MS.EucRegH
import HRS.MS.LogReg
import HRS.MS.CanThmAux1
import HRS.MS.ThCorrDilAux2

/-!
# TC-1: drift structure of the thermal generator (S4.4, step 9)

Namespace `HRS.MS.Tc1`, helper prefix `tc1_`.  Write `U = convMeasure (rieszKernel d s) (thermalMeasure d s a β)`,
`ρ = thermalDensity d s a β`, `μ = thermalMeasure d s a β`, `B = -β • ∇U`.

* `tc1_U_smooth`: `U ∈ C^∞` for `0 ≤ s < d` (regularity theorems of S3.4 / S4.1).
* `tc1_gen_eq`: `thermalGen d s a β χ x = poissonOp (fun x => -(a β) • x + B x) χ x` as soon as `U` is differentiable
  (no regularity of `χ` is needed: it is an identity between the two defining expressions); `tc1_gen_eq_thermal`
  discharges the differentiability of `U` for the thermal data.
* `tc1_grad_rho`: `∇ρ = ρ • (-(aβ) x + B)` (from the thermal equation `ρ = e^{-β(V+U)}/Z`).
* `tc1_B_eq`: any `B'` with `GapRef d ρ (aβ) B'` equals `B` (since `ρ > 0`).
* `tc1_drift_data`: from `TcDrift d ρ (β a) Mb m₂ m` (the output of `tcu_uniform_*`) one gets, for the explicit drift
  `B = -β • ∇U`: `HasCbBound m Mb B`, `IsInvariantMeasure (-(aβ) x + B) μ`, `∫ ‖x‖² dμ ≤ m₂` and integrability of `‖x‖²`;
  exactly the hypotheses of `tcq_affine_poisson_higher` (`ThCorrDilAux2.lean`) with `q = a β`.
* `tc1_poisson_thermal`: the two combined: constants `C, Cm` depending only on `qm, qp, Mb, m₂, m, d` (not on `s, a, β`)
  such that for thermal data with `a β ∈ [qm, qp]` and `TcDrift`, every centred `r ∈ C_b^m` has a solution `χ` of
  the Poisson equation with `thermalGen d s a β χ = r` everywhere.

Statement adjustments relative to the plan sketch: `tc1_gapRef` is replaced by `tc1_B_eq` + `tc1_drift_data`
(the `GapRef` structure is already part of `TcDrift`, so only the identification of its drift with `-β ∇U` is needed).
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
open HRS HRS.Whole

noncomputable section

namespace HRS.MS.Tc1

variable {d : ℕ}

theorem tc1_hasFDeriv_conf (a : ℝ) (x : Euc d) :
    HasFDerivAt (confinement a) (a • innerSL ℝ x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul (a / 2)
  have e : (confinement a) = fun y : Euc d => a / 2 * ‖y‖ ^ 2 := by
    funext y; unfold confinement; ring
  rw [e]
  convert h using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem tc1_gradient_conf_add {U : Euc d → ℝ} {x : Euc d} (hU : DifferentiableAt ℝ U x) (a : ℝ) :
    gradient (fun y => confinement a y + U y) x = a • x + gradient U x := by
  refine ext_inner_left ℝ fun v => ?_
  have h : HasFDerivAt (fun y => confinement a y + U y) (a • innerSL ℝ x + fderiv ℝ U x) x :=
    (tc1_hasFDeriv_conf a x).add hU.hasFDerivAt
  rw [HRS.MS.PoisKolm.kl_inner_gradient _ x v, h.fderiv, inner_add_right, inner_smul_right,
    HRS.MS.PoisKolm.kl_inner_gradient U x v]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
    smul_eq_mul]
  rw [real_inner_comm x v]

/-- the identity `L = -Δ + β ∇(V+U)·∇` equals `poissonOp (-(aβ) x - β ∇U)`. -/
theorem tc1_gen_eq {s a β : ℝ}
    (hU : Differentiable ℝ (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)))
    (χ : Euc d → ℝ) (x : Euc d) :
    thermalGen d s a β χ x = poissonOp (fun x => -(a * β) • x + (-β) • gradient
      (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x) χ x := by
  unfold thermalGen poissonOp
  rw [tc1_gradient_conf_add (hU x) a]
  simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
  ring

theorem tc1_U_smooth (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) (hβ : 0 < β) :
    ContDiff ℝ ∞ (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) := by
  rcases hs0.eq_or_lt with h0 | h0
  · subst h0
    exact (HRS.MS.LogReg.logThermal_regularity_proof hd a β ha hβ).2.1
  · exact (HRS.MS.Thm.euc_thermal_regularity_proof hd h0 hsd a β ha hβ).2.1

theorem tc1_gen_eq_thermal (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) (hβ : 0 < β)
    (χ : Euc d → ℝ) (x : Euc d) :
    thermalGen d s a β χ x = poissonOp (fun x => -(a * β) • x + (-β) • gradient
      (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x) χ x :=
  tc1_gen_eq ((tc1_U_smooth hd hs0 hsd ha hβ).differentiable (by simp)) χ x

theorem tc1_thermal_eq (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) (hβ : 0 < β) :
    HRS.Whole.IsThermalDensity (rieszKernel d s) (confinement a) β (thermalDensity d s a β) := by
  rcases hs0.eq_or_lt with h0 | h0
  · subst h0
    exact HRS.MS.Can2.can2_isThermalDensity_log hd ha hβ
  · exact HRS.MS.Can2.can2_isThermalDensity_pos hd h0 hsd ha hβ

theorem tc1_grad_rho (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) (hβ : 0 < β)
    (x : Euc d) :
    gradient (thermalDensity d s a β) x = thermalDensity d s a β x •
      (-(a * β) • x + (-β) • gradient (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x) := by
  have hU : DifferentiableAt ℝ (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x :=
    ((tc1_U_smooth hd hs0 hsd ha hβ).differentiable (by simp)) x
  set U := HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β) with hUdef
  have hth := (tc1_thermal_eq hd hs0 hsd ha hβ).2
  set Z := ∫ y, Real.exp (-β * (confinement a y + HRS.Whole.convMeasure (rieszKernel d s)
    (HRS.Whole.withDensityReal (thermalDensity d s a β)) y)) with hZ
  have hfun : thermalDensity d s a β = fun y => Z⁻¹ * Real.exp (-β * (confinement a y + U y)) := by
    funext y; rw [hth y, div_eq_inv_mul]; rfl
  have hE : HasFDerivAt (fun y => -β * (confinement a y + U y))
      ((-β) • (a • innerSL ℝ x + fderiv ℝ U x)) x :=
    (((tc1_hasFDeriv_conf a x).add hU.hasFDerivAt).const_mul (-β))
  have hρ := (hE.exp).const_mul Z⁻¹
  refine ext_inner_left ℝ fun v => ?_
  rw [HRS.MS.PoisKolm.kl_inner_gradient _ x v, inner_smul_right, inner_add_right, inner_smul_right,
    inner_smul_right, HRS.MS.PoisKolm.kl_inner_gradient U x v, real_inner_comm x v]
  have hf := hρ.fderiv
  rw [← hfun] at hf
  rw [hf, hfun]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, innerSL_apply_apply,
    smul_eq_mul]
  ring

theorem tc1_B_eq (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) (hβ : 0 < β)
    {B : Euc d → Euc d} (hR : HRS.MS.Gap.GapRef d (thermalDensity d s a β) (a * β) B) :
    B = fun x => (-β) • gradient (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x := by
  funext x
  have h := hR.grad x
  rw [tc1_grad_rho hd hs0 hsd ha hβ x] at h
  have h2 := smul_right_injective (Euc d) (hR.pos x).ne' h
  exact (add_left_cancel h2).symm

/-- Drift data for the thermal density from `TcDrift` (output of `tcu_uniform_*`): the explicit drift
`B = -β • ∇U` has the `C_b^m` bound `Mb`, `μ` is invariant for `-(aβ) x + B`, and the second moment of `μ` is `≤ m₂`. -/
theorem tc1_drift_data (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) (hβ : 0 < β)
    {Mb m₂ : ℝ} {m : ℕ}
    (h : HRS.MS.TcDefs.TcDrift d (thermalDensity d s a β) (β * a) Mb m₂ m) :
    HasCbBound m Mb (fun x => (-β) • gradient
      (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x) ∧
    IsInvariantMeasure (fun x => -(a * β) • x + (-β) • gradient
      (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x) (thermalMeasure d s a β) ∧
    Integrable (fun x : Euc d => ‖x‖ ^ 2) (thermalMeasure d s a β) ∧
    ∫ x, ‖x‖ ^ 2 ∂(thermalMeasure d s a β) ≤ m₂ := by
  obtain ⟨B, hR, hcb⟩ := h.gap
  rw [mul_comm β a] at hR
  have hB := tc1_B_eq hd hs0 hsd ha hβ hR
  subst hB
  obtain ⟨-, hint, hmom⟩ := HRS.MS.Gap.gap_moment hR
  refine ⟨hcb, HRS.MS.Gap.gap_invariant hR, hint, ?_⟩
  unfold thermalMeasure
  rw [hmom]
  exact h.moment

/-- **TC-1 + TC-Q.**  Uniform Poisson solve for thermal data: `C, Cm` are quantified before `s, a, β, r`. -/
theorem tc1_poisson_thermal (hd : 2 ≤ d) (qm qp Mb m₂ : ℝ) (hqm : 0 < qm) (m : ℕ) (hm : 2 ≤ m) :
    ∃ C Cm : ℝ, ∀ (s a β : ℝ), 0 ≤ s → s < d → 0 < a → 0 < β → qm ≤ a * β → a * β ≤ qp →
      HRS.MS.TcDefs.TcDrift d (thermalDensity d s a β) (β * a) Mb m₂ m →
      ∀ r : Euc d → ℝ, MemCb m r → Integrable r (thermalMeasure d s a β) →
        ∫ x, r x ∂(thermalMeasure d s a β) = 0 →
        ∃ χ : Euc d → ℝ, ContDiff ℝ m χ ∧ Integrable χ (thermalMeasure d s a β) ∧
          ∫ x, χ x ∂(thermalMeasure d s a β) = 0 ∧ (∀ x, thermalGen d s a β χ x = r x) ∧
          (∀ x, |χ x| ≤ C * cbNorm 2 r * (1 + Real.log (2 + ‖x‖))) ∧
          (∀ x y, ‖gradient χ x‖ + ‖iteratedFDeriv ℝ 2 χ y‖ ≤ C * cbNorm 2 r) ∧
          ∀ x : Fin m → Euc d,
            ∑ j : Fin m, ‖iteratedFDeriv ℝ ((j : ℕ) + 1) χ (x j)‖ ≤ Cm * cbNorm m r := by
  obtain ⟨C, Cm, h⟩ := HRS.MS.TcQ.tcq_affine_poisson_higher (d := d) (by omega) qm qp Mb m₂ hqm m hm
  refine ⟨C, Cm, fun s a β hs0 hsd ha hβ hq1 hq2 hdr r hr hri hrc => ?_⟩
  obtain ⟨hcb, hinv, hint, hmom⟩ := tc1_drift_data hd hs0 hsd ha hβ hdr
  obtain ⟨χ, ⟨-, hi, hc, heq, hlog, hgr⟩, hcd, hder⟩ :=
    h (a * β) ⟨hq1, hq2⟩ _ hcb _ hinv hint hmom r hr hri hrc
  exact ⟨χ, hcd, hi, hc, fun x => by rw [tc1_gen_eq_thermal hd hs0 hsd ha hβ]; exact heq x, hlog, hgr, hder⟩

end HRS.MS.Tc1

end
