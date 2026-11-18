import HRS.Whole.MovtrAux6

/-!
# MOV-B1 (1): potential form of the force `movForce d s h = ∇(g * h)` (S6.1, step 2)

Namespace `HRS.MS.MovForce`, prefix `mv1_`.  Infrastructure lemmas (not manuscript rows).

For `h ∈ C¹(ℝ^d)` with Gaussian bounds `|h y| ≤ C e^{-c‖y‖²}`, `‖Dh y‖ ≤ C e^{-c‖y‖²}` and
`g = rieszKernel d s`, `0 ≤ s < d`, `1 ≤ d` (the brief asks `2 ≤ d`; `1 ≤ d` is all that is used):

* `mv1_hasFDerivAt_convFun`: `convFun g h` is Fréchet differentiable, `D(g*h) = ∫ g(z) Dh(x-z) dz`
  (differentiation under the integral on the `h` side only; no cancellation convention needed);
* `mv1_force_eq_grad`: `movForce d s h x = gradient (convFun g h) x` (cancellation-convention force
  is the gradient of the potential), via `movtr_hasDerivAt_potential` and uniqueness of derivatives;
* `mv1_force_eq_conv_grad`: `(movForce d s h x) i = convFun g (∂_i h) x`;
* `mv1_force_contDiff`: `h ∈ C^{k+1}` with Gaussian bounds of all `D^j h`, `j ≤ k+1`, gives
  `movForce d s h ∈ C^k` (and the `C^∞` version).

Junk-value traps: every integral used is proved integrable (Gaussian majorant times the integrable
majorant of `g`), `movForce` is a Bochner integral with no integrability hypothesis, but we only
use it through `movtr_hasDerivAt_potential` which proves integrability.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovForce

open HRS.Whole

variable {d : ℕ}

/-- Gaussian bounds on `D^j h` for all `j ≤ k`. -/
def MovGauss (k : ℕ) (h : Euc d → ℝ) : Prop :=
  ∀ j : ℕ, j ≤ k → ∃ C c : ℝ, 0 < c ∧ ∀ x, ‖iteratedFDeriv ℝ j h x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2)

/-- `convFun k f x = ∫ z, k z * f (x - z)`. -/
lemma mv1_convFun_eq (k f : Euc d → ℝ) (x : Euc d) :
    HRS.Whole.convFun k f x = ∫ z, k z * f (x - z) := by
  unfold HRS.Whole.convFun
  rw [← integral_sub_left_eq_self (fun z => k z * f (x - z)) volume x]
  simp

/-- Joint Gaussian bound for `h` and `Dh` from `MovGauss 1`. -/
lemma mv1_gauss01 {h : Euc d → ℝ} (hg : MovGauss 1 h) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ (∀ y, |h y| ≤ C * Real.exp (-c * ‖y‖ ^ 2)) ∧
      (∀ y, ‖fderiv ℝ h y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) := by
  obtain ⟨C0, c0, hc0, h0⟩ := hg 0 (by norm_num)
  obtain ⟨C1, c1, hc1, h1⟩ := hg 1 le_rfl
  have hC0 : 0 ≤ C0 := by
    have := h0 0
    simp at this
    exact le_trans (abs_nonneg _) this
  have hC1 : 0 ≤ C1 := by
    have := h1 0
    simp at this
    exact le_trans (norm_nonneg _) this
  refine ⟨max C0 C1, min c0 c1, le_max_of_le_left hC0, lt_min hc0 hc1, ?_, ?_⟩
  · intro y
    have := h0 y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    refine this.trans ?_
    have hexp : Real.exp (-c0 * ‖y‖ ^ 2) ≤ Real.exp (-(min c0 c1) * ‖y‖ ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [min_le_left c0 c1, sq_nonneg ‖y‖]
    calc C0 * Real.exp (-c0 * ‖y‖ ^ 2) ≤ max C0 C1 * Real.exp (-c0 * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (le_max_of_le_left hC0)
  · intro y
    have := h1 y
    rw [norm_iteratedFDeriv_one] at this
    refine this.trans ?_
    have hexp : Real.exp (-c1 * ‖y‖ ^ 2) ≤ Real.exp (-(min c0 c1) * ‖y‖ ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [min_le_right c0 c1, sq_nonneg ‖y‖]
    calc C1 * Real.exp (-c1 * ‖y‖ ^ 2) ≤ max C0 C1 * Real.exp (-c1 * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (le_max_of_le_left hC0)

section Generic

variable {c : ℝ} {k : Euc d → ℝ} {B : Euc d → ℝ}

/-- Pointwise domination of `k z * ρ (x' - z)` by the common majorant. -/
lemma mv1_dom_pt0 {C R : ℝ} (hc : 0 < c) (hC : 0 ≤ C) {ρ : Euc d → ℝ}
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2)) {x' : Euc d} (hx : ‖x'‖ ≤ R)
    {z : Euc d} (hz : |k z| ≤ B z) :
    ‖k z * ρ (x' - z)‖ ≤ C * Real.exp (c * R ^ 2) * (B z * Real.exp (-(c / 2) * ‖z‖ ^ 2)) := by
  have h2 := movtr_gauss_shift hc hx z
  have hBn : 0 ≤ B z := (abs_nonneg _).trans hz
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1' := h0 (x' - z)
  calc |k z| * |ρ (x' - z)| ≤ B z * (C * (Real.exp (c * R ^ 2) * Real.exp (-(c / 2) * ‖z‖ ^ 2))) :=
        mul_le_mul hz (h1'.trans (mul_le_mul_of_nonneg_left h2 hC)) (abs_nonneg _) hBn
    _ = _ := by ring

/-- Pointwise domination of `k z • Dρ (x' - z)` by the common majorant. -/
lemma mv1_dom_pt1 {C R : ℝ} (hc : 0 < c) (hC : 0 ≤ C) {ρ : Euc d → ℝ}
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) {x' : Euc d} (hx : ‖x'‖ ≤ R)
    {z : Euc d} (hz : |k z| ≤ B z) :
    ‖k z • fderiv ℝ ρ (x' - z)‖ ≤ C * Real.exp (c * R ^ 2) * (B z * Real.exp (-(c / 2) * ‖z‖ ^ 2)) := by
  have h2 := movtr_gauss_shift hc hx z
  have hBn : 0 ≤ B z := (abs_nonneg _).trans hz
  rw [norm_smul, Real.norm_eq_abs]
  have h1' := h1 (x' - z)
  calc |k z| * ‖fderiv ℝ ρ (x' - z)‖
      ≤ B z * (C * (Real.exp (c * R ^ 2) * Real.exp (-(c / 2) * ‖z‖ ^ 2))) :=
        mul_le_mul hz (h1'.trans (mul_le_mul_of_nonneg_left h2 hC)) (norm_nonneg _) hBn
    _ = _ := by ring

lemma mv1_ball_bound (x : Euc d) {x' : Euc d} (hx' : x' ∈ Metric.ball x 1) :
    ‖x'‖ ≤ ‖x‖ + 1 := by
  rw [Metric.mem_ball, dist_eq_norm] at hx'
  calc ‖x'‖ = ‖x + (x' - x)‖ := by simp
    _ ≤ ‖x‖ + ‖x' - x‖ := norm_add_le _ _
    _ ≤ ‖x‖ + 1 := by linarith

/-- Fréchet derivative of `x ↦ ∫ k(z) ρ(x - z) dz`. -/
lemma mv1_hasFDerivAt_conv (hc : 0 < c) (hk : AEStronglyMeasurable k volume)
    (hB : ∀ᵐ z, |k z| ≤ B z)
    (hBint : Integrable (fun z => B z * Real.exp (-(c / 2) * ‖z‖ ^ 2))) {C : ℝ} (hC : 0 ≤ C)
    {ρ : Euc d → ℝ} (hρ1 : ContDiff ℝ 1 ρ)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (h1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) :
    HasFDerivAt (fun x' => ∫ z, k z * ρ (x' - z)) (∫ z, k z • fderiv ℝ ρ (x - z)) x ∧
      Integrable (fun z => k z • fderiv ℝ ρ (x - z)) := by
  have hρc : Continuous ρ := hρ1.continuous
  have hdiff : Differentiable ℝ ρ := hρ1.differentiable (by norm_num)
  have hfd : Continuous (fderiv ℝ ρ) := hρ1.continuous_fderiv (by norm_num)
  set R : ℝ := ‖x‖ + 1 with hR
  have hmeasF : ∀ x' : Euc d, AEStronglyMeasurable (fun z => k z * ρ (x' - z)) volume := fun x' =>
    hk.mul (hρc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hint0 : Integrable (fun z => k z * ρ (x - z)) :=
    movtr_integrable_of_gauss_bound hc hk hB hBint hC hρc (x' := x) (R := R) (by simp [hR]) h0
  have hmeasF' : AEStronglyMeasurable (fun z => k z • fderiv ℝ ρ (x - z)) volume :=
    hk.smul (hfd.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hbd : Integrable (fun z => C * Real.exp (c * R ^ 2) *
      (B z * Real.exp (-(c / 2) * ‖z‖ ^ 2))) := hBint.const_mul _
  have hint1 : Integrable (fun z => k z • fderiv ℝ ρ (x - z)) := by
    refine Integrable.mono' hbd hmeasF' ?_
    filter_upwards [hB] with z hz
    exact mv1_dom_pt1 (k := k) (B := B) hc hC h1 (x' := x) (R := R) (by simp [hR]) hz
  refine ⟨?_, hint1⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun x' z => k z * ρ (x' - z)) (F' := fun x' z => k z • fderiv ℝ ρ (x' - z))
    (bound := fun z => C * Real.exp (c * R ^ 2) * (B z * Real.exp (-(c / 2) * ‖z‖ ^ 2)))
    (x₀ := x) (s := Metric.ball x 1) (Metric.ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall hmeasF) hint0 hmeasF' ?_ hbd ?_
  · filter_upwards [hB] with z hz x' hx'
    exact mv1_dom_pt1 (k := k) (B := B) hc hC h1 (mv1_ball_bound x hx') hz
  · refine Filter.Eventually.of_forall fun z x' _ => ?_
    have h2 : HasFDerivAt (fun x' : Euc d => x' - z) (ContinuousLinearMap.id ℝ (Euc d)) x' :=
      (hasFDerivAt_id x').sub_const z
    have h3 := (hdiff (x' - z)).hasFDerivAt.comp x' h2
    have h4 := h3.const_mul (k z)
    refine h4.congr_fderiv ?_
    ext v
    simp

/-- Continuity of `x ↦ ∫ k(z) ρ(x - z) dz` for continuous Gaussian-bounded `ρ`. -/
lemma mv1_continuous_conv (hc : 0 < c) (hk : AEStronglyMeasurable k volume)
    (hB : ∀ᵐ z, |k z| ≤ B z)
    (hBint : Integrable (fun z => B z * Real.exp (-(c / 2) * ‖z‖ ^ 2))) {C : ℝ} (hC : 0 ≤ C)
    {ρ : Euc d → ℝ} (hρc : Continuous ρ)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2)) :
    Continuous (fun x' => ∫ z, k z * ρ (x' - z)) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  set R : ℝ := ‖x‖ + 1 with hR
  refine continuousAt_of_dominated (μ := volume)
    (F := fun x' z => k z * ρ (x' - z))
    (bound := fun z => C * Real.exp (c * R ^ 2) * (B z * Real.exp (-(c / 2) * ‖z‖ ^ 2)))
    (Filter.Eventually.of_forall fun x' =>
      hk.mul (hρc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable) ?_
    (hBint.const_mul _) ?_
  · filter_upwards [Metric.ball_mem_nhds x one_pos] with x' hx'
    filter_upwards [hB] with z hz
    exact mv1_dom_pt0 (k := k) (B := B) hc hC h0 (mv1_ball_bound x hx') hz
  · refine Filter.Eventually.of_forall fun z => ?_
    exact (continuous_const.mul (hρc.comp (continuous_id.sub continuous_const))).continuousAt

end Generic

section Riesz

variable {s : ℝ}

/-- The data on `g = rieszKernel d s` needed for the generic lemmas. -/
lemma mv1_g_data (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {c : ℝ} (hc : 0 < c) :
    AEStronglyMeasurable (rieszKernel d s) volume ∧
      (∀ᵐ z : Euc d, |rieszKernel d s z| ≤ 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) ∧
      Integrable (fun z : Euc d => (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) *
        Real.exp (-(c / 2) * ‖z‖ ^ 2)) := by
  have hgm : Measurable (rieszKernel d s) := by
    rw [← movtr_gEps_zero d s]; exact movtr_gEps_measurable s 0
  refine ⟨hgm.aestronglyMeasurable, ?_,
    movtr_majorant_integrable hd hs0 hsd (c := c / 2) (by positivity)⟩
  filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
  rw [← movtr_gEps_zero d s]
  exact movtr_gEps_abs_le hs0 le_rfl zero_le_one hz

/-- `convFun g h` is Fréchet differentiable with `D(g*h)(x) e = ∫ g(z) Dh(x-z) e dz`. -/
theorem mv1_hasFDerivAt_convFun (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {c C : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) {h : Euc d → ℝ} (hh : ContDiff ℝ 1 h)
    (h0 : ∀ y, |h y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (h1 : ∀ y, ‖fderiv ℝ h y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) :
    ∃ L : Euc d →L[ℝ] ℝ, HasFDerivAt (HRS.Whole.convFun (rieszKernel d s) h) L x ∧
      (∀ e, L e = ∫ z, rieszKernel d s z * fderiv ℝ h (x - z) e) ∧
      ∀ e, Integrable (fun z => rieszKernel d s z * fderiv ℝ h (x - z) e) := by
  obtain ⟨hk, hB, hBint⟩ := mv1_g_data (d := d) hd hs0 hsd hc
  obtain ⟨hF, hint⟩ := mv1_hasFDerivAt_conv hc hk hB hBint hC hh h0 h1 x
  refine ⟨∫ z, rieszKernel d s z • fderiv ℝ h (x - z), ?_, fun e => ?_, fun e => ?_⟩
  · have : HRS.Whole.convFun (rieszKernel d s) h = fun x' => ∫ z, rieszKernel d s z * h (x' - z) :=
      funext fun x' => mv1_convFun_eq _ _ x'
    rw [this]; exact hF
  · rw [ContinuousLinearMap.integral_apply hint]
    simp
  · simpa using (ContinuousLinearMap.apply ℝ ℝ e).integrable_comp hint

/-- The cancellation-convention force is the gradient of the potential `g * h`. -/
theorem mv1_force_eq_grad (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {c C : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) {h : Euc d → ℝ} (hh : ContDiff ℝ 1 h)
    (h0 : ∀ y, |h y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (h1 : ∀ y, ‖fderiv ℝ h y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) :
    movForce d s h x = gradient (HRS.Whole.convFun (rieszKernel d s) h) x ∧
      DifferentiableAt ℝ (HRS.Whole.convFun (rieszKernel d s) h) x := by
  obtain ⟨L, hL, -, -⟩ := mv1_hasFDerivAt_convFun hd hs0 hsd hc hC hh h0 h1 x
  refine ⟨?_, hL.differentiableAt⟩
  ext i
  rw [movtr_gradient_apply, hL.fderiv]
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
  have hline : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const e).const_add x
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => HRS.Whole.convFun (rieszKernel d s) h (x + t • e)) (L e) 0 := by
    have hL' : HasFDerivAt (HRS.Whole.convFun (rieszKernel d s) h) L (x + (0:ℝ) • e) := by
      simpa using hL
    exact hL'.comp_hasDerivAt (0:ℝ) hline
  have h3 := movtr_hasDerivAt_potential hd hs0 hsd hc hC hh h0 h1 x i
  exact h3.unique h2

/-- `(∇g * h)_i = g * ∂_i h` (cancellation convention on the left). -/
theorem mv1_force_eq_conv_grad (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {c C : ℝ} (hc : 0 < c)
    (hC : 0 ≤ C) {h : Euc d → ℝ} (hh : ContDiff ℝ 1 h)
    (h0 : ∀ y, |h y| ≤ C * Real.exp (-c * ‖y‖ ^ 2))
    (h1 : ∀ y, ‖fderiv ℝ h y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) (i : Fin d) :
    (movForce d s h x) i =
      HRS.Whole.convFun (rieszKernel d s) (fun y => fderiv ℝ h y (EuclideanSpace.single i 1)) x := by
  obtain ⟨L, hL, hLe, -⟩ := mv1_hasFDerivAt_convFun hd hs0 hsd hc hC hh h0 h1 x
  rw [(mv1_force_eq_grad hd hs0 hsd hc hC hh h0 h1 x).1, movtr_gradient_apply, hL.fderiv, hLe,
    mv1_convFun_eq]

end Riesz

end HRS.MS.MovForce
