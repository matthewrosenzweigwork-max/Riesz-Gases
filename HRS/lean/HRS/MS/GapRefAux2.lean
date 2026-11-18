import HRS.MS.GapRefAux1
import HRS.MS.LogReg

/-!
# GAP-1 (part 2): `GapRef` for the logarithmic thermal densities (`gap_drift`)

Supplement foundation packet GAP-1 (namespace `HRS.MS.Gap`, helper prefix `gap1_`), continuing `GapRefAux1`.

* `gap_of_logDensity`: a density `ρ = exp(-(q/2)‖x‖² + G)` with `G ∈ C^∞` having bounded derivatives of every
  positive order, `∫ρ = 1`, finite second moment, satisfies `GapRef d ρ q (∇G)`.  Generic: `q` and `G` abstract (the
  route for S4.4 with `s > 0` once `euc_thermal_regularity` supplies the derivative bounds of `g * ρ`).
* `gap_of_tilt`: the tilt `(1 + εψ) ρ` of such a density (`ψ ∈ C_c^∞`, `|ε||ψ| ≤ 1/2`, `∫ψρ = 0`) satisfies
  `GapRef` with `B = ∇(G + log(1 + εψ))`.
* `gap_gradient_log`: `∇ log ρ = -q x + B` (the drift of `weightedGen`, `Thermal.lean`).
* `gap_drift`: for `d ≥ 2`, `a, β > 0` and `hρ : IsStaticReference d 0 a β ψ ρ` (both constructors), there is `B` with
  `GapRef d ρ (a * β) B`: `ρ > 0`, `ρ ∈ C^∞`, `∇ρ = ρ (-(aβ) x + B)`, `B ∈ C_b^m` for every `m`, `∫ρ = 1` and
  `∫‖x‖²ρ < ∞`.  The thermal case uses `logThermal_bounds_proof` (two-sided Gaussian bound, via the rapid decay
  `lreg_rdec_of_le`), the thermal equation (`IsThermalDensity`, via `lreg_data`) and `logThermal_regularity_proof`
  (bullets 2-3: `g * ρ ∈ C^∞` with bounded derivatives of positive order).

Statement adjustments relative to the plan sketch: the conclusion is the packaged structure `GapRef` (`∃ B`), with
`B` implicitly `-β ∇(g*ρ_*) + ε ∇ψ/(1+εψ)` (see `gap_of_tilt`); the moment bound is `GapRef.moment2` together with
`gap_moment` of `GapRefAux1`.  No hypothesis was added to the frozen `IsStaticReference`.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
open HRS HRS.Whole HRS.MS.PoisKolm HRS.MS.PoisInv HRS.MS.LogReg HRS.MS.Can2

noncomputable section

namespace HRS.MS.Gap

variable {d : ℕ}

/-! ### Generic criteria -/

lemma gap1_contDiff_gradient {G : Euc d → ℝ} (hG : ContDiff ℝ ∞ G) (m : ℕ) :
    ContDiff ℝ m (gradient G) := by
  have h1 : ContDiff ℝ m (fderiv ℝ G) :=
    (contDiff_infty.1 hG (m + 1)).fderiv_right (m := m) (by norm_cast)
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp h1

lemma gap1_norm_iter_gradient {G : Euc d → ℝ} (j : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (gradient G) x‖ = ‖iteratedFDeriv ℝ (j + 1) G x‖ := by
  have : gradient G = ((InnerProductSpace.toDual ℝ (Euc d)).symm : _ ≃ₗᵢ[ℝ] _) ∘ fderiv ℝ G := rfl
  rw [this, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]

theorem gap_of_logDensity {q : ℝ} {G ρ : Euc d → ℝ} (hG : ContDiff ℝ ∞ G)
    (hGb : ∀ j : ℕ, 1 ≤ j → ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j G x‖ ≤ C)
    (hρ : ∀ x, ρ x = Real.exp (-(q / 2) * ‖x‖ ^ 2 + G x)) (hint : Integrable ρ)
    (h1 : ∫ x, ρ x = 1) (hm : Integrable (fun x => ‖x‖ ^ 2 * ρ x)) :
    GapRef d ρ q (gradient G) := by
  have hfun : ρ = fun x => Real.exp (-(q / 2) * ‖x‖ ^ 2 + G x) := funext hρ
  have hsm : ContDiff ℝ ∞ ρ := by
    rw [hfun]
    exact ((contDiff_const.mul (contDiff_norm_sq ℝ)).add hG).exp
  refine ⟨fun x => by rw [hρ]; exact Real.exp_pos _, hsm, hint, h1, hm, fun x => ?_, fun m => ?_⟩
  · -- the gradient identity
    have hd : HasFDerivAt (fun y : Euc d => -(q / 2) * ‖y‖ ^ 2 + G y)
        ((-(q / 2)) • (2 • innerSL ℝ x) + fderiv ℝ G x) x :=
      (((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul (-(q / 2))).add
        ((hG.differentiable (by simp) x).hasFDerivAt)
    have hρd : HasFDerivAt ρ (ρ x • ((-(q / 2)) • (2 • innerSL ℝ x) + fderiv ℝ G x)) x := by
      rw [hfun]
      exact hd.exp
    refine ext_inner_left ℝ fun v => ?_
    rw [kl_inner_gradient ρ x v, hρd.fderiv, inner_smul_right, inner_add_right, inner_smul_right,
      kl_inner_gradient G x v]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, innerSL_apply_apply,
      smul_eq_mul, nsmul_eq_mul]
    rw [real_inner_comm x v]
    push_cast
    ring
  · -- bounds on the derivatives of `B = ∇G`
    choose! C hC using hGb
    refine ⟨∑ j ∈ Finset.range (m + 1), |C (j + 1)|, gap1_contDiff_gradient hG m, fun j hj x => ?_⟩
    rw [gap1_norm_iter_gradient]
    refine (hC (j + 1) (by omega) x).trans ?_
    refine (le_abs_self _).trans ?_
    exact Finset.single_le_sum (f := fun j => |C (j + 1)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

/-- `∇ log ρ = -q x + B` (the drift of `weightedGen`). -/
theorem gap_gradient_log {q : ℝ} {B : Euc d → Euc d} {ρ : Euc d → ℝ} (hR : GapRef d ρ q B) (x : Euc d) :
    gradient (fun y => Real.log (ρ y)) x = -q • x + B x := by
  have hρd : DifferentiableAt ℝ ρ x := (hR.smooth.differentiable (by simp)) x
  have hne : ρ x ≠ 0 := (hR.pos x).ne'
  refine ext_inner_left ℝ fun v => ?_
  rw [kl_inner_gradient, (hρd.hasFDerivAt.log hne).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← kl_inner_gradient ρ x v, hR.grad x, inner_smul_right]
  field_simp

lemma gap1_bdd_of_compact {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (j : ℕ) :
    ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have h1 : Continuous fun y => ‖iteratedFDeriv ℝ j f y‖ :=
    (hf.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).norm
  have h2 : HasCompactSupport fun y => ‖iteratedFDeriv ℝ j f y‖ := (hc.iteratedFDeriv j).norm
  obtain ⟨S, hS⟩ := h1.bounded_above_of_compact_support h2
  exact ⟨S, fun y => by simpa using hS y⟩

/-- **Tilt criterion.**  If `ρ₀ = exp(-(q/2)‖x‖² + G)` is as in `gap_of_logDensity`, `ψ ∈ C_c^∞`,
`|ε||ψ| ≤ 1/2` and `∫ ψ ρ₀ = 0`, then `(1 + εψ) ρ₀` is a `GapRef` with `B = ∇(G + log(1 + εψ))`. -/
theorem gap_of_tilt {q ε : ℝ} {G ρ₀ ψ : Euc d → ℝ} (hG : ContDiff ℝ ∞ G)
    (hGb : ∀ j : ℕ, 1 ≤ j → ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j G x‖ ≤ C)
    (hρ : ∀ x, ρ₀ x = Real.exp (-(q / 2) * ‖x‖ ^ 2 + G x)) (hint : Integrable ρ₀)
    (h1 : ∫ x, ρ₀ x = 1) (hm : Integrable (fun x => ‖x‖ ^ 2 * ρ₀ x))
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hε : ∀ x, |ε| * |ψ x| ≤ 1 / 2)
    (hmean : ∫ x, ψ x * ρ₀ x = 0) :
    GapRef d (fun x => (1 + ε * ψ x) * ρ₀ x) q
      (gradient (fun x => G x + Real.log (1 + ε * ψ x))) := by
  have hlow : ∀ x, 1 / 2 ≤ 1 + ε * ψ x := fun x => by
    have h := hε x
    have : -(|ε| * |ψ x|) ≤ ε * ψ x := by rw [← abs_mul]; exact neg_abs_le _
    linarith
  have hpos : ∀ x, 1 + ε * ψ x ≠ 0 := fun x => by have := hlow x; positivity
  have hup : ∀ x, |1 + ε * ψ x| ≤ 3 / 2 := fun x => by
    have h := hε x
    have : ε * ψ x ≤ |ε| * |ψ x| := by rw [← abs_mul]; exact le_abs_self _
    rw [abs_of_nonneg (by linarith [hlow x])]; linarith
  set L : Euc d → ℝ := fun x => Real.log (1 + ε * ψ x) with hL
  have hLs : ContDiff ℝ ∞ L :=
    ContDiff.log (contDiff_const.add (contDiff_const.mul hψ)) hpos
  have hLc : HasCompactSupport L := by
    refine hψc.mono' ?_
    intro x hx
    refine subset_closure ?_
    by_contra h
    apply hx
    have : ψ x = 0 := Function.notMem_support.1 h
    simp [hL, this]
  have hG' : ContDiff ℝ ∞ (fun x => G x + L x) := hG.add hLs
  have hGb' : ∀ j : ℕ, 1 ≤ j → ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j (fun x => G x + L x) x‖ ≤ C := by
    intro j hj
    obtain ⟨C1, hC1⟩ := hGb j hj
    obtain ⟨C2, hC2⟩ := gap1_bdd_of_compact hLs hLc j
    refine ⟨C1 + C2, fun x => ?_⟩
    show ‖iteratedFDeriv ℝ j (G + L) x‖ ≤ C1 + C2
    rw [iteratedFDeriv_add_apply (contDiff_infty.1 hG j).contDiffAt (contDiff_infty.1 hLs j).contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add (hC1 x) (hC2 x))
  have hρc : Continuous ρ₀ := by
    have : ρ₀ = fun x => Real.exp (-(q / 2) * ‖x‖ ^ 2 + G x) := funext hρ
    rw [this]
    exact (((contDiff_const.mul (contDiff_norm_sq ℝ)).add hG).exp).continuous
  have hψcont : Continuous ψ := hψ.continuous
  obtain ⟨Cψ, hCψ⟩ : ∃ C : ℝ, ∀ x, ‖ψ x‖ ≤ C := by
    obtain ⟨C, hC⟩ := gap1_bdd_of_compact hψ hψc 0
    exact ⟨C, fun x => by simpa using hC x⟩
  have hfc : Continuous fun x : Euc d => (1 + ε * ψ x) * ρ₀ x :=
    (continuous_const.add (continuous_const.mul hψcont)).mul hρc
  have hint' : Integrable (fun x => (1 + ε * ψ x) * ρ₀ x) := by
    refine (hint.const_mul (3 / 2)).mono' hfc.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    have h0 : 0 ≤ ρ₀ x := by rw [hρ]; exact (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_right (hup x) h0
  have hψρ : Integrable (fun x => ψ x * ρ₀ x) := by
    refine (hint.const_mul Cψ).mono' (hψcont.mul hρc).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    have h0 : 0 ≤ ρ₀ x := by rw [hρ]; exact (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_right (by simpa using hCψ x) h0
  refine gap_of_logDensity hG' hGb' (fun x => ?_) hint' ?_ ?_
  · have h0 : 0 < 1 + ε * ψ x := by linarith [hlow x]
    have h2 := Real.exp_log h0
    rw [hρ]
    calc (1 + ε * ψ x) * Real.exp (-(q / 2) * ‖x‖ ^ 2 + G x)
        = Real.exp (Real.log (1 + ε * ψ x)) * Real.exp (-(q / 2) * ‖x‖ ^ 2 + G x) := by rw [h2]
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        ring
  · have e : ∀ x, (1 + ε * ψ x) * ρ₀ x = ρ₀ x + ε * (ψ x * ρ₀ x) := fun x => by ring
    simp_rw [e]
    rw [integral_add hint (hψρ.const_mul ε), integral_const_mul, hmean, h1]
    ring
  · refine ((hm.const_mul (3 / 2))).mono' ((continuous_norm.pow 2).mul hfc).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h0 : 0 ≤ ρ₀ x := by rw [hρ]; exact (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ ^ 2)]
    calc ‖x‖ ^ 2 * (|1 + ε * ψ x| * ρ₀ x) ≤ ‖x‖ ^ 2 * (3 / 2 * ρ₀ x) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hup x) h0) (by positivity)
      _ = 3 / 2 * (‖x‖ ^ 2 * ρ₀ x) := by ring

/-! ### The logarithmic thermal density -/

/-- Log-density data of `thermalDensity d 0 a β`: `ρ = exp(-(aβ/2)‖x‖² + G)` with `G = -β (g*ρ) - log Z`
smooth with bounded derivatives of every positive order; `ρ` is an integrable probability density with finite
second moment. -/
lemma gap1_thermal_data (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ G : Euc d → ℝ, ContDiff ℝ ∞ G ∧ (∀ j : ℕ, 1 ≤ j → ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j G x‖ ≤ C) ∧
      (∀ x, thermalDensity d 0 a β x = Real.exp (-((a * β) / 2) * ‖x‖ ^ 2 + G x)) ∧
      Integrable (thermalDensity d 0 a β) ∧ ∫ x, thermalDensity d 0 a β x = 1 ∧
      Integrable (fun x => ‖x‖ ^ 2 * thermalDensity d 0 a β x) := by
  obtain ⟨Z, c, C, hZ, hc, hC, hρ0, hρm, heq, hbd, hU⟩ := lreg_data hd ha hβ
  obtain ⟨-, hWs, hWb, -⟩ := logThermal_regularity_proof hd a β ha hβ
  have hP := (can2_isThermalDensity_log hd ha hβ).1
  set ρ := thermalDensity d 0 a β with hρ
  set W := HRS.Whole.convMeasure (rieszKernel d 0) (thermalMeasure d 0 a β) with hW
  have hdec : lreg_RDec ρ :=
    lreg_rdec_of_le ha hβ hρ0 (fun x => by simpa [mul_assoc] using (hbd x).2)
  obtain ⟨C2, hC2, hb2⟩ := lreg_bound_of_rdec hdec 2
  obtain ⟨C0, hC0, hb0⟩ := lreg_bound_of_rdec hdec 0
  have hmeas : AEStronglyMeasurable ρ volume := hρm.aestronglyMeasurable
  have hint : Integrable ρ := lreg_integrable_of_bound hmeas (C := C0) fun y => by simpa using hb0 y
  refine ⟨fun x => -β * W x - Real.log Z, (contDiff_const.mul hWs).sub contDiff_const, ?_, ?_, hint,
    hP.integral_one, ?_⟩
  · intro j hj
    obtain ⟨CW, hCW⟩ := hWb j hj
    refine ⟨β * CW, fun x => ?_⟩
    have e : (fun x => -β * W x - Real.log Z) = (fun x => (-β) • W x) + fun _ => -Real.log Z := by
      funext x; simp [sub_eq_add_neg]
    have hA : ContDiffAt ℝ j (fun x => (-β) • W x) x :=
      ((contDiff_infty.1 hWs j).const_smul (-β)).contDiffAt
    have hB : ContDiffAt ℝ j (fun _ : Euc d => -Real.log Z) x := contDiff_const.contDiffAt
    rw [e, iteratedFDeriv_add_apply hA hB, iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, add_zero,
      iteratedFDeriv_const_smul_apply' (contDiff_infty.1 hWs j).contDiffAt, norm_smul, Real.norm_eq_abs,
      abs_neg, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left (hCW x) hβ.le
  · intro x
    rw [heq x, ← hU x]
    have : -((a * β) / 2) * ‖x‖ ^ 2 + (-β * W x - Real.log Z) =
        -β * (a * ‖x‖ ^ 2 / 2 + W x) - Real.log Z := by ring
    show _ = Real.exp (-((a * β) / 2) * ‖x‖ ^ 2 + (-β * W x - Real.log Z))
    rw [this, Real.exp_sub, Real.exp_log hZ]
  · refine (lreg_phi_integrable.const_mul C2).mono'
      ((continuous_norm.pow 2).aestronglyMeasurable.mul hmeas) (Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ ρ y := hρ0 y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖y‖ ^ 2)]
    have h1 := hb2 y
    rw [Real.norm_of_nonneg h0] at h1
    have h3 : ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := by nlinarith [norm_nonneg y]
    calc ‖y‖ ^ 2 * ρ y ≤ (1 + ‖y‖) ^ 2 * ρ y := mul_le_mul_of_nonneg_right h3 h0
      _ ≤ C2 * lreg_phi d y := h1

/-- **`gap_drift`.**  For `d ≥ 2`, `a, β > 0` and any static reference `ρ` at `s = 0` (the thermal density or a
compact relative perturbation `(1 + εψ) ρ_*`), `ρ > 0` is a `C^∞` probability density with finite second moment,
`∇ρ = ρ (-(aβ) x + B)` and `B ∈ C_b^m` for every `m`
(`B = -β ∇(g*ρ_*) + ε ∇ψ/(1+εψ)`, see `gap_of_tilt`). -/
theorem gap_drift (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ψ ρ : Euc d → ℝ}
    (hρ : IsStaticReference d 0 a β ψ ρ) : ∃ B : Euc d → Euc d, GapRef d ρ (a * β) B := by
  obtain ⟨G, hG, hGb, heq, hint, h1, hm⟩ := gap1_thermal_data hd ha hβ
  have heq' : ∀ x, thermalDensity d 0 a β x = Real.exp (-((a * β) / 2) * ‖x‖ ^ 2 + G x) := heq
  cases hρ with
  | thermal => exact ⟨_, gap_of_logDensity hG hGb heq' hint h1 hm⟩
  | perturbed ε hε =>
    exact ⟨_, gap_of_tilt hG hGb heq' hint h1 hm hε.smooth hε.compactSupport hε.small hε.meanZero⟩

end HRS.MS.Gap

end
