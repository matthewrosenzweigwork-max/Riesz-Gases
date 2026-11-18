import HRS.MS.UniqM1
import HRS.PDE.ToolboxRd.Fourier

/-!
# N4a: Fourier interpolation between `L²` and `H¹` on `ℝ^d`

* `n4a_memSobolev`: `H¹ ⊆ H^r` for `0 ≤ r ≤ 1` (monotonicity of the weight `(1+4π²|ξ|²)^s`).
* `n4a_interp`: `‖u‖²_{H^r} ≤ ‖u‖²_{L²}^{1-r} ‖u‖²_{H¹}^r` (Hölder on `∫ w^r |û|²`).
* `n4a_interp_E`: the same bound for `sobolevNormE` in `ℝ≥0∞`.
* `n4a_interp_E_bound`: if `sobolevNormE 0 u ≤ ofReal a` and `sobolevNormE 1 u ≤ ofReal b`, then
  `sobolevNormE r u ≤ ofReal (a^(1-r) * b^r)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HRS.MS.UniqN4a

open HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- `H¹ ⊆ H^r` for `0 ≤ r ≤ 1`. -/
theorem n4a_memSobolev (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {u : Euc d → ℝ}
    (hu : HRS.PDE.ToolboxRd.MemSobolev 1 u) : HRS.PDE.ToolboxRd.MemSobolev r u :=
  memSobolev_mono hr1 hu

/-- Pointwise splitting `w^r f = (w f)^r · f^(1-r)` for `w, f ≥ 0`. -/
theorem n4a_split (r w f : ℝ) (hw : 0 ≤ w) (hf : 0 ≤ f) :
    w ^ r * f = (w * f) ^ r * f ^ (1 - r) := by
  have h1 : r + (1 - r) = 1 := by ring
  have h2 : f ^ r * f ^ (1 - r) = f := by
    rw [← Real.rpow_add' hf (by rw [h1]; norm_num), h1, Real.rpow_one]
  rw [Real.mul_rpow hw hf]
  calc w ^ r * f = w ^ r * (f ^ r * f ^ (1 - r)) := by rw [h2]
    _ = w ^ r * f ^ r * f ^ (1 - r) := by ring

/-- Hölder on an abstract measure space: `∫ w^r f ≤ (∫ w f)^r (∫ f)^(1-r)` for `0 < r < 1`
and `w, f ≥ 0` with `f`, `w f` integrable. -/
theorem n4a_holder_abs {α : Type*} [MeasurableSpace α] {μ : Measure α} {w f : α → ℝ} {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x)
    (hfI : Integrable f μ) (hwfI : Integrable (fun x => w x * f x) μ) :
    ∫ x, w x ^ r * f x ∂μ ≤ (∫ x, w x * f x ∂μ) ^ r * (∫ x, f x ∂μ) ^ (1 - r) := by
  have hr1' : (1 - r) ≠ 0 := (sub_pos.2 hr1).ne'
  have hwf : ∀ x, 0 ≤ w x * f x := fun x => mul_nonneg (hw x) (hf x)
  have hF1m : AEStronglyMeasurable (fun x => (w x * f x) ^ r) μ :=
    (hwfI.aestronglyMeasurable.aemeasurable.pow_const r).aestronglyMeasurable
  have hF2m : AEStronglyMeasurable (fun x => f x ^ (1 - r)) μ :=
    (hfI.aestronglyMeasurable.aemeasurable.pow_const (1 - r)).aestronglyMeasurable
  have hp0 : ENNReal.ofReal r⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hr0)).ne'
  have hq0 : ENNReal.ofReal (1 - r)⁻¹ ≠ 0 :=
    (ENNReal.ofReal_pos.2 (inv_pos.2 (sub_pos.2 hr1))).ne'
  have hF1 : MemLp (fun x => (w x * f x) ^ r) (ENNReal.ofReal r⁻¹) μ := by
    rw [← integrable_norm_rpow_iff hF1m hp0 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (inv_nonneg.2 hr0.le)]
    refine hwfI.congr (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hwf x) _), Real.rpow_rpow_inv (hwf x) hr0.ne']
  have hF2 : MemLp (fun x => f x ^ (1 - r)) (ENNReal.ofReal (1 - r)⁻¹) μ := by
    rw [← integrable_norm_rpow_iff hF2m hq0 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (inv_nonneg.2 (sub_pos.2 hr1).le)]
    refine hfI.congr (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hf x) _), Real.rpow_rpow_inv (hf x) hr1']
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ)
    (Real.HolderConjugate.inv_one_sub_inv hr0 hr1)
    (f := fun x => (w x * f x) ^ r) (g := fun x => f x ^ (1 - r))
    (Eventually.of_forall fun x => Real.rpow_nonneg (hwf x) _)
    (Eventually.of_forall fun x => Real.rpow_nonneg (hf x) _) hF1 hF2
  beta_reduce at hH
  have eM : ∫ x, (w x * f x) ^ r * f x ^ (1 - r) ∂μ = ∫ x, w x ^ r * f x ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact (n4a_split r (w x) (f x) (hw x) (hf x)).symm
  have eL : ∫ x, ((w x * f x) ^ r) ^ r⁻¹ ∂μ = ∫ x, w x * f x ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact Real.rpow_rpow_inv (hwf x) hr0.ne'
  have eZ : ∫ x, (f x ^ (1 - r)) ^ (1 - r)⁻¹ ∂μ = ∫ x, f x ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact Real.rpow_rpow_inv (hf x) hr1'
  rw [eM, eL, eZ] at hH
  simpa only [one_div, inv_inv] using hH

/-- Hölder interpolation of the squared Sobolev norms: `‖u‖²_{H^r} ≤ ‖u‖²_{L²}^{1-r} ‖u‖²_{H¹}^r`. -/
theorem n4a_interp (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {u : Euc d → ℝ} (hu : HRS.PDE.ToolboxRd.MemSobolev 1 u) :
    sobolevNormSq r u ≤ sobolevNormSq 0 u ^ (1 - r) * sobolevNormSq 1 u ^ r := by
  rcases hr0.eq_or_lt with h0 | hpos
  · subst h0
    simp
  rcases hr1.eq_or_lt with h1 | hlt
  · subst h1
    simp
  have hF : MemLp u 2 volume := hu.1
  have hI0 : Integrable (fun ξ : Euc d => ‖fourierL2 u ξ‖ ^ 2) volume :=
    integrable_norm_sq_fourierL2 hF
  have hI1 : Integrable (fun ξ : Euc d => wt ξ * ‖fourierL2 u ξ‖ ^ 2) volume := by
    have h := hu.2
    simp only [Real.rpow_one] at h
    exact h
  have H := n4a_holder_abs (μ := volume) (w := wt) (f := fun ξ : Euc d => ‖fourierL2 u ξ‖ ^ 2)
    (r := r) hpos hlt (fun ξ => (wt_pos ξ).le) (fun ξ => by positivity) hI0 hI1
  have e0 : sobolevNormSq 0 u = ∫ ξ : Euc d, ‖fourierL2 u ξ‖ ^ 2 := by
    rw [sobolevNormSq_eq]
    simp only [Real.rpow_zero, one_mul]
  have e1 : sobolevNormSq 1 u = ∫ ξ : Euc d, wt ξ * ‖fourierL2 u ξ‖ ^ 2 := by
    rw [sobolevNormSq_eq]
    simp only [Real.rpow_one]
  calc sobolevNormSq r u
      ≤ (∫ ξ : Euc d, wt ξ * ‖fourierL2 u ξ‖ ^ 2) ^ r * (∫ ξ : Euc d, ‖fourierL2 u ξ‖ ^ 2) ^ (1 - r) :=
        (sobolevNormSq_eq r u).le.trans H
    _ = sobolevNormSq 0 u ^ (1 - r) * sobolevNormSq 1 u ^ r := by
        rw [e0, e1]; ring

/-- Real square-root form of the interpolation bound. -/
theorem n4a_sqrt_interp {A B C r : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (C_le : C ≤ A ^ (1 - r) * B ^ r) :
    Real.sqrt C ≤ Real.sqrt A ^ (1 - r) * Real.sqrt B ^ r := by
  have key : Real.sqrt A ^ (1 - r) * Real.sqrt B ^ r = Real.sqrt (A ^ (1 - r) * B ^ r) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      Real.mul_rpow (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _),
      ← Real.rpow_mul hA, ← Real.rpow_mul hB, ← Real.rpow_mul hA, ← Real.rpow_mul hB]
    ring_nf
  rw [key]
  exact Real.sqrt_le_sqrt C_le

/-- Interpolation of `sobolevNormE` in `ℝ≥0∞`: `‖u‖_{H^r} ≤ ‖u‖_{L²}^{1-r} ‖u‖_{H¹}^r`. -/
theorem n4a_interp_E (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {u : Euc d → ℝ} (hu : HRS.PDE.ToolboxRd.MemSobolev 1 u) :
    sobolevNormE r u ≤ sobolevNormE 0 u ^ (1 - r) * sobolevNormE 1 u ^ r := by
  have hA : 0 ≤ sobolevNormSq 0 u := by
    rw [sobolevNormSq_eq]
    exact integral_nonneg fun ξ => mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (by positivity)
  have hB : 0 ≤ sobolevNormSq 1 u := by
    rw [sobolevNormSq_eq]
    exact integral_nonneg fun ξ => mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (by positivity)
  have hE0 : sobolevNormE 0 u = ENNReal.ofReal (Real.sqrt (sobolevNormSq 0 u)) := by
    unfold sobolevNormE
    rw [if_pos (HRS.MS.UniqM1.memSobolev_zero_iff.2 hu.1)]
  have hE1 : sobolevNormE 1 u = ENNReal.ofReal (Real.sqrt (sobolevNormSq 1 u)) := by
    unfold sobolevNormE
    rw [if_pos hu]
  have hEr : sobolevNormE r u = ENNReal.ofReal (Real.sqrt (sobolevNormSq r u)) := by
    unfold sobolevNormE
    rw [if_pos (n4a_memSobolev r hr0 hr1 hu)]
  rw [hEr, hE0, hE1,
    ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg (sobolevNormSq 0 u))
      (by linarith : (0:ℝ) ≤ 1 - r),
    ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg (sobolevNormSq 1 u)) hr0,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.sqrt_nonneg (sobolevNormSq 0 u)) (1 - r))]
  apply ENNReal.ofReal_le_ofReal
  exact n4a_sqrt_interp hA hB (n4a_interp r hr0 hr1 hu)

/-- Corollary: bounds on the endpoint norms give a bound at order `r`. -/
theorem n4a_interp_E_bound (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {u : Euc d → ℝ}
    (hu : HRS.PDE.ToolboxRd.MemSobolev 1 u) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h0 : sobolevNormE 0 u ≤ ENNReal.ofReal a) (h1 : sobolevNormE 1 u ≤ ENNReal.ofReal b) :
    sobolevNormE r u ≤ ENNReal.ofReal (a ^ (1 - r) * b ^ r) := by
  calc sobolevNormE r u ≤ sobolevNormE 0 u ^ (1 - r) * sobolevNormE 1 u ^ r :=
        n4a_interp_E r hr0 hr1 hu
    _ ≤ (ENNReal.ofReal a) ^ (1 - r) * (ENNReal.ofReal b) ^ r :=
        mul_le_mul' (ENNReal.rpow_le_rpow h0 (by linarith : (0:ℝ) ≤ 1 - r))
          (ENNReal.rpow_le_rpow h1 hr0)
    _ = ENNReal.ofReal (a ^ (1 - r) * b ^ r) := by
        rw [ENNReal.ofReal_rpow_of_nonneg ha (by linarith : (0:ℝ) ≤ 1 - r),
          ENNReal.ofReal_rpow_of_nonneg hb hr0,
          ENNReal.ofReal_mul (Real.rpow_nonneg ha _)]

end HRS.MS.UniqN4a
