import HRS.MS.CzElemAux2

/-!
# ELEM-A, part 3: Taylor remainder, `C_b²` data, coordinate kernels (towards (iii-c))

Packet ELEM-A (CZ development), namespace `HRS.CZ.ElemA`.

* `elema_taylor`: `|f(x) - f(x-z) - Df(x)z| ≤ (M/2)|z|²` when `‖D²f‖ ≤ M`.
* `elema_cb2_data`: from `MemCb 2 μ` the bounds `|μ| ≤ B₀`, `‖Dμ‖ ≤ B₁`, `‖D²μ‖ ≤ B₂`, `cbNorm 2 μ = B₀+B₁+B₂`.
* `elema_pvK_coord`: the kernel of `Ω(u) = u_i` is `z_i/|z|^{d+θ}`.
* `elema_grad_sum`: `∑_i (∇μ)_i z_i = Dμ(x) z`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff SchwartzMap

noncomputable section

namespace HRS.CZ.ElemA

open HRS.CZ.Pv

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the first-order Taylor remainder `R(x,z) = μ(x) - μ(x-z) - Dμ(x)z` -/
def elema_R (μ : 𝔼 → ℝ) (x z : 𝔼) : ℝ := μ x - μ (x - z) - fderiv ℝ μ x z

/-- Taylor's bound for the remainder -/
lemma elema_taylor {f : 𝔼 → ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M) (x z : 𝔼) :
    |elema_R f x z| ≤ M / 2 * ‖z‖ ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hddf : Differentiable ℝ (fderiv ℝ f) := hf1.differentiable (by norm_num)
  have hlipD : ∀ a b : 𝔼, ‖fderiv ℝ f a - fderiv ℝ f b‖ ≤ M * ‖a - b‖ := by
    intro a b
    have := (convex_univ : Convex ℝ (Set.univ : Set 𝔼)).norm_image_sub_le_of_norm_fderiv_le
      (f := fderiv ℝ f) (fun x _ => hddf x)
      (fun x _ => by rw [pvapi_fderiv_fderiv_norm]; exact hM x) (mem_univ b) (mem_univ a)
    exact this
  set φ : ℝ → ℝ := fun t => f (x - t • z) - f x + t * fderiv ℝ f x z with hφ
  have hd2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x - t • z) (-z) t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const z).const_sub x
  have hφd : ∀ t : ℝ, HasDerivAt φ (fderiv ℝ f x z - fderiv ℝ f (x - t • z) z) t := by
    intro t
    have h2 := (hdf (x - t • z)).hasFDerivAt.comp_hasDerivAt t (hd2 t)
    have h3 : HasDerivAt φ (fderiv ℝ f (x - t • z) (-z) + 1 * fderiv ℝ f x z) t :=
      (h2.sub_const (f x)).add ((hasDerivAt_id t).mul_const (fderiv ℝ f x z))
    convert h3 using 1
    simp [sub_eq_add_neg, add_comm]
  have hBd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => M / 2 * ‖z‖ ^ 2 * t ^ 2) (M * ‖z‖ ^ 2 * t) t := by
    intro t
    have := (hasDerivAt_pow 2 t).const_mul (M / 2 * ‖z‖ ^ 2)
    convert this using 1
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := φ) (f' := fun t => fderiv ℝ f x z - fderiv ℝ f (x - t • z) z) (a := 0) (b := 1)
    (B := fun t : ℝ => M / 2 * ‖z‖ ^ 2 * t ^ 2) (B' := fun t => M * ‖z‖ ^ 2 * t)
    (fun t _ => (hφd t).continuousAt.continuousWithinAt)
    (fun t _ => (hφd t).hasDerivWithinAt)
    (by simp [hφ]) hBd
    (fun t ht => by
      have ht0 : 0 ≤ t := ht.1
      have h1 : ‖fderiv ℝ f x z - fderiv ℝ f (x - t • z) z‖ ≤
          ‖fderiv ℝ f x - fderiv ℝ f (x - t • z)‖ * ‖z‖ := by
        rw [← sub_apply]
        exact ContinuousLinearMap.le_opNorm _ _
      have h2 := hlipD x (x - t • z)
      have h3 : ‖x - (x - t • z)‖ = t * ‖z‖ := by
        rw [sub_sub_cancel, norm_smul, Real.norm_of_nonneg ht0]
      rw [h3] at h2
      calc _ ≤ ‖fderiv ℝ f x - fderiv ℝ f (x - t • z)‖ * ‖z‖ := h1
        _ ≤ (M * (t * ‖z‖)) * ‖z‖ := by gcongr
        _ = M * ‖z‖ ^ 2 * t := by ring)
  have := key (x := 1) ⟨zero_le_one, le_rfl⟩
  simp only [hφ, Real.norm_eq_abs, one_smul, one_mul, one_pow, mul_one] at this
  have e : elema_R f x z = -(f (x - z) - f x + fderiv ℝ f x z) := by
    unfold elema_R; ring
  rw [e, abs_neg]
  exact this

/-- bounds from `MemCb 2` -/
lemma elema_cb2_data {μ : 𝔼 → ℝ} (hμ : HRS.MemCb 2 μ) :
    ∃ B0 B1 B2 : ℝ, 0 ≤ B0 ∧ 0 ≤ B1 ∧ 0 ≤ B2 ∧ HRS.cbNorm 2 μ = B0 + B1 + B2 ∧ HRS.cbNorm 1 μ = B0 + B1 ∧ (∀ y, |μ y| ≤ B0) ∧
      (∀ y, ‖fderiv ℝ μ y‖ ≤ B1) ∧ (∀ y, ‖iteratedFDeriv ℝ 2 μ y‖ ≤ B2) := by
  have h0 := hμ.2 0 (by norm_num)
  have h1 := hμ.2 1 (by norm_num)
  have h2 := hμ.2 2 le_rfl
  refine ⟨⨆ z : 𝔼, ‖iteratedFDeriv ℝ 0 μ z‖, ⨆ z : 𝔼, ‖iteratedFDeriv ℝ 1 μ z‖,
    ⨆ z : 𝔼, ‖iteratedFDeriv ℝ 2 μ z‖, Real.iSup_nonneg fun z => norm_nonneg _,
    Real.iSup_nonneg fun z => norm_nonneg _, Real.iSup_nonneg fun z => norm_nonneg _, ?_, ?_, fun y => ?_,
    fun y => ?_, fun y => le_ciSup h2 y⟩
  · unfold HRS.cbNorm
    simp [Finset.sum_range_succ]
  · unfold HRS.cbNorm
    simp [Finset.sum_range_succ]
  · have := le_ciSup h0 y
    simpa [Real.norm_eq_abs] using this
  · have := le_ciSup h1 y
    simpa using this

/-- the kernel of `Ω(u) = u_i` -/
lemma elema_pvK_coord (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) (i : Fin d) (z : 𝔼) :
    pvK d θ (fun u : 𝔼 => u i) z = z i / ‖z‖ ^ ((d : ℝ) + θ) := by
  by_cases hz : z = 0
  · subst hz
    simp [pvK_zero hd hθ]
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    unfold pvK
    rw [Real.rpow_sub_one hn.ne']
    simp only [PiLp.smul_apply, smul_eq_mul]
    field_simp

/-- `∑_i (∇μ)_i z_i = Dμ(x) z` -/
lemma elema_grad_sum (μ : 𝔼 → ℝ) (x z : 𝔼) : ∑ i : Fin d, gradient μ x i * z i = fderiv ℝ μ x z := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := z) (y := fderiv ℝ μ x)
  rw [← h]
  show _ = inner ℝ (gradient μ x) z
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

lemma elema_R_zero (μ : 𝔼 → ℝ) (x : 𝔼) : elema_R μ x 0 = 0 := by
  simp [elema_R]

/-- the pointwise bound of the remainder kernel by `elema_kk` -/
lemma elema_remainder_le {θ : ℝ} {μ : 𝔼 → ℝ} (hμ : ContDiff ℝ 2 μ) {B0 B1 B2 : ℝ} (hB0 : 0 ≤ B0)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (h0 : ∀ y, |μ y| ≤ B0) (h1 : ∀ y, ‖fderiv ℝ μ y‖ ≤ B1)
    (h2 : ∀ y, ‖iteratedFDeriv ℝ 2 μ y‖ ≤ B2) (x z : 𝔼) :
    |elema_R μ x z| / ‖z‖ ^ ((d : ℝ) + θ) ≤ elema_kk d θ 1 (B2 / 2) (B0 + B1 / 2) z := by
  by_cases hz : z = 0
  · subst hz
    rw [elema_R_zero, abs_zero, zero_div]
    exact elema_kk_nonneg θ 1 _ _ zero_le_one (by linarith) (by linarith) 0
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hD : 0 < ‖z‖ ^ ((d : ℝ) + θ) := Real.rpow_pos_of_pos hn _
    rw [div_le_iff₀ hD]
    unfold elema_kk
    split_ifs with h
    · have hT := elema_taylor hμ h2 x z
      calc |elema_R μ x z| ≤ B2 / 2 * ‖z‖ ^ 2 := hT
        _ = 1 * (B2 / 2) * ‖z‖ ^ (2 - ((d : ℝ) + θ)) * ‖z‖ ^ ((d : ℝ) + θ) := by
            rw [mul_assoc (1 * (B2 / 2)), ← Real.rpow_add hn]
            have : (2 - ((d : ℝ) + θ) + ((d : ℝ) + θ)) = ((2 : ℕ) : ℝ) := by push_cast; ring
            rw [this, Real.rpow_natCast]
            ring
    · have hz1 : 1 < ‖z‖ := not_le.1 h
      have hb : |elema_R μ x z| ≤ 2 * B0 + B1 * ‖z‖ := by
        unfold elema_R
        have e1 := h0 x
        have e2 := h0 (x - z)
        have e3a : |fderiv ℝ μ x z| ≤ ‖fderiv ℝ μ x‖ * ‖z‖ := by
          simpa [Real.norm_eq_abs] using (fderiv ℝ μ x).le_opNorm z
        have e3 : |fderiv ℝ μ x z| ≤ B1 * ‖z‖ :=
          e3a.trans (mul_le_mul_of_nonneg_right (h1 x) (norm_nonneg _))
        calc |μ x - μ (x - z) - fderiv ℝ μ x z| ≤ |μ x| + |μ (x - z)| + |fderiv ℝ μ x z| := by
              refine (abs_sub _ _).trans ?_
              have := abs_sub (μ x) (μ (x - z))
              linarith
          _ ≤ 2 * B0 + B1 * ‖z‖ := by linarith
      calc |elema_R μ x z| ≤ 2 * B0 + B1 * ‖z‖ := hb
        _ ≤ (2 * B0 + B1) * ‖z‖ := by nlinarith
        _ = 1 * (2 * (B0 + B1 / 2)) * ‖z‖ ^ (1 - ((d : ℝ) + θ)) * ‖z‖ ^ ((d : ℝ) + θ) := by
            rw [mul_assoc (1 * (2 * (B0 + B1 / 2))), ← Real.rpow_add hn]
            have : (1 - ((d : ℝ) + θ) + ((d : ℝ) + θ)) = 1 := by ring
            rw [this, Real.rpow_one]
            ring

/-- the remainder integrand `R(x,z) W(x-z) / |z|^{d+θ}` -/
def elema_G (d : ℕ) (θ : ℝ) (μ W : EuclideanSpace ℝ (Fin d) → ℝ) (x z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  elema_R μ x z * W (x - z) / ‖z‖ ^ ((d : ℝ) + θ)

lemma elema_G_measurable {θ : ℝ} {μ W : 𝔼 → ℝ} (hμ : Continuous μ) (hW : Continuous W) (x : 𝔼) :
    Measurable (elema_G d θ μ W x) := by
  unfold elema_G elema_R
  exact (((measurable_const.sub (hμ.measurable.comp (measurable_const.sub measurable_id))).sub
    ((fderiv ℝ μ x).continuous.measurable)).mul (hW.measurable.comp (measurable_const.sub measurable_id))).div
    (measurable_norm.pow_const _)

lemma elema_G_measurable_prod {θ : ℝ} {μ W : 𝔼 → ℝ} (hμ : Continuous μ) (hμ1 : Continuous (fderiv ℝ μ))
    (hW : Continuous W) :
    Measurable (fun p : 𝔼 × 𝔼 => elema_G d θ μ W p.1 p.2) := by
  unfold elema_G elema_R
  have hap : Continuous (fun p : 𝔼 × 𝔼 => fderiv ℝ μ p.1 p.2) :=
    (hμ1.comp continuous_fst).clm_apply continuous_snd
  exact ((((hμ.comp continuous_fst).sub (hμ.comp (continuous_fst.sub continuous_snd))).sub hap).mul
    (hW.comp (continuous_fst.sub continuous_snd))).measurable.div
    ((measurable_norm.comp measurable_snd).pow_const _)

/-- `G` is dominated by the majorant kernel -/
lemma elema_G_le {θ : ℝ} {μ W : 𝔼 → ℝ} (hμ : ContDiff ℝ 2 μ) {B0 B1 B2 : ℝ} (hB0 : 0 ≤ B0)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (h0 : ∀ y, |μ y| ≤ B0) (h1 : ∀ y, ‖fderiv ℝ μ y‖ ≤ B1)
    (h2 : ∀ y, ‖iteratedFDeriv ℝ 2 μ y‖ ≤ B2) (x z : 𝔼) :
    ‖elema_G d θ μ W x z‖ₑ ≤ ENNReal.ofReal (elema_kk d θ 1 (B2 / 2) (B0 + B1 / 2) z) * ‖W (x - z)‖ₑ := by
  have hk := elema_remainder_le (d := d) (θ := θ) hμ hB0 hB1 hB2 h0 h1 h2 x z
  have hk0 := elema_kk_nonneg (d := d) θ 1 (B2 / 2) (B0 + B1 / 2) zero_le_one (by linarith) (by linarith) z
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hk0]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  unfold elema_G
  rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
  calc |elema_R μ x z| * |W (x - z)| / ‖z‖ ^ ((d : ℝ) + θ) =
      (|elema_R μ x z| / ‖z‖ ^ ((d : ℝ) + θ)) * |W (x - z)| := by ring
    _ ≤ elema_kk d θ 1 (B2 / 2) (B0 + B1 / 2) z * |W (x - z)| :=
        mul_le_mul_of_nonneg_right hk (abs_nonneg _)

/-- an a.e.-measurable function dominated by `kk · |W(x-·)|` with `W` bounded is integrable -/
lemma elema_integrable_of_kk (hd : 1 ≤ d) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) {B La Ba : ℝ} (hB : 0 ≤ B)
    (hLa : 0 ≤ La) (hBa : 0 ≤ Ba) {G W : 𝔼 → ℝ} {BW : ℝ} (hG : AEStronglyMeasurable G volume)
    (hWb : ∀ y, |W y| ≤ BW) (x : 𝔼)
    (hle : ∀ z, ‖G z‖ₑ ≤ ENNReal.ofReal (elema_kk d θ B La Ba z) * ‖W (x - z)‖ₑ) : Integrable G := by
  obtain ⟨C0, hC0, hkk⟩ := elema_kk_lintegral hd hθ1 hθ2 hB
  refine ⟨hG, ?_⟩
  have h1 : ∫⁻ z, ‖G z‖ₑ ≤ ∫⁻ z, ENNReal.ofReal (elema_kk d θ B La Ba z) * ENNReal.ofReal BW := by
    refine lintegral_mono fun z => (hle z).trans ?_
    refine mul_le_mul_right ?_ _
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (hWb _)
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top] at h1
  exact h1.trans_lt (ENNReal.mul_lt_top ((hkk La Ba hLa hBa).trans_lt ENNReal.ofReal_lt_top)
    ENNReal.ofReal_lt_top)

/-- integrability of the coordinate kernels on `{ε < |z|}` -/
lemma elema_pvK_int_trunc (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) {Ω : 𝔼 → ℝ} {B : ℝ} (hK : IsPvKernel Ω B)
    {u : 𝔼 → ℝ} (hu : Integrable u) (x : 𝔼) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun z => pvK d θ Ω z * u (x - z)) {z : 𝔼 | ε < ‖z‖} := by
  have hS : MeasurableSet {z : 𝔼 | ε < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine Integrable.mono' (((hu.comp_sub_left x).norm.const_mul (B * ε ^ (1 - ((d : ℝ) + θ)))).integrableOn)
    (((pvK_measurable hK θ).aestronglyMeasurable.mul (hu.comp_sub_left x).aestronglyMeasurable).restrict)
    ((ae_restrict_iff' hS).2 (ae_of_all _ fun z hz => ?_))
  have hz' : ε < ‖z‖ := hz
  rw [norm_mul, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_right ((pvK_abs_le hd hθ hK z).trans ?_) (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hε hz'.le (by linarith)) hK.nonneg

/-- the representation, given integrability of the remainder integrand (`0 < θ < 2`) -/
theorem elema_expansion_repr_of (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {μ : 𝔼 → ℝ}
    (hμ : HRS.MemCb 2 μ) (W : 𝓢(𝔼, ℝ)) (x : 𝔼) (hGint : Integrable (elema_G d θ μ W x)) :
    HRS.Whole.AppendixA.lamComm d θ μ W x - ∑ i : Fin d, gradient μ x i *
        HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) W x = ∫ z, elema_G d θ μ W x z := by
  obtain ⟨BW, LW, MW, hW⟩ := PvC2.of_schwartz W
  have hG0 : elema_G d θ μ W x 0 = 0 := by simp [elema_G, elema_R_zero]
  have T1 := lamComm_kernel_tendsto hd hθ0 hθ2 hμ W x
  have T2 := pvapi_tendsto_trunc hGint hG0
  have T3 : ∀ i : Fin d, Tendsto (fun ε : ℝ => pvTrunc d θ (fun u : 𝔼 => u i) W ε x) (𝓝[>] 0)
      (𝓝 (HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) W x)) := by
    intro i
    have hfar := pvK_far_integrable_of_integrable hd hθ0 (isPvKernel_coord i) W.integrable x
    rw [pvOdd_eq_of_lip hd hθ0 hθ2 (isPvKernel_coord i) hW.lipschitzWith x hfar]
    exact pvTrunc_tendsto hd hθ0 hθ2 (isPvKernel_coord i) hW.lipschitzWith x hfar
  have T4 := T2.add (tendsto_finsetSum (Finset.univ : Finset (Fin d))
    (fun i _ => (T3 i).const_mul (gradient μ x i)))
  have hev : (fun ε : ℝ => ∫ z in {z : 𝔼 | ε < ‖z‖}, (μ x - μ (x - z)) * W (x - z) / ‖z‖ ^ ((d : ℝ) + θ))
      =ᶠ[𝓝[>] 0] fun ε : ℝ => (∫ z in {z : 𝔼 | ε < ‖z‖}, elema_G d θ μ W x z) +
        ∑ i : Fin d, gradient μ x i * pvTrunc d θ (fun u : 𝔼 => u i) W ε x := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hS : MeasurableSet {z : 𝔼 | ε < ‖z‖} := measurableSet_lt measurable_const measurable_norm
    have hi : ∀ i : Fin d, IntegrableOn (fun z => gradient μ x i * (pvK d θ (fun u : 𝔼 => u i) z * W (x - z)))
        {z : 𝔼 | ε < ‖z‖} := fun i =>
      (elema_pvK_int_trunc hd hθ0 (isPvKernel_coord i) W.integrable x hε).const_mul _
    have hpt : ∀ z : 𝔼, (μ x - μ (x - z)) * W (x - z) / ‖z‖ ^ ((d : ℝ) + θ) =
        elema_G d θ μ W x z +
          ∑ i : Fin d, gradient μ x i * (pvK d θ (fun u : 𝔼 => u i) z * W (x - z)) := by
      intro z
      have e1 : ∑ i : Fin d, gradient μ x i * (pvK d θ (fun u : 𝔼 => u i) z * W (x - z)) =
          fderiv ℝ μ x z * W (x - z) / ‖z‖ ^ ((d : ℝ) + θ) := by
        rw [← elema_grad_sum, Finset.sum_mul, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [elema_pvK_coord hd hθ0]
        ring
      rw [e1]
      unfold elema_G elema_R
      ring
    rw [setIntegral_congr_fun hS (fun z _ => hpt z), integral_add hGint.integrableOn
      (integrable_finsetSum _ (fun i _ => hi i)), integral_finsetSum _ (fun i _ => hi i)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
    rfl
  have hlim := tendsto_nhds_unique (T1.congr' hev) T4
  linarith

/-- (iii-c), the representation: for `1 < θ < 2`, `μ ∈ C_b²`, `W` Schwartz,
`[Λ^θ,μ]W(x) - ∑_i ∂_iμ(x) 𝒯^{(i)}_θ W(x) = ∫ R(x,z) W(x-z) |z|^{-(d+θ)} dz` (absolutely convergent) -/
theorem elema_expansion_repr (hd : 1 ≤ d) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) {μ : 𝔼 → ℝ}
    (hμ : HRS.MemCb 2 μ) (W : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    Integrable (elema_G d θ μ W x) ∧
    HRS.Whole.AppendixA.lamComm d θ μ W x - ∑ i : Fin d, gradient μ x i *
        HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) W x = ∫ z, elema_G d θ μ W x z := by
  have hμ2 : ContDiff ℝ 2 μ := by simpa using hμ.1
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, -, -, h0, h1, h2⟩ := elema_cb2_data hμ
  obtain ⟨BW, LW, MW, hW⟩ := PvC2.of_schwartz W
  have hGint : Integrable (elema_G d θ μ W x) :=
    elema_integrable_of_kk hd hθ1 hθ2 (B := 1) (La := B2 / 2) (Ba := B0 + B1 / 2) zero_le_one
      (by linarith) (by linarith) (elema_G_measurable hμ2.continuous W.continuous x).aestronglyMeasurable
      hW.bdd x (fun z => elema_G_le hμ2 hB0 hB1 hB2 h0 h1 h2 x z)
  exact ⟨hGint, elema_expansion_repr_of hd (by linarith) hθ2 hμ W x hGint⟩

end HRS.CZ.ElemA
