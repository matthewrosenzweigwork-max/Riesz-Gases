import HRS.MS.CzPvkAux3
import HRS.MS.CzPvAux3
import HRS.MS.CzSymAux3
import HRS.MS.CzMikExtAux2
import HRS.MS.CzElemAux4

/-!
# PV-ASM, part 1: the uniform truncation bound on Schwartz functions (`ElemTruncBound`)

Packet PVASM (CZ development), namespace `HRS.CZ.PvAsm`.  Infrastructure (not a manuscript row); LINEAR kernel
`K_i(z) = z_i / |z|^{d+1}` only (`Ω(u) = u_i`, no general `Ω`).

Main result `elemTruncBound_lin`: for `d ≥ 1` and `1 < p < ∞` there is `CR` (depending on `d, p` only) with
`ElemTruncBound d p CR`, i.e. `‖pvTrunc d 1 (u_i) ε W‖_p ≤ CR ‖W‖_p` for every Schwartz `W`, every `ε > 0`
and every coordinate `i`.

Route: for a radial bump `φ` (unit scale, `PvkBump`), `kernel_decomp` gives `K 1_{|z|>ε} = KP_ε + Ψ_ε`
with `KP_ε = p.v. K * φ_ε`; the Ψ-part is bounded by `young_Psi` uniformly in `ε`, and for Schwartz `W`
`KP_ε * W = φ_ε * (T W)` (`T W = pvOdd d 1 (u_i) W`, associativity of the convolution plus dominated
convergence in the truncation parameter); `‖T W‖_p ≤ C ‖W‖_p` is the Mikhlin theorem (`mikhlin_Lp_schwartz`)
applied to the explicit symbol of `pvOdd_linear_fourier` (`m = -i c_1 ξ_i/|ξ|`), and `φ_ε *` is a contraction.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap

noncomputable section

namespace HRS.CZ.PvAsm

open HRS.CZ.Pv HRS.CZ.Pvk HRS.CZ.Mik HRS.CZ.Sym

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### the linear kernel and its truncations -/

/-- the linear kernel `K_i(z) = z_i/|z|^{d+1}` (`Ω(u) = u_i`) in the form of `PvkKernel` -/
def pvasmK (d : ℕ) (i : Fin d) : EuclideanSpace ℝ (Fin d) → ℝ :=
  pvkOmegaK d (fun u : EuclideanSpace ℝ (Fin d) => u i)

lemma pvasm_trunc_eq (i : Fin d) (u : 𝔼 → ℝ) (ε : ℝ) (x : 𝔼) :
    pvTrunc d 1 (fun v : 𝔼 => v i) u ε x = ∫ z, pvkKtr (pvasmK d i) ε z * u (x - z) := by
  rw [← pvk_setIntegral_eq_Ktr]
  unfold pvTrunc pvasmK
  refine setIntegral_congr_fun (measurableSet_lt measurable_const measurable_norm) fun z _ => ?_
  have := pvkOmegaK_eq_rpow (d := d) (fun v : 𝔼 => v i) z
  simp only at this ⊢
  rw [this]

lemma pvasm_pvK_eq (i : Fin d) (z : 𝔼) : pvK d 1 (fun v : 𝔼 => v i) z = pvasmK d i z := by
  unfold pvK pvasmK
  exact pvkOmegaK_eq_rpow (d := d) (fun v : 𝔼 => v i) z

lemma pvasm_kernel (hd : 1 ≤ d) (i : Fin d) : ∃ L : ℝ, PvkKernel d (pvasmK d i) L := by
  refine pvkKernel_of_contDiff hd (Ω := fun v : 𝔼 => v i) ?_ (fun u _ => by simp)
  exact ((EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ).contDiff).of_le (by exact_mod_cast le_top)

/-! ### a uniform bound for the truncations of a Lipschitz integrable function -/

lemma pvasm_trunc_unif (hd : 1 ≤ d) (i : Fin d) {u : 𝔼 → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    (hui : Integrable u) :
    ∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x : 𝔼,
      |∫ z, pvkKtr (pvasmK d i) ε z * u (x - z)| ≤ c := by
  have hK := isPvKernel_coord (d := d) i
  set G : 𝔼 → ℝ := fun z => (L : ℝ) * ‖z‖ ^ (-((d : ℝ) - 1)) with hG
  have hGi : IntegrableOn G (ball (0 : 𝔼) 2) :=
    (pvapi_integrableOn_ball_rpow hd (α := (d : ℝ) - 1) (by linarith) 2).const_mul (L : ℝ)
  refine ⟨(∫ z in ball (0 : 𝔼) 2, G z) + ∫ z, ‖u z‖, fun ε hε hε1 x => ?_⟩
  rw [← pvasm_trunc_eq]
  have hfar := pvK_far_integrable_of_integrable hd one_pos hK hui x
  rw [pvTrunc_diff_repr hd one_pos one_lt_two hK hu x hfar hε hε1]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · -- near part
    set S : Set 𝔼 := {z : 𝔼 | ε < ‖z‖} ∩ closedBall 0 1 with hS
    have hSm : MeasurableSet S :=
      (measurableSet_lt measurable_const measurable_norm).inter measurableSet_closedBall
    have hSB : S ⊆ ball (0 : 𝔼) 2 := fun z hz => by
      have := mem_closedBall_zero_iff.1 hz.2
      rw [mem_ball_zero_iff]; linarith
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hGi.mono_set hSB) ?_).trans ?_
    · refine (ae_restrict_iff' hSm).2 (ae_of_all _ fun z hz => ?_)
      have hn : 0 < ‖z‖ := lt_trans hε hz.1
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 := pvK_abs_le hd one_pos hK z
      have h2 := pvapi_lip_bound hu x z
      have h3 : |pvK d 1 (fun v : 𝔼 => v i) z| * |u (x - z) - u x| ≤
          (1 * ‖z‖ ^ (1 - ((d : ℝ) + 1))) * ((L : ℝ) * ‖z‖) :=
        mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg zero_le_one (Real.rpow_nonneg hn.le _))
      refine h3.trans (le_of_eq ?_)
      simp only [hG]
      have : ‖z‖ ^ (-((d : ℝ) - 1)) = ‖z‖ ^ (1 - ((d : ℝ) + 1)) * ‖z‖ := by
        have e : -((d : ℝ) - 1) = (1 - ((d : ℝ) + 1)) + 1 := by ring
        rw [e, Real.rpow_add hn, Real.rpow_one]
      rw [this]; ring
    · refine setIntegral_mono_set hGi ?_ (Eventually.of_forall hSB)
      refine (ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ fun z _ => ?_)
      simp only [hG, Pi.zero_apply]
      exact mul_nonneg L.2 (Real.rpow_nonneg (norm_nonneg _) _)
  · -- far part
    have hT : MeasurableSet {z : 𝔼 | 1 < ‖z‖} := measurableSet_lt measurable_const measurable_norm
    rw [← Real.norm_eq_abs]
    have hi : Integrable (fun z => ‖u (x - z)‖) := (hui.comp_sub_left x).norm
    refine (norm_integral_le_of_norm_le hi.integrableOn ?_).trans ?_
    · refine (ae_restrict_iff' hT).2 (ae_of_all _ fun z hz => ?_)
      rw [norm_mul, Real.norm_eq_abs]
      have := pvK_abs_le_far hd one_pos hK (le_of_lt (show 1 < ‖z‖ from hz))
      calc |pvK d 1 (fun v : 𝔼 => v i) z| * ‖u (x - z)‖ ≤ 1 * ‖u (x - z)‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = ‖u (x - z)‖ := one_mul _
    · calc ∫ z in {z : 𝔼 | 1 < ‖z‖}, ‖u (x - z)‖ ≤ ∫ z, ‖u (x - z)‖ :=
            setIntegral_le_integral hi (Eventually.of_forall fun z => norm_nonneg _)
        _ = ∫ z, ‖u z‖ := integral_sub_left_eq_self (fun z => ‖u z‖) volume x

/-! ### associativity of the convolution with a bounded kernel -/

/-- `((k * f) * g)(x) = (f * (k * g))(x)` for a bounded measurable kernel `k` and integrable `f, g`. -/
lemma pvasm_assoc {k f g : 𝔼 → ℝ} (hk : Measurable k) {c : ℝ} (hkb : ∀ y, |k y| ≤ c)
    (hf : Integrable f) (hg : Integrable g) (x : 𝔼) :
    ∫ z, (∫ y, k y * f (z - y)) * g (x - z) = ∫ w, f w * ∫ y, k y * g (x - w - y) := by
  set Φ : 𝔼 × 𝔼 → ℝ := fun p => k p.1 * (f p.2 * g (x - p.1 - p.2)) with hΦ
  have hconv : Integrable (fun p : 𝔼 × 𝔼 => f p.2 * g (p.1 - p.2)) (volume.prod volume) := by
    have := hf.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hg
    simpa using this
  have hmp : MeasurePreserving (fun p : 𝔼 × 𝔼 => (x - p.1, p.2)) (volume.prod volume)
      (volume.prod volume) :=
    (Measure.measurePreserving_sub_left volume x).prod (MeasurePreserving.id volume)
  have hΦi : Integrable Φ (volume.prod volume) := by
    have h1 := hmp.integrable_comp_of_integrable hconv
    refine Integrable.bdd_mul (c := c) h1 (hk.comp measurable_fst).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]; exact hkb _
  have hS : MeasurePreserving (fun p : 𝔼 × 𝔼 => (p.1, p.2 - p.1)) (volume.prod volume)
      (volume.prod volume) := measurePreserving_prod_sub volume volume
  set G : 𝔼 × 𝔼 → ℝ := fun p => k p.1 * (f (p.2 - p.1) * g (x - p.2)) with hGdef
  have hGΦ : G = fun p => Φ (p.1, p.2 - p.1) := by
    funext p
    simp only [hGdef, hΦ]
    congr 3
    abel
  have hGi : Integrable G (volume.prod volume) := by
    rw [hGΦ]; exact hS.integrable_comp_of_integrable hΦi
  have e1 : ∫ z, (∫ y, k y * f (z - y)) * g (x - z) = ∫ z, ∫ y, G (y, z) := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hGdef]; ring
  have e2 : ∫ z, ∫ y, G (y, z) = ∫ p, G p ∂(volume.prod volume) :=
    (integral_prod_symm G hGi).symm
  have e3 : ∫ p, G p ∂(volume.prod volume) = ∫ y, ∫ z, G (y, z) := integral_prod G hGi
  have e4 : ∀ y : 𝔼, ∫ z, G (y, z) = ∫ w, Φ (y, w) := fun y => by
    have := integral_sub_right_eq_self (μ := (volume : Measure 𝔼)) (fun w => Φ (y, w)) y
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    rw [hGΦ]
  have e5 : ∫ y, ∫ w, Φ (y, w) = ∫ p, Φ p ∂(volume.prod volume) := (integral_prod Φ hΦi).symm
  have e6 : ∫ p, Φ p ∂(volume.prod volume) = ∫ w, ∫ y, Φ (y, w) := integral_prod_symm Φ hΦi
  rw [e1, e2, e3]
  simp_rw [e4]
  rw [e5, e6]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  dsimp only
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [hΦ]
  rw [sub_right_comm x y w]
  ring

/-! ### `KP_ε * W = φ_ε * (T W)` for Schwartz `W` -/

lemma pvasm_dil_lip {φ : 𝔼 → ℝ} {Lφ M : ℝ} (hφ : PvkBump d φ Lφ M) {ε : ℝ} (hε : 0 < ε) :
    ∃ L' : ℝ≥0, LipschitzWith L' (pvkDil ε φ) := by
  refine ⟨(⟨(ε ^ d)⁻¹ * (Lφ * ε⁻¹), by have := hφ.lip_nonneg; positivity⟩ : ℝ≥0),
    LipschitzWith.of_dist_le_mul fun a b => ?_⟩
  rw [Real.dist_eq, dist_eq_norm]
  unfold pvkDil
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (ε ^ d)⁻¹)]
  have h1 := hφ.lip (ε⁻¹ • a) (ε⁻¹ • b)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hε)] at h1
  change _ ≤ (ε ^ d)⁻¹ * (Lφ * ε⁻¹) * ‖a - b‖
  calc (ε ^ d)⁻¹ * |φ (ε⁻¹ • a) - φ (ε⁻¹ • b)| ≤ (ε ^ d)⁻¹ * (Lφ * (ε⁻¹ * ‖a - b‖)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

lemma pvasm_dil_cont {φ : 𝔼 → ℝ} {Lφ M : ℝ} (hφ : PvkBump d φ Lφ M) (ε : ℝ) :
    Continuous (pvkDil ε φ) :=
  continuous_const.mul ((pvk_bump_cont hφ).comp (continuous_const_smul ε⁻¹))

lemma pvasm_dil_integrable {φ : 𝔼 → ℝ} {Lφ M : ℝ} (hφ : PvkBump d φ Lφ M) {ε : ℝ} (hε : 0 < ε) :
    Integrable (pvkDil ε φ) :=
  pvk_dil_integrable hε (pvk_bump_integrable hφ)

lemma pvasm_trunc_tendsto (hd : 1 ≤ d) (i : Fin d) (W : 𝓢(𝔼, ℝ)) (y : 𝔼) :
    Tendsto (fun δ : ℝ => pvTrunc d 1 (fun v : 𝔼 => v i) W δ y) (𝓝[>] 0)
      (𝓝 (HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W y)) := by
  have hK := isPvKernel_coord (d := d) i
  obtain ⟨B1, L1, M1, h1⟩ := PvC2.of_schwartz W
  have hfar := pvK_far_integrable_of_integrable hd one_pos hK W.integrable y
  have hlim := pvTrunc_tendsto hd one_pos one_lt_two hK h1.lipschitzWith y hfar
  have hv := pvOdd_eq_of_lip hd one_pos one_lt_two hK h1.lipschitzWith y hfar
  rw [hv]
  exact hlim

/-- **`KP_ε * W = φ_ε * (T W)`** for Schwartz `W`, where `T W = pvOdd d 1 (u_i) W`. -/
theorem pvasm_KP_conv (hd : 1 ≤ d) (i : Fin d) {L : ℝ} (hK : PvkKernel d (pvasmK d i) L)
    {φ : 𝔼 → ℝ} {Lφ M : ℝ} (hφ : PvkBump d φ Lφ M) {ε : ℝ} (hε : 0 < ε) (W : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    ∫ z, pvkDil ε (pvkKP (pvasmK d i) φ) z * W (x - z) =
      ∫ w, pvkDil ε φ w * HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W (x - w) := by
  have hKc := isPvKernel_coord (d := d) i
  obtain ⟨B1, L1, M1, h1⟩ := PvC2.of_schwartz W
  have hWl := h1.lipschitzWith
  obtain ⟨Lε, hLε⟩ := pvasm_dil_lip hφ hε
  have hφi := pvasm_dil_integrable hφ hε
  have hφc := pvasm_dil_cont hφ ε
  obtain ⟨c1, hc1⟩ := pvasm_trunc_unif hd i hLε hφi
  obtain ⟨c2, hc2⟩ := pvasm_trunc_unif hd i hWl W.integrable
  have hWi : Integrable fun z => W (x - z) := W.integrable.comp_sub_left x
  have hev1 : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ ∧ δ ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with δ hδ using ⟨hδ.1, hδ.2.le⟩
  -- Step 1: limit of the `z`-integrals
  have step1 : Tendsto (fun δ : ℝ => ∫ z, (∫ y, pvkKtr (pvasmK d i) δ y * pvkDil ε φ (z - y)) *
      W (x - z)) (𝓝[>] 0) (𝓝 (∫ z, pvkDil ε (pvkKP (pvasmK d i) φ) z * W (x - z))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => |c1| * ‖W (x - z)‖) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun δ => ?_
      have hm : Measurable fun z : 𝔼 => ∫ y, pvkKtr (pvasmK d i) δ y * pvkDil ε φ (z - y) := by
        have := pvTrunc_measurable (d := d) (θ := 1) hKc hφc δ
        simpa [pvasm_trunc_eq] using this
      exact (hm.mul (W.continuous.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    · filter_upwards [hev1] with δ hδ
      refine ae_of_all _ fun z => ?_
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ((hc1 δ hδ.1 hδ.2 z).trans (le_abs_self _)) (norm_nonneg _)
    · exact hWi.norm.const_mul _
    · refine ae_of_all _ fun z => ?_
      exact ((kernel_decomp hd hK hφ).2.2.2.2.2.2.2.2.2 ε hε z).mul_const _
  -- Step 2: limit of the `w`-integrals
  have step2 : Tendsto (fun δ : ℝ => ∫ w, pvkDil ε φ w *
      ∫ y, pvkKtr (pvasmK d i) δ y * W (x - w - y)) (𝓝[>] 0)
      (𝓝 (∫ w, pvkDil ε φ w * HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W (x - w))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun w => |c2| * ‖pvkDil ε φ w‖) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun δ => ?_
      have hm : Measurable fun y : 𝔼 => ∫ z, pvkKtr (pvasmK d i) δ z * W (y - z) := by
        have := pvTrunc_measurable (d := d) (θ := 1) hKc W.continuous δ
        simpa [pvasm_trunc_eq] using this
      exact (hφc.measurable.mul (hm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    · filter_upwards [hev1] with δ hδ
      refine ae_of_all _ fun w => ?_
      rw [norm_mul, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [Real.norm_eq_abs]
      exact (hc2 δ hδ.1 hδ.2 (x - w)).trans (le_abs_self _)
    · exact hφi.norm.const_mul _
    · refine ae_of_all _ fun w => ?_
      have := pvasm_trunc_tendsto hd i W (x - w)
      simp only [pvasm_trunc_eq] at this
      exact this.const_mul _
  -- Step 3: the two sequences coincide
  have hEq : ∀ᶠ δ : ℝ in 𝓝[>] 0, (∫ z, (∫ y, pvkKtr (pvasmK d i) δ y * pvkDil ε φ (z - y)) *
      W (x - z)) = ∫ w, pvkDil ε φ w * ∫ y, pvkKtr (pvasmK d i) δ y * W (x - w - y) := by
    filter_upwards [hev1] with δ hδ
    exact pvasm_assoc (pvk_Ktr_meas hK δ) (c := L * (δ ^ d)⁻¹) (pvk_Ktr_bound hd hK hδ.1) hφi
      W.integrable x
  exact tendsto_nhds_unique (step1.congr' hEq) step2

/-! ### the `L^p` bound of `T W = pvOdd d 1 (u_i) W` on Schwartz functions (Mikhlin) -/

/-- the multiplier of `pvOdd d 1 (u_i)` is `(-i c_1)` times the Riesz symbol `ξ_i/|ξ|` -/
lemma pvasm_symbol (i : Fin d) (ξ : 𝔼) :
    symlin_mult d 1 i ξ =
      (-Complex.I * ((symlin_c d 1 : ℝ) : ℂ)) * ((ξ i / ‖ξ‖ : ℝ) : ℂ) := by
  unfold symlin_mult
  by_cases h : ξ = 0
  · subst h
    simp
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 h
    have hπ := Real.pi_pos
    have e : (2 * Real.pi * ‖ξ‖) ^ ((1 : ℝ) - 2) = (2 * Real.pi * ‖ξ‖)⁻¹ := by
      rw [show ((1 : ℝ) - 2) = -1 by norm_num, Real.rpow_neg_one]
    rw [e]
    have hn' : (‖ξ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn.ne'
    have hπ' : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hπ.ne'
    push_cast
    field_simp

lemma pvasm_enorm_real (r : ℝ) : ‖(r : ℂ)‖ₑ = ‖r‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]

lemma pvasm_pvOdd_eq_T (hd : 1 ≤ d) (i : Fin d) (Z : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    ((HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) Z x : ℝ) : ℂ) =
      mik2_T (fun ξ : 𝔼 => ((ξ i / ‖ξ‖ : ℝ) : ℂ))
        ((-Complex.I * ((symlin_c d 1 : ℝ) : ℂ)) • symlin_Cx Z) x := by
  have h1 := (pvOdd_linear_fourier hd one_pos one_lt_two i Z).1 x
  rw [h1]
  unfold mik2_T
  refine congrFun (congrArg 𝓕⁻ ?_) x
  funext ξ
  dsimp only
  rw [mik2_fourier_smul, pvasm_symbol]
  have : (⇑(symlin_Cx Z) : 𝔼 → ℂ) = fun y : 𝔼 => ((Z y : ℝ) : ℂ) := rfl
  rw [this]
  ring

/-- `∫ |T Z|^p ≤ C ∫ |Z|^p` for Schwartz `Z`, uniformly in the coordinate `i` -/
theorem pvasm_T_lintegral (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (i : Fin d) (Z : 𝓢(𝔼, ℝ)),
      ∫⁻ x, ‖HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) Z x‖ₑ ^ p ≤ C * ∫⁻ x, ‖Z x‖ₑ ^ p := by
  obtain ⟨C0, hC0, hmain⟩ := mikhlin_Lp_schwartz hd hp
  obtain ⟨A, hA0, hA⟩ := isMikhlin_riesz d
  have hp0 : 0 ≤ p := by linarith
  refine ⟨C0 * ENNReal.ofReal A ^ p * ‖((-Complex.I * ((symlin_c d 1 : ℝ) : ℂ)))‖ₑ ^ p,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hC0 (ENNReal.rpow_ne_top_of_nonneg hp0
      ENNReal.ofReal_ne_top)) (ENNReal.rpow_ne_top_of_nonneg hp0 enorm_ne_top), fun i Z => ?_⟩
  set a : ℂ := -Complex.I * ((symlin_c d 1 : ℝ) : ℂ) with ha
  have h2 := hmain A _ hA0 (hA i) (a • symlin_Cx Z)
  have e1 : ∫⁻ x, ‖HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) Z x‖ₑ ^ p =
      ∫⁻ x, ‖mik2_T (fun ξ : 𝔼 => ((ξ i / ‖ξ‖ : ℝ) : ℂ)) (a • symlin_Cx Z) x‖ₑ ^ p := by
    refine lintegral_congr fun x => ?_
    rw [← pvasm_pvOdd_eq_T hd i Z x, pvasm_enorm_real]
  have e2 : ∫⁻ x, ‖(a • symlin_Cx Z) x‖ₑ ^ p = ‖a‖ₑ ^ p * ∫⁻ x, ‖Z x‖ₑ ^ p := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0 enorm_ne_top)]
    refine lintegral_congr fun x => ?_
    rw [smul_apply, smul_eq_mul, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hp0,
      symlin_Cx_apply, pvasm_enorm_real]
  rw [e1]
  refine h2.trans (le_of_eq ?_)
  rw [e2]
  ring

/-- the eLpNorm form of the Schwartz-level Mikhlin bound -/
theorem pvasm_T_eLpNorm (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ (i : Fin d) (Z : 𝓢(𝔼, ℝ)),
      eLpNorm (HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) Z) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal CT * eLpNorm Z (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hmain⟩ := pvasm_T_lintegral hd hp
  have hp0 : 0 < p := by linarith
  have hexp : (0 : ℝ) ≤ 1 / p := by positivity
  have hfin : C ^ (1 / p) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hexp hC
  refine ⟨(C ^ (1 / p)).toReal, ENNReal.toReal_nonneg, fun i Z => ?_⟩
  rw [ENNReal.ofReal_toReal hfin]
  have hne : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hKc := isPvKernel_coord (d := d) i
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne ENNReal.ofReal_ne_top
      (pvOdd_aesm hd one_pos one_lt_two hKc Z),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hne ENNReal.ofReal_ne_top Z.continuous.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  rw [← ENNReal.mul_rpow_of_nonneg _ _ hexp]
  exact ENNReal.rpow_le_rpow (hmain i Z) hexp

/-! ### measurability of convolutions -/

lemma pvasm_conv_meas {κ h : 𝔼 → ℝ} (hκ : Measurable κ) (hh : Measurable h) :
    Measurable (fun x : 𝔼 => ∫ z, κ z * h (x - z)) := by
  have hF : Measurable (fun p : 𝔼 × 𝔼 => κ p.2 * h (p.1 - p.2)) :=
    (hκ.comp measurable_snd).mul (hh.comp (measurable_fst.sub measurable_snd))
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

lemma pvasm_dil_bdd {F : 𝔼 → ℝ} {c : ℝ} (hb : ∀ z, |F z| ≤ c) {ε : ℝ} (hε : 0 < ε) (z : 𝔼) :
    |pvkDil ε F z| ≤ (ε ^ d)⁻¹ * c := by
  unfold pvkDil
  rw [abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (hb _) (by positivity)

lemma pvasm_Psi_bdd (hd : 1 ≤ d) {K : 𝔼 → ℝ} {L : ℝ} (hK : PvkKernel d K L) {φ : 𝔼 → ℝ} {Lφ M : ℝ}
    (hφ : PvkBump d φ Lφ M) : ∃ c : ℝ, ∀ z, |pvkPsi K φ z| ≤ c := by
  obtain ⟨C, hC⟩ := pvk_Psi_decay hd hK hφ
  have hC0 := pvk_C_nonneg hC
  refine ⟨C, fun z => (hC z).trans ?_⟩
  have : (1 + ‖z‖) ^ (-((d : ℝ) + 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg z]) (by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith)
  calc C * (1 + ‖z‖) ^ (-((d : ℝ) + 1)) ≤ C * 1 := mul_le_mul_of_nonneg_left this hC0
    _ = C := mul_one C

/-- the decomposition of the truncations of a Schwartz function -/
theorem pvasm_trunc_decomp (hd : 1 ≤ d) (i : Fin d) {L : ℝ} (hK : PvkKernel d (pvasmK d i) L)
    {φ : 𝔼 → ℝ} {Lφ M : ℝ} (hφ : PvkBump d φ Lφ M) {ε : ℝ} (hε : 0 < ε) (W : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    pvTrunc d 1 (fun v : 𝔼 => v i) W ε x =
      (∫ w, pvkDil ε φ w * HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W (x - w)) +
        ∫ z, pvkDil ε (pvkPsi (pvasmK d i) φ) z * W (x - z) := by
  have hWi : Integrable fun z => W (x - z) := W.integrable.comp_sub_left x
  obtain ⟨c1, hc1⟩ := (kernel_decomp hd hK hφ).2.1
  obtain ⟨c2, hc2⟩ := pvasm_Psi_bdd hd hK hφ
  have h1 : Integrable fun z => pvkDil ε (pvkKP (pvasmK d i) φ) z * W (x - z) :=
    Integrable.bdd_mul (c := (ε ^ d)⁻¹ * c1) hWi
      (pvk_dil_measurable (kernel_decomp hd hK hφ).2.2.1 ε).aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]; exact pvasm_dil_bdd hc1 hε z)
  have h2 : Integrable fun z => pvkDil ε (pvkPsi (pvasmK d i) φ) z * W (x - z) :=
    Integrable.bdd_mul (c := (ε ^ d)⁻¹ * c2) hWi
      (pvk_dil_measurable (pvk_Psi_measurable hd hK hφ) ε).aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]; exact pvasm_dil_bdd hc2 hε z)
  rw [pvasm_trunc_eq, pvk_trunc_integral_decomp hK hε x h1 h2, pvasm_KP_conv hd i hK hφ hε W x]

/-- per-coordinate truncation bound, given the Mikhlin bound for `T` -/
theorem pvasm_trunc_bound_i (hd : 1 ≤ d) (i : Fin d) {p : ℝ} (hp : 1 < p) {CT : ℝ} (hCT : 0 ≤ CT)
    (hT : ∀ Z : 𝓢(𝔼, ℝ), eLpNorm (HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) Z)
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal CT * eLpNorm Z (ENNReal.ofReal p) volume) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (W : 𝓢(𝔼, ℝ)) (ε : ℝ), 0 < ε →
      eLpNorm (fun x => pvTrunc d 1 (fun v : 𝔼 => v i) W ε x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (CT + c) * eLpNorm W (ENNReal.ofReal p) volume := by
  obtain ⟨L, hK⟩ := pvasm_kernel hd i
  obtain ⟨Lφ, M, hφ⟩ := pvkBump_of_contDiffBump
    (⟨1 / 2, 1, by norm_num, by norm_num⟩ : ContDiffBump (0 : 𝔼)) (by norm_num)
  set φ := (⟨1 / 2, 1, by norm_num, by norm_num⟩ : ContDiffBump (0 : 𝔼)).normed volume with hφdef
  have hΨi := Psi_integrable hd hK hφ
  have hΨm := pvk_Psi_measurable hd hK hφ
  have hc0 : 0 ≤ ∫ z, ‖pvkPsi (pvasmK d i) φ z‖ := integral_nonneg fun z => norm_nonneg _
  refine ⟨∫ z, ‖pvkPsi (pvasmK d i) φ z‖, hc0, fun W ε hε => ?_⟩
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  obtain ⟨B1, L1, M1, h1⟩ := PvC2.of_schwartz W
  have hKc := isPvKernel_coord (d := d) i
  have hTm : Measurable (HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W) :=
    pvOdd_measurable_of_lip hd one_pos one_lt_two hKc h1.lipschitzWith fun x =>
      pvK_far_integrable_of_integrable hd one_pos hKc W.integrable x
  have hfun : (fun x => pvTrunc d 1 (fun v : 𝔼 => v i) W ε x) = fun x =>
      (∫ w, pvkDil ε φ w * HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W (x - w)) +
        ∫ z, pvkDil ε (pvkPsi (pvasmK d i) φ) z * W (x - z) :=
    funext fun x => pvasm_trunc_decomp hd i hK hφ hε W x
  rw [hfun]
  refine le_trans (eLpNorm_add_le (f := fun x => ∫ w, pvkDil ε φ w *
      HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W (x - w))
    (g := fun x => ∫ z, pvkDil ε (pvkPsi (pvasmK d i) φ) z * W (x - z)) (μ := volume) hp1) ?_
  have hA := young_Psi (F := ℝ) (Ψ := φ) (pvk_bump_cont hφ).measurable (pvk_bump_integrable hφ) hp.le
    (g := HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W) hTm.aestronglyMeasurable hε
  have hB := young_Psi (F := ℝ) (Ψ := pvkPsi (pvasmK d i) φ) hΨm hΨi hp.le
    (g := W) W.continuous.aestronglyMeasurable hε
  have hφn : ∫ z, ‖φ z‖ = 1 := by
    have : ∫ z, ‖φ z‖ = ∫ z, φ z :=
      integral_congr_ae (ae_of_all _ fun z => by simp [Real.norm_eq_abs, abs_of_nonneg (hφ.nonneg z)])
    rw [this, hφ.integral_eq_one]
  rw [hφn, ENNReal.ofReal_one, one_mul] at hA
  simp only [smul_eq_mul] at hA hB
  calc _ ≤ eLpNorm (HRS.Whole.AppendixA.pvOdd d 1 (fun v : 𝔼 => v i) W) (ENNReal.ofReal p) volume +
        ENNReal.ofReal (∫ z, ‖pvkPsi (pvasmK d i) φ z‖) * eLpNorm W (ENNReal.ofReal p) volume :=
        add_le_add hA hB
    _ ≤ ENNReal.ofReal CT * eLpNorm W (ENNReal.ofReal p) volume +
        ENNReal.ofReal (∫ z, ‖pvkPsi (pvasmK d i) φ z‖) * eLpNorm W (ENNReal.ofReal p) volume :=
        add_le_add (hT W) le_rfl
    _ = _ := by
        rw [← add_mul, ENNReal.ofReal_add hCT hc0]

/-- **`ElemTruncBound` for the linear kernels** (the deliverable (1) of PV-ASM): for `d ≥ 1`, `1 < p`
there is `CR` (depending on `d, p`) with `‖pvTrunc d 1 (u_i) ε W‖_p ≤ CR ‖W‖_p` for all Schwartz `W`,
`ε > 0` and all coordinates `i`. -/
theorem elemTruncBound_lin (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) :
    ∃ CR : ℝ, 0 ≤ CR ∧ HRS.CZ.ElemA.ElemTruncBound d p CR := by
  obtain ⟨CT, hCT, hT⟩ := pvasm_T_eLpNorm hd hp
  have h := fun i : Fin d => pvasm_trunc_bound_i hd i hp hCT (hT i)
  choose c hc0 hc using h
  refine ⟨CT + ∑ i, c i, add_nonneg hCT (Finset.sum_nonneg fun i _ => hc0 i), fun i W ε hε => ?_⟩
  refine (hc i W ε hε).trans ?_
  have := Finset.single_le_sum (f := c) (fun j _ => hc0 j) (Finset.mem_univ i)
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

end HRS.CZ.PvAsm
