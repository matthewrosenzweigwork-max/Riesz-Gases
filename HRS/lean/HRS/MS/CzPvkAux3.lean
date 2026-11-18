import HRS.MS.CzPvkAux1
import HRS.MS.CzPvkAux2
import HRS.Commutator.Whole.XLIAux23

/-!
# PV-KERNEL, part 3: the decomposition `K 1_{|z|>ε} = KP_ε + Ψ_ε`, Young bound, ties

Packet PVK (CZ development), namespace `HRS.CZ.Pvk`.  Infrastructure (not a manuscript row); the setting
(`PvkKernel`, `PvkBump`, `pvkKtr`, `pvkKP`) is in `CzPvkAux2.lean`, the approximate identity in `CzPvkAux1.lean`.

Main declarations (the packet's output names):
* `kernel_decomp`: for `K` odd, `(-d)`-homogeneous, Lipschitz on the sphere, and a bump `φ`: the truncated integrals
  `∫_{|y|>δ} K y φ(z-y) dy` converge as `δ → 0+` to `pvkKP K φ z`; `KP` is bounded, measurable, odd;
  `Ψ := pvkPsi K φ = K 1_{|z|>1} - KP` satisfies `|Ψ z| ≤ C (1+‖z‖)^{-(d+1)}`, is measurable, integrable, with `∫ Ψ = 0`;
  for every `ε > 0`: `K 1_{|z|>ε} = KP_ε + Ψ_ε` pointwise (`pvkDil ε f z = ε^{-d} f(z/ε)`, homogeneity of `K`),
  and `KP_ε z = lim_δ ∫_{|y|>δ} K y φ_ε(z-y) dy` (so `KP_ε = p.v. K * φ_ε`).
* `Psi_integrable`, `Psi_meanzero` (the latter because `Ψ` is odd), `pvk_Psi_decay` (the decay bound).
* `young_Psi`: `‖Ψ_ε * g‖_p ≤ ‖Ψ‖_1 ‖g‖_p`, uniformly in `ε > 0` (`1 ≤ p`, `g` a.e. strongly measurable; values in any
  real normed space; the left side is the `eLpNorm` of the Bochner convolution, whose a.e. measurability is part of
  the proof), via `young_lintegral` (`XLIAux23`).
* `ae_tendsto_Psi`: for `g ∈ L^p`, a.e. `x`: `(Ψ_ε * g)(x) → 0` (`ae_tendsto_approxid_meanzero` of part 1 applied to `Ψ`).
* `pvkOmegaK`, `pvkKernel_of_omega`, `pvkKernel_of_contDiff` (every `C¹` `Ω`, odd on the unit sphere, gives a
  `PvkKernel`; in particular every `IsOddSmooth Ω`), `pvkBump_of_contDiffBump`, `pvk_setIntegral_eq_Ktr`,
  `pvk_trunc_integral_decomp` (`T_ε g(x) = (KP_ε * g)(x) + (Ψ_ε * g)(x)` when both pieces are integrable).

Adjustments with respect to the packet sketch (harmless): `p` in `young_Psi` is a real exponent `1 ≤ p` (as in
`young_lintegral`); the p.v. definition uses `limUnder` and the existence of the limit is proved (`kernel_decomp`,
first conjunct); `KP` is not claimed smooth (bounded, measurable, odd only).
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.CZ.Pvk

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

section Scaling

variable {K : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {φ : EuclideanSpace ℝ (Fin d) → ℝ} {Lφ M : ℝ}

lemma pvk_Ktr_smul (hK : PvkKernel d K L) {ε : ℝ} (hε : 0 < ε) (δ : ℝ) (w : 𝔼) :
    pvkKtr K δ (ε • w) = (ε ^ d)⁻¹ * pvkKtr K (δ / ε) w := by
  unfold pvkKtr
  have hn : ‖ε • w‖ = ε * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have : δ < ε * ‖w‖ ↔ δ / ε < ‖w‖ := by rw [div_lt_iff₀ hε, mul_comm]
  rw [hn]
  by_cases h : δ < ε * ‖w‖
  · simp only [h, this.1 h, ↓reduceIte]; rw [hK.hom ε hε]
  · have h' : ¬ δ / ε < ‖w‖ := fun h' => h (this.2 h')
    simp only [h, h', ↓reduceIte, mul_zero]

/-- The scaling identity for the truncated kernel in terms of the unit truncation. -/
lemma pvk_Ktr_scale (hK : PvkKernel d K L) {ε : ℝ} (hε : 0 < ε) (z : 𝔼) :
    pvkKtr K ε z = pvkDil ε (pvkKtr K 1) z := by
  have := pvk_Ktr_smul hK hε ε (ε⁻¹ • z)
  rw [smul_inv_smul₀ hε.ne', div_self hε.ne'] at this
  exact this

lemma pvk_dil_add (ε : ℝ) (f g : 𝔼 → ℝ) (z : 𝔼) :
    pvkDil ε (fun w => f w + g w) z = pvkDil ε f z + pvkDil ε g z := by
  unfold pvkDil; ring

/-- Scaling of the principal value: the truncated integrals against `φ_ε` are the dilated ones. -/
lemma pvk_trunc_dil (hK : PvkKernel d K L) {ε : ℝ} (hε : 0 < ε) (φ : 𝔼 → ℝ) (δ : ℝ) (z : 𝔼) :
    ∫ y, pvkKtr K δ y * pvkDil ε φ (z - y) = (ε ^ d)⁻¹ * pvkTrunc K φ (δ / ε) (ε⁻¹ • z) := by
  set F : 𝔼 → ℝ := fun y => pvkKtr K δ y * pvkDil ε φ (z - y) with hF
  have h := Measure.integral_comp_smul (volume : Measure 𝔼) F ε
  rw [finrank_euclideanSpace_fin, abs_of_pos (by positivity), smul_eq_mul] at h
  have hFε : ∀ w : 𝔼, F (ε • w) = ((ε ^ d)⁻¹ * (ε ^ d)⁻¹) *
      (pvkKtr K (δ / ε) w * φ (ε⁻¹ • z - w)) := by
    intro w
    simp only [hF, pvkDil]
    rw [pvk_Ktr_smul hK hε, smul_sub, inv_smul_smul₀ hε.ne']
    ring
  simp_rw [hFε] at h
  rw [integral_const_mul] at h
  have hε' : ε ^ d ≠ 0 := by positivity
  unfold pvkTrunc
  have : ∫ y, F y = ε ^ d * (((ε ^ d)⁻¹ * (ε ^ d)⁻¹) *
      ∫ w, pvkKtr K (δ / ε) w * φ (ε⁻¹ • z - w)) := by
    rw [h]; field_simp
  rw [this]; field_simp

end Scaling


section Decay

variable {K : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {φ : EuclideanSpace ℝ (Fin d) → ℝ} {Lφ M : ℝ}

/-- For `‖z‖ ≥ 2` the near-field part of `KP` vanishes and `Ψ z = ∫ (K z - K y) φ(z-y) dy`. -/
lemma pvk_Psi_far (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) {z : 𝔼}
    (hz : 2 ≤ ‖z‖) : pvkPsi K φ z = ∫ y, (K z - K y) * φ (z - y) := by
  have hsupp : ∀ y : 𝔼, ‖y‖ < 1 → φ (z - y) = 0 := fun y hy => by
    apply hφ.supp
    have : ‖z‖ - ‖y‖ ≤ ‖z - y‖ := norm_sub_norm_le z y
    linarith
  have hI1 : pvkI1 K φ z = 0 := by
    unfold pvkI1
    refine integral_eq_zero_of_ae (ae_of_all _ fun y => ?_)
    by_cases h : y ∈ ball (0:𝔼) 1
    · have hy : ‖y‖ < 1 := by simpa using h
      rw [Set.indicator_of_mem h]
      simp [pvkG, hsupp y hy, hφ.supp z (by linarith)]
    · rw [Set.indicator_of_notMem h]; rfl
  have hcongr : (fun y => {y : 𝔼 | 1 ≤ ‖y‖}.indicator (fun y => K y * φ (z - y)) y) =
      fun y => K y * φ (z - y) := by
    funext y
    by_cases h : 1 ≤ ‖y‖
    · rw [Set.indicator_of_mem (show y ∈ {y : 𝔼 | 1 ≤ ‖y‖} from h)]
    · rw [Set.indicator_of_notMem (show y ∉ {y : 𝔼 | 1 ≤ ‖y‖} from h), hsupp y (not_le.1 h),
        mul_zero]
  have hint : Integrable (fun y => K y * φ (z - y)) := by
    have := pvk_I2_integrable hd hK hφ z
    rwa [show ({y : 𝔼 | 1 ≤ ‖y‖}.indicator fun y => K y * φ (z - y)) =
      fun y => K y * φ (z - y) from hcongr] at this
  have hint2 : Integrable (fun y : 𝔼 => K z * φ (z - y)) :=
    ((pvk_bump_integrable hφ).comp_sub_left z).const_mul _
  have hI2 : pvkI2 K φ z = ∫ y, K y * φ (z - y) := by
    unfold pvkI2; rw [hcongr]
  have hone : ∫ y : 𝔼, φ (z - y) = 1 := by
    rw [integral_sub_left_eq_self φ volume z]; exact hφ.integral_eq_one
  have e : (fun y => (K z - K y) * φ (z - y)) = fun y => K z * φ (z - y) - K y * φ (z - y) := by
    funext y; ring
  rw [e, integral_sub hint2 hint, integral_const_mul, hone, mul_one]
  unfold pvkPsi
  rw [pvk_KP_eq hd hK hφ, hI1, hI2, zero_add]
  have : pvkKtr K 1 z = K z := by
    unfold pvkKtr; simp only [show (1:ℝ) < ‖z‖ by linarith, ↓reduceIte]
  rw [this]

lemma pvk_Psi_far_bound (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) {z : 𝔼}
    (hz : 2 ≤ ‖z‖) :
    |pvkPsi K φ z| ≤ ((4 + d) * 4 ^ d) * L * ((‖z‖ ^ d)⁻¹ * ‖z‖⁻¹) := by
  rw [pvk_Psi_far hd hK hφ hz, ← Real.norm_eq_abs]
  set c : ℝ := ((4 + d) * 4 ^ d) * L * ((‖z‖ ^ d)⁻¹ * ‖z‖⁻¹) with hc
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith
  have hgi : Integrable (fun y : 𝔼 => c * φ (z - y)) :=
    ((pvk_bump_integrable hφ).comp_sub_left z).const_mul _
  have hb := norm_integral_le_of_norm_le hgi (f := fun y => (K z - K y) * φ (z - y))
    (ae_of_all _ fun y => ?_)
  · refine hb.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_sub_left_eq_self φ volume z, hφ.integral_eq_one, mul_one]
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφ.nonneg _)]
    by_cases h : φ (z - y) = 0
    · simp [h]
    · have hy : ‖z - y‖ ≤ 1 := by
        by_contra hh
        exact h (hφ.supp _ (not_le.1 hh))
      have hdiff := pvk_K_diff hd hK hz0 (y := y) (by
        have : ‖y - z‖ = ‖z - y‖ := norm_sub_rev _ _
        linarith)
      rw [abs_sub_comm]
      refine mul_le_mul_of_nonneg_right ?_ (hφ.nonneg _)
      refine hdiff.trans ?_
      have hyz : ‖y - z‖ ≤ 1 := by rw [norm_sub_rev]; exact hy
      have hP : 0 ≤ (‖z‖ ^ d)⁻¹ * ‖z‖⁻¹ := by positivity
      have hc1 : 0 ≤ ((4 + d) * 4 ^ d) * L := mul_nonneg (by positivity) hK.nonneg
      rw [hc]
      refine mul_le_mul_of_nonneg_left ?_ hc1
      calc ‖y - z‖ * ((‖z‖ ^ d)⁻¹ * ‖z‖⁻¹) ≤ 1 * ((‖z‖ ^ d)⁻¹ * ‖z‖⁻¹) :=
            mul_le_mul_of_nonneg_right hyz hP
        _ = _ := one_mul _



lemma pvk_rpow_inv (d : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ (-((d:ℝ) + 1)) = ((1 + r) ^ (d + 1))⁻¹ := by
  rw [Real.rpow_neg (by positivity)]
  congr 1
  rw [← Real.rpow_natCast]; norm_num

lemma pvk_Ktr_one_bound (hd : 1 ≤ d) (hK : PvkKernel d K L) (z : 𝔼) : |pvkKtr K 1 z| ≤ L := by
  have := pvk_Ktr_bound hd hK one_pos z
  simpa using this

/-- Decay of `Ψ = K 1_{|z|>1} - KP`: `|Ψ z| ≤ C (1+‖z‖)^{-(d+1)}`. -/
theorem pvk_Psi_decay (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) :
    ∃ C : ℝ, ∀ z : 𝔼, |pvkPsi K φ z| ≤ C * (1 + ‖z‖) ^ (-((d:ℝ) + 1)) := by
  obtain ⟨cKP, hcKP⟩ := pvk_KP_bounded hd hK hφ
  have hcKP0 : 0 ≤ cKP := (abs_nonneg _).trans (hcKP 0)
  refine ⟨max (3 ^ (d + 1) * (L + cKP)) ((3 / 2) ^ (d + 1) * (((4 + d) * 4 ^ d) * L)), fun z => ?_⟩
  rw [pvk_rpow_inv d (norm_nonneg z)]
  have hQ : 0 < ((1 + ‖z‖) ^ (d + 1))⁻¹ := by positivity
  by_cases hz : ‖z‖ < 2
  · have h1 : |pvkPsi K φ z| ≤ L + cKP := by
      unfold pvkPsi
      exact (abs_sub _ _).trans (add_le_add (pvk_Ktr_one_bound hd hK z) (hcKP z))
    have h2 : (1 + ‖z‖) ^ (d + 1) ≤ 3 ^ (d + 1) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have h3 : ((3:ℝ) ^ (d + 1))⁻¹ ≤ ((1 + ‖z‖) ^ (d + 1))⁻¹ := inv_anti₀ (by positivity) h2
    refine h1.trans ?_
    calc L + cKP = (3 ^ (d + 1) * (L + cKP)) * ((3:ℝ) ^ (d + 1))⁻¹ := by field_simp
      _ ≤ (3 ^ (d + 1) * (L + cKP)) * ((1 + ‖z‖) ^ (d + 1))⁻¹ :=
          mul_le_mul_of_nonneg_left h3 (by have := hK.nonneg; positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hQ.le
  · have hz2 : 2 ≤ ‖z‖ := not_lt.1 hz
    have hzpos : 0 < ‖z‖ := by linarith
    refine (pvk_Psi_far_bound hd hK hφ hz2).trans ?_
    have h1 : (1 + ‖z‖) ^ (d + 1) ≤ (3 / 2) ^ (d + 1) * ‖z‖ ^ (d + 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have h2 : (‖z‖ ^ d)⁻¹ * ‖z‖⁻¹ = (‖z‖ ^ (d + 1))⁻¹ := by
      rw [pow_succ, mul_inv]
    have h3 : (‖z‖ ^ (d + 1))⁻¹ ≤ (3 / 2) ^ (d + 1) * ((1 + ‖z‖) ^ (d + 1))⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div, ← mul_div_assoc, div_le_div_iff₀ (by positivity)
        (by positivity)]
      calc 1 * (1 + ‖z‖) ^ (d + 1) ≤ (3 / 2) ^ (d + 1) * ‖z‖ ^ (d + 1) := by linarith
        _ = _ := by ring
    rw [h2]
    calc ((4 + d) * 4 ^ d) * L * (‖z‖ ^ (d + 1))⁻¹
        ≤ ((4 + d) * 4 ^ d) * L * ((3 / 2) ^ (d + 1) * ((1 + ‖z‖) ^ (d + 1))⁻¹) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg (by positivity) hK.nonneg)
      _ = ((3 / 2) ^ (d + 1) * (((4 + d) * 4 ^ d) * L)) * ((1 + ‖z‖) ^ (d + 1))⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hQ.le

lemma pvk_Psi_odd (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) (z : 𝔼) :
    pvkPsi K φ (-z) = -pvkPsi K φ z := by
  unfold pvkPsi
  rw [pvk_KP_odd hd hK hφ]
  have : pvkKtr K 1 (-z) = -pvkKtr K 1 z := by
    unfold pvkKtr
    by_cases h : 1 < ‖z‖
    · simp only [norm_neg, h, ↓reduceIte, hK.odd]
    · simp only [norm_neg, h, ↓reduceIte, neg_zero]
  rw [this]; ring

lemma pvk_Psi_measurable (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) :
    Measurable (pvkPsi K φ) :=
  (pvk_Ktr_meas hK 1).sub (pvk_KP_measurable hd hK hφ)

/-- `Ψ ∈ L¹`. -/
theorem Psi_integrable (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) :
    Integrable (pvkPsi K φ) := by
  obtain ⟨C, hC⟩ := pvk_Psi_decay hd hK hφ
  exact pvk_Psi_integrable (pvk_Psi_measurable hd hK hφ) hC

/-- `∫ Ψ = 0` (both `K 1_{|z|>1}` and `KP` are odd, so `Ψ` is odd and integrable). -/
theorem Psi_meanzero (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) :
    ∫ z, pvkPsi K φ z = 0 :=
  pvk_integral_odd (pvk_Psi_odd hd hK hφ)

end Decay


section Decomp

variable {K : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {φ : EuclideanSpace ℝ (Fin d) → ℝ} {Lφ M : ℝ}

/-- Scaled principal value: `KP_ε := (KP)_ε` is the limit of the truncated integrals against `φ_ε`. -/
lemma pvk_KP_scaled (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) {ε : ℝ}
    (hε : 0 < ε) (z : 𝔼) :
    Tendsto (fun δ => ∫ y, pvkKtr K δ y * pvkDil ε φ (z - y)) (𝓝[>] 0)
      (𝓝 (pvkDil ε (pvkKP K φ) z)) := by
  have h1 : Tendsto (fun δ : ℝ => δ / ε) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun δ : ℝ => δ / ε) (𝓝 0) (𝓝 (0 / ε)) :=
        (continuous_id.div_const ε).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact div_pos hδ hε
  have h2 := ((pvk_trunc_tendsto hd hK hφ (ε⁻¹ • z)).comp h1).const_mul ((ε ^ d)⁻¹)
  rw [← pvk_KP_eq hd hK hφ] at h2
  refine h2.congr' ?_
  filter_upwards with δ
  simp only [Function.comp]
  rw [pvk_trunc_dil hK hε φ δ z]

/-- **Kernel decomposition** (`kernel_decomp`).  For `K` odd, homogeneous of degree `-d`, Lipschitz
on the sphere, and `φ` a radial bump with `∫ φ = 1`:
`KP = p.v. K * φ` exists (as a limit of truncated integrals), is bounded, measurable and odd;
`Ψ = K 1_{|z|>1} - KP` is `O((1+|z|)^{-(d+1)})`, integrable, of mean zero; and for every `ε > 0`,
`K 1_{|z|>ε} = KP_ε + Ψ_ε` with `KP_ε = ε^{-d} KP(·/ε) = p.v. K * φ_ε`. -/
theorem kernel_decomp (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) :
    (∀ z : 𝔼, Tendsto (fun δ => ∫ y, pvkKtr K δ y * φ (z - y)) (𝓝[>] 0) (𝓝 (pvkKP K φ z))) ∧
    (∃ c : ℝ, ∀ z : 𝔼, |pvkKP K φ z| ≤ c) ∧ Measurable (pvkKP K φ) ∧
    (∀ z : 𝔼, pvkKP K φ (-z) = -pvkKP K φ z) ∧
    (∃ C : ℝ, ∀ z : 𝔼, |pvkPsi K φ z| ≤ C * (1 + ‖z‖) ^ (-((d:ℝ) + 1))) ∧
    Measurable (pvkPsi K φ) ∧ Integrable (pvkPsi K φ) ∧ ∫ z, pvkPsi K φ z = 0 ∧
    (∀ ε : ℝ, 0 < ε → ∀ z : 𝔼,
      pvkKtr K ε z = pvkDil ε (pvkKP K φ) z + pvkDil ε (pvkPsi K φ) z) ∧
    (∀ ε : ℝ, 0 < ε → ∀ z : 𝔼, Tendsto (fun δ => ∫ y, pvkKtr K δ y * pvkDil ε φ (z - y))
      (𝓝[>] 0) (𝓝 (pvkDil ε (pvkKP K φ) z))) := by
  refine ⟨fun z => ?_, pvk_KP_bounded hd hK hφ, pvk_KP_measurable hd hK hφ, pvk_KP_odd hd hK hφ,
    pvk_Psi_decay hd hK hφ, pvk_Psi_measurable hd hK hφ, Psi_integrable hd hK hφ,
    Psi_meanzero hd hK hφ, fun ε hε z => ?_, fun ε hε z => pvk_KP_scaled hd hK hφ hε z⟩
  · have := pvk_trunc_tendsto hd hK hφ z
    rw [← pvk_KP_eq hd hK hφ] at this
    exact this
  · rw [pvk_Ktr_scale hK hε]
    have : pvkKtr K 1 = fun w => pvkKP K φ w + pvkPsi K φ w := by
      funext w; unfold pvkPsi; ring
    rw [this, pvk_dil_add]

end Decomp


section Young

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma pvk_dil_norm_integral {ε : ℝ} (hε : 0 < ε) (Ψ : 𝔼 → ℝ) :
    ∫ z, ‖pvkDil ε Ψ z‖ = ∫ z, ‖Ψ z‖ := by
  have : (fun z => ‖pvkDil ε Ψ z‖) = pvkDil ε (fun z => ‖Ψ z‖) := by
    funext z
    unfold pvkDil
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [this, pvk_dil_integral hε]

/-- **Young bound for `Ψ_ε`**: `‖Ψ_ε * g‖_p ≤ ‖Ψ‖_1 ‖g‖_p` for `1 ≤ p < ∞`, uniformly in `ε > 0`. -/
theorem young_Psi {Ψ : 𝔼 → ℝ} (hΨm : Measurable Ψ) (hΨ : Integrable Ψ) {p : ℝ} (hp : 1 ≤ p)
    {g : 𝔼 → F} (hg : AEStronglyMeasurable g volume) {ε : ℝ} (hε : 0 < ε) :
    eLpNorm (fun x => ∫ z, pvkDil ε Ψ z • g (x - z)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (∫ z, ‖Ψ z‖) * eLpNorm g (ENNReal.ofReal p) volume := by
  obtain ⟨g', hg's, hgg'⟩ := hg
  have hae : ∀ x : 𝔼, (fun z => g (x - z)) =ᵐ[volume] fun z => g' (x - z) := fun x =>
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae_eq_comp hgg'
  have hT : (fun x : 𝔼 => ∫ z, pvkDil ε Ψ z • g (x - z)) =
      fun x => ∫ z, pvkDil ε Ψ z • g' (x - z) := by
    funext x
    refine integral_congr_ae ?_
    filter_upwards [hae x] with z hz
    simp only [hz]
  rw [hT, eLpNorm_congr_ae hgg']
  have hp0 : (0:ℝ) < p := by linarith
  have hpne0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hTm : AEStronglyMeasurable (fun x : 𝔼 => ∫ z, pvkDil ε Ψ z • g' (x - z)) volume := by
    have : StronglyMeasurable (fun q : 𝔼 × 𝔼 => pvkDil ε Ψ q.2 • g' (q.1 - q.2)) :=
      ((pvk_dil_measurable hΨm ε).comp measurable_snd).stronglyMeasurable.smul
        (hg's.comp_measurable (measurable_fst.sub measurable_snd))
    exact this.aestronglyMeasurable.integral_prod_right'
  rw [eLpNorm_eq_eLpNorm' hpne0 ENNReal.ofReal_ne_top hTm,
    eLpNorm_eq_eLpNorm' hpne0 ENNReal.ofReal_ne_top hg's.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  unfold eLpNorm' 
  set a : 𝔼 → ℝ≥0∞ := fun z => ‖pvkDil ε Ψ z‖ₑ with ha
  set b : 𝔼 → ℝ≥0∞ := fun y => ‖g' y‖ₑ with hb
  have ham : Measurable a := (pvk_dil_measurable hΨm ε).enorm
  have hbm : Measurable b := hg's.enorm
  have hpt : ∀ x : 𝔼, ‖∫ z, pvkDil ε Ψ z • g' (x - z)‖ₑ ≤ ∫⁻ z, a z * b (x - z) := fun x =>
    (enorm_integral_le_lintegral_enorm _).trans
      (le_of_eq (lintegral_congr fun z => by simp [ha, hb, enorm_smul]))
  have h1 : ∫⁻ x, ‖∫ z, pvkDil ε Ψ z • g' (x - z)‖ₑ ^ p ≤ ∫⁻ x, (∫⁻ z, a z * b (x - z)) ^ p :=
    lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) hp0.le
  have h2 := HRS.Commutator.Whole.XLI.young_lintegral ham hbm hp
  have h3 : ∫⁻ z, a z = ENNReal.ofReal (∫ z, ‖Ψ z‖) := by
    rw [← pvk_dil_norm_integral hε Ψ]
    exact (ofReal_integral_norm_eq_lintegral_enorm (pvk_dil_integrable hε hΨ)).symm
  have hb' : ∫⁻ x, ‖g' x‖ₑ ^ p = ∫⁻ x, b x ^ p := rfl
  calc (∫⁻ x, ‖∫ z, pvkDil ε Ψ z • g' (x - z)‖ₑ ^ p) ^ (1 / p)
      ≤ ((∫⁻ z, a z) ^ p * ∫⁻ x, b x ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (h1.trans h2) (by positivity)
    _ = (∫⁻ z, a z) * (∫⁻ x, b x ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
        have : p * (1 / p) = 1 := by field_simp
        rw [this, ENNReal.rpow_one]
    _ = _ := by rw [h3]

end Young


section Corollaries

variable {K : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {φ : EuclideanSpace ℝ (Fin d) → ℝ} {Lφ M : ℝ}

/-- **Approximate identity for `Ψ`**: for `g ∈ L^p` (`1 ≤ p`), a.e. `x`, `(Ψ_ε * g)(x) → 0` as
`ε → 0+`.  Combination of `kernel_decomp` and `ae_tendsto_approxid_meanzero`. -/
theorem ae_tendsto_Psi {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {g : 𝔼 → F} (hg : MemLp g p volume) :
    ∀ᵐ x ∂(volume : Measure 𝔼),
      Tendsto (fun ε : ℝ => ∫ z, pvkDil ε (pvkPsi K φ) z • g (x - z)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC⟩ := pvk_Psi_decay hd hK hφ
  exact ae_tendsto_approxid_meanzero (pvk_Psi_measurable hd hK hφ) hC (Psi_meanzero hd hK hφ) hp hg

/-- The kernel `K z = Ω(z/|z|)/|z|^d`. -/
def pvkOmegaK (d : ℕ) (Ω : EuclideanSpace ℝ (Fin d) → ℝ) (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Ω (‖z‖⁻¹ • z) / ‖z‖ ^ d

/-- `pvkOmegaK` is the `θ = 1` integrand of `pvOdd` (real power `d + 1 - 1`). -/
lemma pvkOmegaK_eq_rpow (Ω : 𝔼 → ℝ) (z : 𝔼) :
    Ω (‖z‖⁻¹ • z) / ‖z‖ ^ ((d : ℝ) + 1 - 1) = pvkOmegaK d Ω z := by
  unfold pvkOmegaK
  rw [add_sub_cancel_right, Real.rpow_natCast]

lemma pvkKernel_of_omega (hd : 1 ≤ d) {Ω : 𝔼 → ℝ} {L : ℝ} (hL : 0 ≤ L) (hΩm : Measurable Ω)
    (hodd : ∀ u : 𝔼, ‖u‖ = 1 → Ω (-u) = -Ω u)
    (hlip : ∀ u v : 𝔼, ‖u‖ = 1 → ‖v‖ = 1 → |Ω u - Ω v| ≤ L * ‖u - v‖) :
    PvkKernel d (pvkOmegaK d Ω) L := by
  have hd0 : d ≠ 0 := by omega
  have hunit : ∀ z : 𝔼, z ≠ 0 → ‖‖z‖⁻¹ • z‖ = 1 := fun z hz => by
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  refine ⟨hL, ?_, ?_, ?_, ?_⟩
  · unfold pvkOmegaK
    exact (hΩm.comp (measurable_norm.inv.smul measurable_id)).div (measurable_norm.pow_const _)
  · intro z
    rcases eq_or_ne z 0 with rfl | hz
    · simp [pvkOmegaK, zero_pow hd0]
    · have h1 : ‖z‖⁻¹ • z ≠ 0 := fun h => by
        have := hunit z hz; rw [h, norm_zero] at this; exact zero_ne_one this
      have e : ‖-z‖⁻¹ • (-z) = -(‖z‖⁻¹ • z) := by rw [norm_neg, smul_neg]
      unfold pvkOmegaK
      rw [e, norm_neg, hodd _ (hunit z hz)]; ring
  · intro c hc z
    rcases eq_or_ne z 0 with rfl | hz
    · simp [pvkOmegaK, hd0]
    · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
      have e : ‖c • z‖⁻¹ • (c • z) = ‖z‖⁻¹ • z := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
        congr 1; field_simp
      unfold pvkOmegaK
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_pow]
      field_simp
  · intro u v hu hv
    have hu0 : u ≠ 0 := fun h => by rw [h, norm_zero] at hu; exact zero_ne_one hu
    have hv0 : v ≠ 0 := fun h => by rw [h, norm_zero] at hv; exact zero_ne_one hv
    unfold pvkOmegaK
    rw [hu, hv, inv_one, one_smul, one_smul, one_pow, div_one, div_one]
    exact hlip u v hu hv

/-- Every `C¹` function `Ω` that is odd on the unit sphere (in particular every smooth odd `Ω`,
i.e. `IsOddSmooth`) gives a kernel satisfying the hypotheses of `kernel_decomp`. -/
theorem pvkKernel_of_contDiff (hd : 1 ≤ d) {Ω : 𝔼 → ℝ} (hΩ : ContDiff ℝ 1 Ω)
    (hodd : ∀ u : 𝔼, ‖u‖ = 1 → Ω (-u) = -Ω u) :
    ∃ L : ℝ, PvkKernel d (pvkOmegaK d Ω) L := by
  obtain ⟨K, hK⟩ := hΩ.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall (0:𝔼) 1)
    (isCompact_closedBall (0:𝔼) 1)
  refine ⟨K, pvkKernel_of_omega hd K.2 hΩ.continuous.measurable hodd fun u v hu hv => ?_⟩
  have h := hK.dist_le_mul u (by simp [hu]) v (by simp [hv])
  rw [Real.dist_eq, dist_eq_norm] at h
  exact h

/-- A `ContDiffBump` of outer radius `≤ 1` (normalised to integral `1`) satisfies `PvkBump`. -/
theorem pvkBump_of_contDiffBump (f : ContDiffBump (0 : 𝔼)) (hf : f.rOut ≤ 1) :
    ∃ Lφ M : ℝ, PvkBump d (f.normed volume) Lφ M := by
  obtain ⟨C, hC⟩ := (f.hasCompactSupport_normed (μ := volume)).exists_bound_of_continuous
    (f.continuous_normed (μ := volume))
  obtain ⟨Lc, hLc⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (f.hasCompactSupport_normed (μ := volume)) (f.contDiff_normed (μ := volume) (n := 1))
    one_ne_zero
  refine ⟨Lc, C, ⟨?_, ?_, ?_, ?_, Lc.2, ?_, ?_⟩⟩
  · exact f.nonneg_normed
  · exact f.normed_neg
  · intro z hz
    by_contra h
    have : z ∈ Function.support (f.normed volume) := h
    rw [f.support_normed_eq] at this
    have := mem_ball_zero_iff.1 this
    linarith
  · intro z
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC z)
  · intro z w
    have := hLc.dist_le_mul z w
    rwa [Real.dist_eq, dist_eq_norm] at this
  · exact f.integral_normed



/-- Truncated singular integral against `u(x-·)`, as an integral over `{ε < ‖z‖}` (the form used in
`pvOdd`/`fracLap`) and as an integral of the truncated kernel. -/
lemma pvk_setIntegral_eq_Ktr {u : 𝔼 → ℝ} (ε : ℝ) (x : 𝔼) :
    ∫ z in {z : 𝔼 | ε < ‖z‖}, K z * u (x - z) = ∫ z, pvkKtr K ε z * u (x - z) := by
  rw [← integral_indicator (measurableSet_lt measurable_const measurable_norm)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases h : ε < ‖z‖
  · simp [pvkKtr, Set.indicator, h]
  · simp [pvkKtr, Set.indicator, h]

/-- Pointwise decomposition of the truncated singular integral `T_ε g(x) = (KP_ε * g)(x) + (Ψ_ε * g)(x)`
(whenever both pieces are integrable). -/
lemma pvk_trunc_integral_decomp (hK : PvkKernel d K L) {ε : ℝ} (hε : 0 < ε) {g : 𝔼 → ℝ} (x : 𝔼)
    (h1 : Integrable fun z => pvkDil ε (pvkKP K φ) z * g (x - z))
    (h2 : Integrable fun z => pvkDil ε (pvkPsi K φ) z * g (x - z)) :
    ∫ z, pvkKtr K ε z * g (x - z) =
      (∫ z, pvkDil ε (pvkKP K φ) z * g (x - z)) + ∫ z, pvkDil ε (pvkPsi K φ) z * g (x - z) := by
  rw [← integral_add h1 h2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  have : pvkKtr K ε z = pvkDil ε (pvkKP K φ) z + pvkDil ε (pvkPsi K φ) z := by
    rw [pvk_Ktr_scale hK hε]
    have : pvkKtr K 1 = fun w => pvkKP K φ w + pvkPsi K φ w := by
      funext w; unfold pvkPsi; ring
    rw [this, pvk_dil_add]
  simp only [this, add_mul]

end Corollaries

end HRS.CZ.Pvk
