import Mathlib

/-!
# PV-KERNEL, part 2: kernel estimates and the principal value `KP = p.v. K * φ`

Packet PVK (CZ development), namespace `HRS.CZ.Pvk`.  Infrastructure (not a manuscript row).

Setting.  `K : ℝ^d → ℝ` is *abstract*: `PvkKernel d K L` asks `K` measurable, odd, homogeneous of degree `-d`
(`K(c z) = c^{-d} K z`) and `L`-Lipschitz on the unit sphere (this covers `K z = Ω(z/|z|)/|z|^d` for every
measurable `Ω`, Lipschitz and odd on the sphere, see `pvkKernel_of_omega` in part 3; `IsOddSmooth Ω` gives it, see
`CzPvkTie.lean`).  `φ` is a bump: `PvkBump d φ Lφ M` asks `φ` nonnegative, even, supported in `closedBall 0 1`,
bounded by `M`, `Lφ`-Lipschitz, `∫ φ = 1` (every `ContDiffBump` of outer radius `≤ 1`, normalised, qualifies:
`pvkBump_of_contDiffBump`).

Contents.  Basic bounds `|K z| ≤ L ‖z‖^{-d}`, `K 0 = 0`; the Lipschitz estimate away from `0`
(`pvk_K_diff`: `|K y - K x| ≤ C(d) L ‖y-x‖ ‖x‖^{-d-1}` for `‖y-x‖ ≤ ‖x‖/2`); the truncated kernel
`pvkKtr K δ = K 1_{‖z‖>δ}`; the principal value `pvkKP K φ z = limUnder_{δ→0+} ∫_{‖y‖>δ} K y φ(z-y) dy`
and the proof that the limit EXISTS (`pvk_trunc_tendsto`: the truncated integrals converge to
`I1 + I2 = ∫_{|y|<1} K y (φ(z-y) - φ(z)) dy + ∫_{|y|≥1} K y φ(z-y) dy`, using that the odd kernel integrates to
zero on annuli); `KP` is bounded, measurable and odd.

Adjustments with respect to the packet sketch (harmless, all documented): `KP` is proved bounded,
measurable and odd (continuity/smoothness of `KP` is not proved and is not used by any later step);
`φ` is only assumed Lipschitz (not smooth) and `Measurable` of the kernel is part of `PvkKernel`;
the statements are for real-valued `K`.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.CZ.Pvk

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- Abstract kernel hypotheses: `K` is measurable, odd, homogeneous of degree `-d`, and Lipschitz
(with constant `L`) on the unit sphere. -/
structure PvkKernel (d : ℕ) (K : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) : Prop where
  nonneg : 0 ≤ L
  meas : Measurable K
  odd : ∀ z, K (-z) = -K z
  hom : ∀ c : ℝ, 0 < c → ∀ z, K (c • z) = (c ^ d)⁻¹ * K z
  lip : ∀ u v : EuclideanSpace ℝ (Fin d), ‖u‖ = 1 → ‖v‖ = 1 → |K u - K v| ≤ L * ‖u - v‖

/-- Bump hypotheses: nonnegative, even, supported in the closed unit ball, bounded by `M`,
`Lφ`-Lipschitz, with integral `1`. -/
structure PvkBump (d : ℕ) (φ : EuclideanSpace ℝ (Fin d) → ℝ) (Lφ M : ℝ) : Prop where
  nonneg : ∀ z, 0 ≤ φ z
  even : ∀ z, φ (-z) = φ z
  supp : ∀ z, 1 < ‖z‖ → φ z = 0
  bdd : ∀ z, φ z ≤ M
  lip_nonneg : 0 ≤ Lφ
  lip : ∀ z w, |φ z - φ w| ≤ Lφ * ‖z - w‖
  integral_eq_one : ∫ z, φ z = 1

/-- The truncated kernel `K 1_{‖z‖>δ}`. -/
def pvkKtr (K : 𝔼 → ℝ) (δ : ℝ) (z : 𝔼) : ℝ := if δ < ‖z‖ then K z else 0

section Basic

variable {K : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ}

lemma pvk_K_zero (hd : 1 ≤ d) (hK : PvkKernel d K L) : K 0 = 0 := by
  have h := hK.hom 2 (by norm_num) 0
  simp only [smul_zero] at h
  have h2 : ((2:ℝ) ^ d)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]; right; exact one_lt_pow₀ (by norm_num) (by omega)
  nlinarith

lemma pvk_K_bound_unit (hK : PvkKernel d K L) {u : 𝔼} (hu : ‖u‖ = 1) : |K u| ≤ L := by
  have h := hK.lip u (-u) hu (by simpa using hu)
  rw [hK.odd u] at h
  have : ‖u - -u‖ = 2 := by
    rw [sub_neg_eq_add, ← two_smul ℝ u, norm_smul, hu]; norm_num
  rw [this] at h
  have : K u - -K u = 2 * K u := by ring
  rw [this, abs_mul] at h
  norm_num at h
  linarith

lemma pvk_K_bound (hd : 1 ≤ d) (hK : PvkKernel d K L) (z : 𝔼) :
    |K z| ≤ L * (‖z‖ ^ d)⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [pvk_K_zero hd hK]; simp [zero_pow (by omega : d ≠ 0)]
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hu : ‖‖z‖⁻¹ • z‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have := hK.hom ‖z‖ hn (‖z‖⁻¹ • z)
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] at this
    rw [this, abs_mul, abs_of_nonneg (by positivity)]
    calc (‖z‖ ^ d)⁻¹ * |K (‖z‖⁻¹ • z)| ≤ (‖z‖ ^ d)⁻¹ * L :=
          mul_le_mul_of_nonneg_left (pvk_K_bound_unit hK hu) (by positivity)
      _ = L * (‖z‖ ^ d)⁻¹ := mul_comm _ _

end Basic


section Lipschitz

variable {K : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ}

/-- Real inequality: Lipschitz bound for `t ↦ t^{-d}` on `[a/2, 3a/2]`. -/
lemma pvk_pow_inv_diff (d : ℕ) (hd : 1 ≤ d) {a b : ℝ} (ha : 0 < a) (hb1 : a / 2 ≤ b)
    (hb2 : b ≤ 3 * a / 2) :
    |(b ^ d)⁻¹ - (a ^ d)⁻¹| ≤ |a - b| * (d * 4 ^ d) * ((a ^ d)⁻¹ * a⁻¹) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hb : 0 < b := by linarith
  have e : (b ^ (m+1))⁻¹ - (a ^ (m+1))⁻¹ =
      (a ^ (m+1) - b ^ (m+1)) * ((a ^ (m+1))⁻¹ * (b ^ (m+1))⁻¹) := by
    field_simp
  rw [e, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (a ^ (m+1))⁻¹ * (b ^ (m+1))⁻¹)]
  have h1 := abs_pow_sub_pow_le (n := m + 1) a b
  have hmax : max |a| |b| ≤ 2 * a := by
    rw [abs_of_pos ha, abs_of_pos hb]; exact max_le (by linarith) (by linarith)
  have h2 : (max |a| |b|) ^ (m + 1 - 1) ≤ (2 * a) ^ m := by
    rw [Nat.add_sub_cancel]
    exact pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg a)) hmax m
  have h3 : (b ^ (m+1))⁻¹ ≤ 2 ^ (m+1) * (a ^ (m+1))⁻¹ := by
    have : (a / 2) ^ (m+1) ≤ b ^ (m+1) := pow_le_pow_left₀ (by positivity) hb1 _
    calc (b ^ (m+1))⁻¹ ≤ ((a / 2) ^ (m+1))⁻¹ := inv_anti₀ (by positivity) this
      _ = 2 ^ (m+1) * (a ^ (m+1))⁻¹ := by rw [div_pow]; field_simp
  have h4 : a ^ m * (a ^ (m+1))⁻¹ = a⁻¹ := by
    rw [pow_succ]; field_simp
  have hpa : 0 < (a ^ (m+1))⁻¹ := by positivity
  calc |a ^ (m+1) - b ^ (m+1)| * ((a ^ (m+1))⁻¹ * (b ^ (m+1))⁻¹)
      ≤ (|a - b| * ((m + 1 : ℕ) : ℝ) * (2 * a) ^ m) *
          ((a ^ (m+1))⁻¹ * (2 ^ (m+1) * (a ^ (m+1))⁻¹)) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = |a - b| * ((m + 1 : ℕ) : ℝ) * (2 ^ m * 2 ^ (m + 1)) *
          ((a ^ m * (a ^ (m+1))⁻¹) * (a ^ (m+1))⁻¹) := by
        rw [mul_pow]; ring
    _ = |a - b| * ((m + 1 : ℕ) : ℝ) * (2 ^ m * 2 ^ (m + 1)) *
          (a⁻¹ * (a ^ (m+1))⁻¹) := by rw [h4]
    _ ≤ |a - b| * ((m + 1 : ℕ) : ℝ) * (4 ^ (m + 1)) * (a⁻¹ * (a ^ (m+1))⁻¹) := by
        have : (2:ℝ) ^ m * 2 ^ (m + 1) ≤ 4 ^ (m + 1) := by
          calc (2:ℝ) ^ m * 2 ^ (m + 1) ≤ 2 ^ (m+1) * 2 ^ (m + 1) := by
                gcongr <;> norm_num
            _ = 4 ^ (m + 1) := by rw [← mul_pow]; norm_num
        gcongr
    _ = _ := by ring


/-- Lipschitz bound for the homogeneous kernel away from the origin. -/
lemma pvk_K_diff (hd : 1 ≤ d) (hK : PvkKernel d K L) {x y : 𝔼} (hx : x ≠ 0)
    (hxy : ‖y - x‖ ≤ ‖x‖ / 2) :
    |K y - K x| ≤ ((4 + d) * 4 ^ d) * L * (‖y - x‖ * ((‖x‖ ^ d)⁻¹ * ‖x‖⁻¹)) := by
  set a := ‖x‖ with ha_def
  set b := ‖y‖ with hb_def
  set t := ‖y - x‖ with ht_def
  have ha : 0 < a := norm_pos_iff.2 hx
  have ht0 : 0 ≤ t := norm_nonneg _
  have hb1 : a / 2 ≤ b := by
    have := norm_sub_norm_le x y
    rw [norm_sub_rev] at this
    linarith
  have hb2 : b ≤ 3 * a / 2 := by
    have : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
      calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith
  have hb : 0 < b := by linarith
  set u : 𝔼 := a⁻¹ • x with hu_def
  set v : 𝔼 := b⁻¹ • y with hv_def
  have hu : ‖u‖ = 1 := by rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ha.ne']
  have hv : ‖v‖ = 1 := by
    rw [hv_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hb.ne']
  have hKx : K x = (a ^ d)⁻¹ * K u := by
    have := hK.hom a ha u
    rwa [hu_def, smul_inv_smul₀ ha.ne'] at this
  have hKy : K y = (b ^ d)⁻¹ * K v := by
    have := hK.hom b hb v
    rwa [hv_def, smul_inv_smul₀ hb.ne'] at this
  -- direction difference
  have hvu : ‖v - u‖ ≤ 4 * t / a := by
    have e : v - u = b⁻¹ • (y - x) + (b⁻¹ - a⁻¹) • x := by
      rw [hv_def, hu_def]; module
    have h1 : ‖v - u‖ ≤ b⁻¹ * t + |b⁻¹ - a⁻¹| * a := by
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hb]
    have hab : |a - b| ≤ t := by
      have := abs_norm_sub_norm_le x y
      rwa [norm_sub_rev] at this
    have h2 : |b⁻¹ - a⁻¹| * a = |a - b| / b := by
      have : b⁻¹ - a⁻¹ = (a - b) / (a * b) := by field_simp
      rw [this, abs_div, abs_of_pos (mul_pos ha hb)]
      field_simp
    have h3 : b⁻¹ ≤ 2 / a := by
      rw [inv_eq_one_div, div_le_div_iff₀ hb ha]; linarith
    calc ‖v - u‖ ≤ b⁻¹ * t + |a - b| / b := by rw [← h2]; exact h1
      _ ≤ b⁻¹ * t + t * b⁻¹ := by
          have : |a - b| / b ≤ t * b⁻¹ := by
            rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right hab (inv_nonneg.2 hb.le)
          linarith
      _ = 2 * (b⁻¹ * t) := by ring
      _ ≤ 2 * (2 / a * t) := by gcongr
      _ = 4 * t / a := by ring
  have hbinv : (b ^ d)⁻¹ ≤ 2 ^ d * (a ^ d)⁻¹ := by
    have : (a / 2) ^ d ≤ b ^ d := pow_le_pow_left₀ (by positivity) hb1 _
    calc (b ^ d)⁻¹ ≤ ((a / 2) ^ d)⁻¹ := inv_anti₀ (by positivity) this
      _ = 2 ^ d * (a ^ d)⁻¹ := by rw [div_pow]; field_simp
  have hdiff := pvk_pow_inv_diff d hd ha hb1 hb2
  have hab : |a - b| ≤ t := by
    have := abs_norm_sub_norm_le x y
    rwa [norm_sub_rev] at this
  have hKu := pvk_K_bound_unit hK hu
  have hLip := hK.lip v u hv hu
  have hL := hK.nonneg
  have hP : 0 < (a ^ d)⁻¹ * a⁻¹ := by positivity
  have e2 : K y - K x = (b ^ d)⁻¹ * (K v - K u) + ((b ^ d)⁻¹ - (a ^ d)⁻¹) * K u := by
    rw [hKx, hKy]; ring
  have hbpos : 0 < (b ^ d)⁻¹ := by positivity
  calc |K y - K x| = |(b ^ d)⁻¹ * (K v - K u) + ((b ^ d)⁻¹ - (a ^ d)⁻¹) * K u| := by rw [e2]
    _ ≤ (b ^ d)⁻¹ * |K v - K u| + |(b ^ d)⁻¹ - (a ^ d)⁻¹| * |K u| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos hbpos]
    _ ≤ (2 ^ d * (a ^ d)⁻¹) * (L * (4 * t / a)) +
          (t * (d * 4 ^ d) * ((a ^ d)⁻¹ * a⁻¹)) * L := by
        gcongr
        · exact hLip.trans (by gcongr)
        · exact hdiff.trans (by gcongr)
    _ = (4 * 2 ^ d + d * 4 ^ d) * L * (t * ((a ^ d)⁻¹ * a⁻¹)) := by
        field_simp
    _ ≤ ((4 + d) * 4 ^ d) * L * (t * ((a ^ d)⁻¹ * a⁻¹)) := by
        have : (2:ℝ) ^ d ≤ 4 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) _
        gcongr
        nlinarith

end Lipschitz


section KP

variable {K : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} {φ : EuclideanSpace ℝ (Fin d) → ℝ} {Lφ M : ℝ}

/-- `KP z = lim_{δ → 0+} ∫_{|y|>δ} K y φ(z-y) dy` (the principal value of `K * φ`; the integral
over `{|y| > δ}` is a Bochner integral of an integrable function). -/
def pvkTrunc (K φ : 𝔼 → ℝ) (δ : ℝ) (z : 𝔼) : ℝ := ∫ y, pvkKtr K δ y * φ (z - y)

/-- The principal value `KP`. -/
def pvkKP (K φ : 𝔼 → ℝ) (z : 𝔼) : ℝ := limUnder (𝓝[>] (0:ℝ)) (fun δ => pvkTrunc K φ δ z)

/-- `Ψ = K 1_{|z|>1} - KP`. -/
def pvkPsi (K φ : 𝔼 → ℝ) (z : 𝔼) : ℝ := pvkKtr K 1 z - pvkKP K φ z

/-- The near-field integrand `K y (φ(z-y) - φ z)`. -/
def pvkG (K φ : 𝔼 → ℝ) (z y : 𝔼) : ℝ := K y * (φ (z - y) - φ z)

lemma pvk_bump_cont (hφ : PvkBump d φ Lφ M) : Continuous φ := by
  have : LipschitzWith ⟨Lφ, hφ.lip_nonneg⟩ φ := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    rw [Real.dist_eq, dist_eq_norm]
    exact hφ.lip z w
  exact this.continuous

lemma pvk_bump_M_nonneg (hφ : PvkBump d φ Lφ M) : 0 ≤ M := (hφ.nonneg 0).trans (hφ.bdd 0)

lemma pvk_Ktr_eq (K : 𝔼 → ℝ) (δ : ℝ) :
    pvkKtr K δ = {y : 𝔼 | δ < ‖y‖}.indicator K := by
  funext y; simp [pvkKtr, Set.indicator]

lemma pvk_Ktr_meas (hK : PvkKernel d K L) (δ : ℝ) : Measurable (pvkKtr K δ) := by
  rw [pvk_Ktr_eq]
  exact hK.meas.indicator (measurableSet_lt measurable_const measurable_norm)

lemma pvk_Ktr_bound (hd : 1 ≤ d) (hK : PvkKernel d K L) {δ : ℝ} (hδ : 0 < δ) (y : 𝔼) :
    |pvkKtr K δ y| ≤ L * (δ ^ d)⁻¹ := by
  unfold pvkKtr
  split_ifs with h
  · refine (pvk_K_bound hd hK y).trans ?_
    have : δ ^ d ≤ ‖y‖ ^ d := pow_le_pow_left₀ hδ.le h.le _
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) this) hK.nonneg
  · simp; exact mul_nonneg hK.nonneg (by positivity)

/-- A bounded measurable function supported in a closed ball is integrable. -/
lemma pvk_integrable_of_bdd {f : 𝔼 → ℝ} (hf : AEStronglyMeasurable f volume) {c : ℝ} (z : 𝔼) (r : ℝ)
    (hc : ∀ y, ‖f y‖ ≤ c) (hs : ∀ y, f y ≠ 0 → y ∈ closedBall z r) : Integrable f := by
  have hi : Integrable ((closedBall z r).indicator fun _ => c) :=
    (integrableOn_const (measure_closedBall_lt_top (x := z) (r := r)).ne).integrable_indicator
      measurableSet_closedBall
  refine hi.mono' hf (ae_of_all _ fun y => ?_)
  by_cases hy : f y = 0
  · simp only [hy, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => (norm_nonneg _).trans (hc y)) y
  · rw [Set.indicator_of_mem (hs y hy)]; exact hc y

lemma pvk_Ktr_integrable (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) {δ : ℝ}
    (hδ : 0 < δ) (z : 𝔼) : Integrable (fun y => pvkKtr K δ y * φ (z - y)) := by
  refine pvk_integrable_of_bdd ?_ (c := L * (δ ^ d)⁻¹ * M) z 1 ?_ ?_
  · exact ((pvk_Ktr_meas hK δ).mul ((pvk_bump_cont hφ).measurable.comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
  · intro y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφ.nonneg _)]
    exact mul_le_mul (pvk_Ktr_bound hd hK hδ y) (hφ.bdd _) (hφ.nonneg _)
      (mul_nonneg hK.nonneg (by positivity))
  · intro y hy
    rw [mem_closedBall, dist_eq_norm]
    by_contra h
    have := hφ.supp (z - y) (by rw [norm_sub_rev]; exact not_le.1 h)
    exact hy (by simp [this])



/-- Near-field part of `KP`. -/
def pvkI1 (K φ : 𝔼 → ℝ) (z : 𝔼) : ℝ := ∫ y, (ball (0:𝔼) 1).indicator (pvkG K φ z) y

/-- Far-field part of `KP`. -/
def pvkI2 (K φ : 𝔼 → ℝ) (z : 𝔼) : ℝ :=
  ∫ y, {y : 𝔼 | 1 ≤ ‖y‖}.indicator (fun y => K y * φ (z - y)) y

lemma pvk_integral_odd {f : 𝔼 → ℝ} (h : ∀ y, f (-y) = -f y) : ∫ y, f y = 0 := by
  have h1 : ∫ y, f (-y) = ∫ y, f y := integral_neg_eq_self f volume
  simp_rw [h] at h1
  rw [integral_neg] at h1
  linarith

lemma pvk_G_meas (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) (z : 𝔼) :
    Measurable (pvkG K φ z) :=
  hK.meas.mul (((pvk_bump_cont hφ).measurable.comp (measurable_const.sub measurable_id)).sub
    measurable_const)

lemma pvk_G_bound (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) (z y : 𝔼) :
    ‖pvkG K φ z y‖ ≤ (L * Lφ) * ‖y‖ ^ (-((d:ℝ) - 1)) := by
  have hnn : 0 ≤ (L * Lφ) * ‖y‖ ^ (-((d:ℝ) - 1)) :=
    mul_nonneg (mul_nonneg hK.nonneg hφ.lip_nonneg) (Real.rpow_nonneg (norm_nonneg _) _)
  rcases eq_or_ne y 0 with rfl | hy
  · simpa [pvkG, pvk_K_zero hd hK] using hnn
  · have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
    have h1 := pvk_K_bound hd hK y
    have h2 : |φ (z - y) - φ z| ≤ Lφ * ‖y‖ := by
      have := hφ.lip (z - y) z
      rwa [sub_sub_cancel_left, norm_neg] at this
    have e : ‖y‖ ^ (-((d:ℝ) - 1)) = ‖y‖ * (‖y‖ ^ d)⁻¹ := by
      rw [show -((d:ℝ) - 1) = 1 + -(d:ℝ) by ring, Real.rpow_add hn, Real.rpow_one,
        Real.rpow_neg hn.le, Real.rpow_natCast]
    rw [Real.norm_eq_abs, pvkG, abs_mul, e]
    calc |K y| * |φ (z - y) - φ z| ≤ (L * (‖y‖ ^ d)⁻¹) * (Lφ * ‖y‖) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hK.nonneg (by positivity))
      _ = _ := by ring

lemma pvk_G_integrableOn (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) (z : 𝔼) :
    IntegrableOn (pvkG K φ z) (ball (0:𝔼) 1) := by
  refine integrableOn_ball_of_norm_le_rpow (by rw [finrank_euclideanSpace_fin]; exact hd)
    (C := L * Lφ) (α := (d:ℝ) - 1) (by rw [finrank_euclideanSpace_fin]; linarith)
    (ae_of_all _ fun y => pvk_G_bound hd hK hφ z y)
    (pvk_G_meas hK hφ z).aestronglyMeasurable

lemma pvk_I2_integrable (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) (z : 𝔼) :
    Integrable ({y : 𝔼 | 1 ≤ ‖y‖}.indicator (fun y => K y * φ (z - y))) := by
  refine pvk_integrable_of_bdd ?_ (c := L * M) z 1 ?_ ?_
  · exact (hK.meas.mul ((pvk_bump_cont hφ).measurable.comp
      (measurable_const.sub measurable_id))).indicator
      (measurableSet_le measurable_const measurable_norm) |>.aestronglyMeasurable
  · intro y
    by_cases hy : 1 ≤ ‖y‖
    · rw [Set.indicator_of_mem (show y ∈ {y : 𝔼 | 1 ≤ ‖y‖} from hy), Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (hφ.nonneg _)]
      have hKy : |K y| ≤ L := by
        refine (pvk_K_bound hd hK y).trans ?_
        have : (1:ℝ) ≤ ‖y‖ ^ d := one_le_pow₀ hy
        have : (‖y‖ ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
        nlinarith [hK.nonneg]
      exact mul_le_mul hKy (hφ.bdd _) (hφ.nonneg _) hK.nonneg
    · rw [Set.indicator_of_notMem (show y ∉ {y : 𝔼 | 1 ≤ ‖y‖} from hy)]
      simpa using mul_nonneg hK.nonneg (pvk_bump_M_nonneg hφ)
  · intro y hy
    rw [mem_closedBall, dist_eq_norm]
    by_contra h
    have := hφ.supp (z - y) (by rw [norm_sub_rev]; exact not_le.1 h)
    apply hy
    simp [Set.indicator, this]



lemma pvk_annulus_odd (hK : PvkKernel d K L) (δ : ℝ) :
    ∫ y, {y : 𝔼 | δ < ‖y‖ ∧ ‖y‖ < 1}.indicator K y = 0 := by
  refine pvk_integral_odd fun y => ?_
  by_cases h : δ < ‖y‖ ∧ ‖y‖ < 1
  · have h' : -y ∈ {y : 𝔼 | δ < ‖y‖ ∧ ‖y‖ < 1} := by simpa [norm_neg] using h
    rw [Set.indicator_of_mem h', Set.indicator_of_mem (show y ∈ {y : 𝔼 | δ < ‖y‖ ∧ ‖y‖ < 1} from h),
      hK.odd]
  · have h' : -y ∉ {y : 𝔼 | δ < ‖y‖ ∧ ‖y‖ < 1} := by simpa [norm_neg] using h
    rw [Set.indicator_of_notMem h', Set.indicator_of_notMem
      (show y ∉ {y : 𝔼 | δ < ‖y‖ ∧ ‖y‖ < 1} from h), neg_zero]

lemma pvk_trunc_tendsto (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) (z : 𝔼) :
    Tendsto (fun δ => pvkTrunc K φ δ z) (𝓝[>] 0) (𝓝 (pvkI1 K φ z + pvkI2 K φ z)) := by
  set A : ℝ → Set 𝔼 := fun δ => {y | δ < ‖y‖ ∧ ‖y‖ < 1} with hA
  have hAm : ∀ δ, MeasurableSet (A δ) := fun δ =>
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have hAB : ∀ δ, A δ ⊆ ball 0 1 := fun δ y hy => by
    have : ‖y‖ < 1 := hy.2
    simpa using this
  set f1 : ℝ → 𝔼 → ℝ := fun δ => (A δ).indicator (pvkG K φ z) with hf1
  have hGi := pvk_G_integrableOn hd hK hφ z
  have hf1i : ∀ δ, Integrable (f1 δ) := fun δ =>
    (hGi.mono_set (hAB δ)).integrable_indicator (hAm δ)
  have hI2i := pvk_I2_integrable hd hK hφ z
  have hlim : Tendsto (fun δ => ∫ y, f1 δ y) (𝓝[>] 0) (𝓝 (pvkI1 K φ z)) := by
    unfold pvkI1
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => ‖(ball (0:𝔼) 1).indicator (pvkG K φ z) y‖) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun δ => (hf1i δ).aestronglyMeasurable
    · refine Eventually.of_forall fun δ => ae_of_all _ fun y => ?_
      by_cases h : y ∈ A δ
      · simp only [hf1]
        rw [Set.indicator_of_mem h, Set.indicator_of_mem (hAB δ h)]
      · simp only [hf1]
        rw [Set.indicator_of_notMem h]; simp
    · exact (hGi.integrable_indicator measurableSet_ball).norm
    · refine ae_of_all _ fun y => ?_
      by_cases hy : y = 0
      · subst hy
        have h0 : pvkG K φ z 0 = 0 := by simp [pvkG, pvk_K_zero hd hK]
        have : ∀ δ, f1 δ 0 = 0 := fun δ => by
          simp only [hf1]; by_cases h : (0:𝔼) ∈ A δ
          · rw [Set.indicator_of_mem h]; exact h0
          · rw [Set.indicator_of_notMem h]
        simp only [this]
        by_cases hb : (0:𝔼) ∈ ball (0:𝔼) 1
        · rw [Set.indicator_of_mem hb, h0]; exact tendsto_const_nhds
        · rw [Set.indicator_of_notMem hb]; exact tendsto_const_nhds
      · have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
        by_cases hy1 : ‖y‖ < 1
        · have hb : y ∈ ball (0:𝔼) 1 := by simpa using hy1
          rw [Set.indicator_of_mem hb]
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [Ioo_mem_nhdsGT hn] with δ hδ
          simp only [hf1]
          rw [Set.indicator_of_mem (show y ∈ A δ from ⟨hδ.2, hy1⟩)]
        · have hb : y ∉ ball (0:𝔼) 1 := by simpa using hy1
          rw [Set.indicator_of_notMem hb]
          have : ∀ δ, f1 δ y = 0 := fun δ => by
            simp only [hf1]
            rw [Set.indicator_of_notMem (fun h => hy1 h.2)]
          simp only [this]; exact tendsto_const_nhds
  have heq : ∀ᶠ δ in 𝓝[>] (0:ℝ), (∫ y, f1 δ y) + pvkI2 K φ z = pvkTrunc K φ δ z := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with δ hδ
    have hδ0 : 0 < δ := hδ.1
    have hf2i : Integrable (fun y => φ z * (A δ).indicator K y) := by
      refine Integrable.const_mul ?_ _
      refine pvk_integrable_of_bdd ?_ (c := L * (δ ^ d)⁻¹) 0 1 ?_ ?_
      · exact (hK.meas.indicator (hAm δ)).aestronglyMeasurable
      · intro y
        by_cases h : y ∈ A δ
        · rw [Set.indicator_of_mem h]
          have := pvk_K_bound hd hK y
          have h2 : δ ^ d ≤ ‖y‖ ^ d := pow_le_pow_left₀ hδ0.le h.1.le _
          exact (pvk_K_bound hd hK y).trans
            (mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h2) hK.nonneg)
        · rw [Set.indicator_of_notMem h]; simp
          exact mul_nonneg hK.nonneg (by positivity)
      · intro y hy
        by_contra hc
        apply hy
        rw [Set.indicator_of_notMem]
        intro h
        apply hc
        have : ‖y‖ < 1 := h.2
        rw [mem_closedBall, dist_zero_right]; exact this.le
    have hpt : ∀ y, pvkKtr K δ y * φ (z - y) = f1 δ y + φ z * (A δ).indicator K y +
        {y : 𝔼 | 1 ≤ ‖y‖}.indicator (fun y => K y * φ (z - y)) y := by
      intro y
      by_cases h1 : δ < ‖y‖
      · by_cases h2 : ‖y‖ < 1
        · have hy : y ∈ A δ := ⟨h1, h2⟩
          have hy2 : y ∉ {y : 𝔼 | 1 ≤ ‖y‖} := fun h => absurd (show 1 ≤ ‖y‖ from h) (not_le.2 h2)
          simp only [hf1, pvkKtr, h1, ↓reduceIte, Set.indicator_of_mem hy, Set.indicator_of_notMem hy2,
            pvkG]
          ring
        · have hy : y ∉ A δ := fun h => h2 h.2
          have hy2 : y ∈ {y : 𝔼 | 1 ≤ ‖y‖} := not_lt.1 h2
          simp only [hf1, pvkKtr, h1, ↓reduceIte, Set.indicator_of_notMem hy, Set.indicator_of_mem hy2]
          ring
      · have hy : y ∉ A δ := fun h => h1 h.1
        have hy2 : y ∉ {y : 𝔼 | 1 ≤ ‖y‖} := fun h => h1 (lt_of_lt_of_le hδ.2 h)
        simp only [hf1, pvkKtr, h1, ↓reduceIte, Set.indicator_of_notMem hy,
          Set.indicator_of_notMem hy2]
        ring
    unfold pvkTrunc pvkI2
    simp_rw [hpt]
    have hs : Integrable (fun y => f1 δ y + φ z * (A δ).indicator K y) := (hf1i δ).add hf2i
    rw [integral_add hs hI2i, integral_add (hf1i δ) hf2i, integral_const_mul,
      pvk_annulus_odd hK, mul_zero, add_zero]
  exact (hlim.add tendsto_const_nhds).congr' heq



lemma pvk_bump_integrable (hφ : PvkBump d φ Lφ M) : Integrable φ := by
  by_contra h
  have := hφ.integral_eq_one
  rw [integral_undef h] at this
  exact zero_ne_one this

lemma pvk_KP_eq (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) (z : 𝔼) :
    pvkKP K φ z = pvkI1 K φ z + pvkI2 K φ z :=
  (pvk_trunc_tendsto hd hK hφ z).limUnder_eq

lemma pvk_I1_integrable_bound (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) :
    Integrable ((ball (0:𝔼) 1).indicator fun y : 𝔼 => (L * Lφ) * ‖y‖ ^ (-((d:ℝ) - 1))) := by
  refine IntegrableOn.integrable_indicator ?_ measurableSet_ball
  refine integrableOn_ball_of_norm_le_rpow (by rw [finrank_euclideanSpace_fin]; exact hd)
    (C := L * Lφ) (α := (d:ℝ) - 1) (by rw [finrank_euclideanSpace_fin]; linarith)
    (ae_of_all _ fun y => ?_)
    ((measurable_const.mul (measurable_norm.pow_const _)).aestronglyMeasurable)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hK.nonneg hφ.lip_nonneg)
    (Real.rpow_nonneg (norm_nonneg _) _))]

lemma pvk_I1_bound (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) (z : 𝔼) :
    |pvkI1 K φ z| ≤ ∫ y, (ball (0:𝔼) 1).indicator
      (fun y : 𝔼 => (L * Lφ) * ‖y‖ ^ (-((d:ℝ) - 1))) y := by
  unfold pvkI1
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (pvk_I1_integrable_bound hd hK hφ) (ae_of_all _ fun y => ?_)
  by_cases h : y ∈ ball (0:𝔼) 1
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; exact pvk_G_bound hd hK hφ z y
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; simp

lemma pvk_I2_bound (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) (z : 𝔼) :
    |pvkI2 K φ z| ≤ L * M * (volume (closedBall (0:𝔼) 1)).toReal := by
  unfold pvkI2
  rw [← Real.norm_eq_abs]
  have hi : Integrable ((closedBall z 1).indicator fun _ : 𝔼 => L * M) :=
    (integrableOn_const (measure_closedBall_lt_top (x := z) (r := 1)).ne).integrable_indicator
      measurableSet_closedBall
  have := norm_integral_le_of_norm_le hi (f := {y : 𝔼 | 1 ≤ ‖y‖}.indicator fun y => K y * φ (z - y))
    (ae_of_all _ fun y => ?_)
  · refine this.trans (le_of_eq ?_)
    rw [integral_indicator_const _ measurableSet_closedBall]
    simp [Measure.real, Measure.addHaar_closedBall_center]
    ring
  · by_cases hy : y ∈ {y : 𝔼 | 1 ≤ ‖y‖}
    · by_cases hc : y ∈ closedBall z 1
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hc, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (hφ.nonneg _)]
        have hy' : 1 ≤ ‖y‖ := hy
        have hKy : |K y| ≤ L := by
          refine (pvk_K_bound hd hK y).trans ?_
          have : (1:ℝ) ≤ ‖y‖ ^ d := one_le_pow₀ hy'
          have : (‖y‖ ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
          nlinarith [hK.nonneg]
        exact mul_le_mul hKy (hφ.bdd _) (hφ.nonneg _) hK.nonneg
      · have : φ (z - y) = 0 := by
          apply hφ.supp
          rw [mem_closedBall, dist_eq_norm] at hc
          rw [norm_sub_rev]; exact not_le.1 hc
        rw [Set.indicator_of_mem hy, this]
        simp; exact (Set.indicator_nonneg (fun _ _ => mul_nonneg hK.nonneg (pvk_bump_M_nonneg hφ)) y)
    · rw [Set.indicator_of_notMem hy]; simp
      exact (Set.indicator_nonneg (fun _ _ => mul_nonneg hK.nonneg (pvk_bump_M_nonneg hφ)) y)

lemma pvk_KP_bounded (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) :
    ∃ c : ℝ, ∀ z, |pvkKP K φ z| ≤ c := by
  refine ⟨(∫ y, (ball (0:𝔼) 1).indicator
      (fun y : 𝔼 => (L * Lφ) * ‖y‖ ^ (-((d:ℝ) - 1))) y) +
    L * M * (volume (closedBall (0:𝔼) 1)).toReal, fun z => ?_⟩
  rw [pvk_KP_eq hd hK hφ]
  exact (abs_add_le _ _).trans (add_le_add (pvk_I1_bound hd hK hφ z) (pvk_I2_bound hd hK hφ z))

lemma pvk_KP_measurable (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) :
    Measurable (pvkKP K φ) := by
  have hφm := (pvk_bump_cont hφ).measurable
  have hm1 : Measurable (fun q : 𝔼 × 𝔼 => (ball (0:𝔼) 1).indicator (pvkG K φ q.1) q.2) := by
    have h1 : Measurable (fun q : 𝔼 × 𝔼 => pvkG K φ q.1 q.2) :=
      (hK.meas.comp measurable_snd).mul
        ((hφm.comp (measurable_fst.sub measurable_snd)).sub (hφm.comp measurable_fst))
    have h2 : MeasurableSet {q : 𝔼 × 𝔼 | q.2 ∈ ball (0:𝔼) 1} :=
      measurable_snd measurableSet_ball
    have := h1.indicator h2
    convert this using 1
    funext q; simp [Set.indicator]
  have hm2 : Measurable (fun q : 𝔼 × 𝔼 =>
      {y : 𝔼 | 1 ≤ ‖y‖}.indicator (fun y => K y * φ (q.1 - y)) q.2) := by
    have h1 : Measurable (fun q : 𝔼 × 𝔼 => K q.2 * φ (q.1 - q.2)) :=
      (hK.meas.comp measurable_snd).mul (hφm.comp (measurable_fst.sub measurable_snd))
    have h2 : MeasurableSet {q : 𝔼 × 𝔼 | q.2 ∈ {y : 𝔼 | 1 ≤ ‖y‖}} :=
      measurable_snd (measurableSet_le measurable_const measurable_norm)
    have := h1.indicator h2
    convert this using 1
    funext q; simp [Set.indicator]
  have e : pvkKP K φ = fun z => pvkI1 K φ z + pvkI2 K φ z := funext (pvk_KP_eq hd hK hφ)
  rw [e]
  refine Measurable.add ?_ ?_
  · exact (hm1.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  · exact (hm2.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

lemma pvk_KP_odd (hd : 1 ≤ d) (hK : PvkKernel d K L) (hφ : PvkBump d φ Lφ M) (z : 𝔼) :
    pvkKP K φ (-z) = -pvkKP K φ z := by
  rw [pvk_KP_eq hd hK hφ, pvk_KP_eq hd hK hφ]
  have h1 : pvkI1 K φ (-z) = -pvkI1 K φ z := by
    unfold pvkI1
    rw [← integral_neg_eq_self (fun y => (ball (0:𝔼) 1).indicator (pvkG K φ (-z)) y) volume,
      ← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    beta_reduce
    have hb : (-y ∈ ball (0:𝔼) 1) ↔ (y ∈ ball (0:𝔼) 1) := by simp
    by_cases h : y ∈ ball (0:𝔼) 1
    · rw [Set.indicator_of_mem (hb.2 h), Set.indicator_of_mem h]
      simp only [pvkG, hK.odd, hφ.even]
      have : φ (-z - -y) = φ (z - y) := by rw [← hφ.even, neg_sub_neg, neg_sub]
      rw [this]; ring
    · rw [Set.indicator_of_notMem (fun h' => h (hb.1 h')), Set.indicator_of_notMem h]; simp
  have h2 : pvkI2 K φ (-z) = -pvkI2 K φ z := by
    unfold pvkI2
    rw [← integral_neg_eq_self (fun y => {y : 𝔼 | 1 ≤ ‖y‖}.indicator (fun y => K y * φ (-z - y)) y)
      volume, ← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    beta_reduce
    by_cases h : 1 ≤ ‖y‖
    · rw [Set.indicator_of_mem (show -y ∈ {y : 𝔼 | 1 ≤ ‖y‖} by simpa using h),
        Set.indicator_of_mem (show y ∈ {y : 𝔼 | 1 ≤ ‖y‖} from h)]
      have : φ (-z - -y) = φ (z - y) := by rw [← hφ.even, neg_sub_neg, neg_sub]
      rw [this, hK.odd]; ring
    · rw [Set.indicator_of_notMem (show -y ∉ {y : 𝔼 | 1 ≤ ‖y‖} by simpa using h),
        Set.indicator_of_notMem (show y ∉ {y : 𝔼 | 1 ≤ ‖y‖} from h)]; simp
  rw [h1, h2]; ring

end KP

end HRS.CZ.Pvk
