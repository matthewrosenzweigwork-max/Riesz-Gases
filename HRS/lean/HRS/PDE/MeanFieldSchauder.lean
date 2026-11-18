import HRS.PDE.MeanFieldHolder
import HRS.Kernel.GradSmooth

/-!
# A Schauder-type gain for convolution with the Riesz kernel (package MF-01, packet P4b)

For a kernel `g` on `𝕋^d` with `|g(z)| ≲ ‖z‖^{-p}`, `|∇g(z)| ≲ ‖z‖^{-p-1}`, `p < d` (torus norm), and
`h ∈ C^{0,a}`:

* `conv_holder`:  `g ⋆ h ∈ C^{0,γ}` for `a ≤ γ ≤ 1`, `γ < a + (d - p)`;
* `cross_*`: if `a + (d - p) > 1`, then `g ⋆ h ∈ C¹` with `∇(g ⋆ h)(x) = ∫ (h(x-z) - h(x)) ∇g(z) dz`
  of class `C^{0,γ'}`, `γ' ≤ a`, `γ' < a + (d - p) - 1`.

All kernel integrals are controlled by the single family `∫ ‖z‖^{-q}`, `q < d`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.PDE.MFSchauder

variable {d : ℕ}

/-! ### Elementary facts on the torus -/

theorem norm_mk_le {x : Euc d} {r : ℝ} (hr : 0 ≤ r) (h : ∀ i, |x i| ≤ r) : ‖Torus.mk x‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg hr).2 fun i => ?_
  have := QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ)) (m := x i)
  have h2 : ‖((x i : ℝ) : UnitAddCircle)‖ ≤ |x i| := by simpa using this
  exact h2.trans (h i)

theorem exists_lift (z : Torus d) : ∃ x : Euc d, Torus.mk x = z ∧ ∀ i, |x i| ≤ ‖z‖ := by
  obtain ⟨x, hx, hb⟩ := KernelGrad.exists_mk_box z
  refine ⟨x, hx, fun i => ?_⟩
  have h1 : ‖((x i : ℝ) : UnitAddCircle)‖ = |x i| :=
    (AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2 (by simpa using hb i)
  have h2 : ‖z i‖ ≤ ‖z‖ := norm_le_pi_norm z i
  have h3 : z i = ((x i : ℝ) : UnitAddCircle) := by rw [← hx]; rfl
  rw [← h1, ← h3]
  exact h2

theorem ae_add_ne_zero (hd : 0 < d) (y : Torus d) : ∀ᵐ z : Torus d, z + y ≠ 0 := by
  have h := (measurePreserving_add_right (volume : Measure (Torus d)) y).quasiMeasurePreserving
  exact h.ae (KernelGrad.torus_ae_ne' hd)

theorem norm_euc_le {x : Euc d} {r : ℝ} (hd : 0 < d) (hr : 0 ≤ r) (h : ∀ i, |x i| ≤ r) :
    ‖x‖ ≤ d * r := by
  have h1 : ‖(fun i => x i : Fin d → ℝ)‖ ≤ r :=
    (pi_norm_le_iff_of_nonneg hr).2 fun i => by simpa using h i
  have h2 := HRS.KernelAux2.norm_toLp_le_card_mul hd (fun i => x i)
  have h3 : (WithLp.toLp 2 (fun i => x i) : Euc d) = x := rfl
  rw [h3] at h2
  exact h2.trans (mul_le_mul_of_nonneg_left h1 (by positivity))

/-! ### The kernel bundle -/

/-- Pointwise bounds on a kernel `g` and its gradient `G`, in terms of the torus norm. -/
structure KB (d : ℕ) (g : Torus d → ℝ) (G : Torus d → Euc d) (p C : ℝ) : Prop where
  hd : 0 < d
  p0 : 0 ≤ p
  pd : p < d
  C0 : 0 ≤ C
  gint : Integrable g
  Gmeas : Measurable G
  gb : ∀ z, z ≠ 0 → |g z| ≤ C * ‖z‖ ^ (-p)
  Gb : ∀ z, z ≠ 0 → ‖G z‖ ≤ C * ‖z‖ ^ (-p - 1)
  grad : ∀ x : Euc d, Torus.mk x ≠ 0 → HasGradientAt (Torus.lift g) (G (Torus.mk x)) x

variable {g : Torus d → ℝ} {G : Torus d → Euc d} {p C : ℝ}

theorem KB.mono (K : KB d g G p C) {p' : ℝ} (hp : p ≤ p') (hp' : p' < d) : KB d g G p' C := by
  refine ⟨K.hd, K.p0.trans hp, hp', K.C0, K.gint, K.Gmeas, fun z hz => ?_, fun z hz => ?_, K.grad⟩
  · have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    refine (K.gb z hz).trans (mul_le_mul_of_nonneg_left ?_ K.C0)
    exact Real.rpow_le_rpow_of_exponent_ge hz0 (by linarith [MFHolder.norm_torus_le_half z]) (by linarith)
  · have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    refine (K.Gb z hz).trans (mul_le_mul_of_nonneg_left ?_ K.C0)
    exact Real.rpow_le_rpow_of_exponent_ge hz0 (by linarith [MFHolder.norm_torus_le_half z]) (by linarith)

/-- The mean value bound for `g` away from the singularity. -/
theorem KB.diff_bound (K : KB d g G p C) {y z : Torus d} (hz : 2 * ‖y‖ < ‖z‖) :
    |g (z + y) - g z| ≤ (d * C * 2 ^ (p + 1)) * ‖y‖ * ‖z‖ ^ (-p - 1) := by
  obtain ⟨xz, hxz, hxzb⟩ := exists_lift z
  obtain ⟨xy, hxy, hxyb⟩ := exists_lift y
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hz0 : 0 < ‖z‖ := by linarith
  have hz2 : 0 < ‖z‖ / 2 := by positivity
  set B : ℝ := C * (‖z‖ / 2) ^ (-p - 1) with hB
  have hseg : ∀ w ∈ segment ℝ xz (xz + xy), ‖z‖ / 2 ≤ ‖Torus.mk w‖ := by
    intro w hw
    rw [segment_eq_image'] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    rw [add_sub_cancel_left, Torus.mk_add, hxz]
    have h1 : ‖Torus.mk (t • xy)‖ ≤ t * ‖y‖ := by
      refine norm_mk_le (mul_nonneg ht.1 hy0) (fun i => ?_)
      simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht.1]
      exact mul_le_mul_of_nonneg_left (hxyb i) ht.1
    have h2 : t * ‖y‖ ≤ ‖y‖ := by nlinarith [ht.2]
    have h3 : ‖z‖ ≤ ‖z + Torus.mk (t • xy)‖ + ‖Torus.mk (t • xy)‖ := by
      have := norm_sub_le (z + Torus.mk (t • xy)) (Torus.mk (t • xy))
      simpa using this
    linarith
  have hderiv : ∀ w ∈ segment ℝ xz (xz + xy),
      HasFDerivWithinAt (Torus.lift g) ((InnerProductSpace.toDual ℝ (Euc d)) (G (Torus.mk w)))
        (segment ℝ xz (xz + xy)) w := by
    intro w hw
    have hne : Torus.mk w ≠ 0 := by
      intro h0
      have := hseg w hw
      rw [h0, norm_zero] at this
      linarith
    exact ((hasGradientAt_iff_hasFDerivAt.1 (K.grad w hne))).hasFDerivWithinAt
  have hbound : ∀ w ∈ segment ℝ xz (xz + xy),
      ‖(InnerProductSpace.toDual ℝ (Euc d)) (G (Torus.mk w))‖ ≤ B := by
    intro w hw
    have hw2 := hseg w hw
    have hne : Torus.mk w ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hw2
      linarith
    rw [LinearIsometryEquiv.norm_map]
    refine (K.Gb _ hne).trans (mul_le_mul_of_nonneg_left ?_ K.C0)
    exact Real.rpow_le_rpow_of_nonpos hz2 hw2 (by linarith [K.p0])
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound
    (convex_segment xz (xz + xy)) (left_mem_segment ℝ xz (xz + xy)) (right_mem_segment ℝ xz (xz + xy))
  have e1 : Torus.lift g (xz + xy) = g (z + y) := by
    simp [Torus.lift, Torus.mk_add, hxz, hxy]
  have e2 : Torus.lift g xz = g z := by simp [Torus.lift, hxz]
  rw [e1, e2, add_sub_cancel_left, Real.norm_eq_abs] at hmv
  have hxyn : ‖xy‖ ≤ d * ‖y‖ := norm_euc_le K.hd hy0 hxyb
  have hB0 : 0 ≤ B := by
    have : 0 ≤ (‖z‖ / 2) ^ (-p - 1) := Real.rpow_nonneg hz2.le _
    rw [hB]; exact mul_nonneg K.C0 this
  have hhalf : (‖z‖ / 2) ^ (-p - 1) = 2 ^ (p + 1) * ‖z‖ ^ (-p - 1) := by
    have h2 : (2 : ℝ) ^ (-p - 1) = ((2 : ℝ) ^ (p + 1))⁻¹ := by
      rw [show -p - 1 = -(p + 1) by ring, Real.rpow_neg (by norm_num)]
    rw [Real.div_rpow hz0.le (by norm_num), h2]
    have : (0 : ℝ) < 2 ^ (p + 1) := by positivity
    field_simp
  calc |g (z + y) - g z| ≤ B * ‖xy‖ := hmv
    _ ≤ B * (d * ‖y‖) := mul_le_mul_of_nonneg_left hxyn hB0
    _ = (d * C * 2 ^ (p + 1)) * ‖y‖ * ‖z‖ ^ (-p - 1) := by
        rw [hB, hhalf]; ring


/-! ### The pointwise bound of the integrand -/

theorem rpow_split {w : ℝ} (hw : 0 < w) (e1 e2 : ℝ) : w ^ (e1 + e2) = w ^ e1 * w ^ e2 :=
  Real.rpow_add hw e1 e2

/-- Pointwise bound of the integrand `(g(z+y) - g(z)) (h(x-z) - h(x))` by two shifted copies of
`‖·‖^{-q}`, `q = p + γ - a`: near region `‖z‖ ≤ 2‖y‖`. -/
theorem KB.E_near (K : KB d g G p C)
    {a γ M : ℝ} (ha : 0 ≤ a) (haγ : a ≤ γ)
    (hM0 : 0 ≤ M) {h : Torus d → ℝ} (hM : ∀ x z, |h (x - z) - h x| ≤ M * ‖z‖ ^ a)
    (x y z : Torus d) (hy : y ≠ 0) (hz : z ≠ 0) (hzy : z + y ≠ 0)
    (hA : ‖z‖ ≤ 2 * ‖y‖) :
    |(g (z + y) - g z) * (h (x - z) - h x)| ≤
      (C * M * 3 ^ γ + d * C * 2 ^ (p + 1) * M) * ‖y‖ ^ γ *
        (‖z + y‖ ^ (-(p + γ - a)) + ‖z‖ ^ (-(p + γ - a))) := by
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hwn : 0 < ‖z + y‖ := norm_pos_iff.2 hzy
  have hC := K.C0
  set r : ℝ := ‖y‖ with hrdef
  set q : ℝ := p + γ - a with hq
  have hE : |(g (z + y) - g z) * (h (x - z) - h x)| =
      |g (z + y) - g z| * |h (x - z) - h x| := abs_mul _ _
  have hMz := hM x z
  have hr3 : (0 : ℝ) < 3 * r := by positivity
  have hrg : 0 ≤ r ^ γ := by positivity
  have hq1 : 0 ≤ ‖z + y‖ ^ (-q) := Real.rpow_nonneg hwn.le _
  have hq2 : 0 ≤ ‖z‖ ^ (-q) := Real.rpow_nonneg hzn.le _
  have hΓ1 : 0 ≤ C * M * 3 ^ γ := by positivity
  have hΓ2 : 0 ≤ (d : ℝ) * C * 2 ^ (p + 1) * M := by positivity
  have hzy3 : ‖z + y‖ ≤ 3 * r := by
    have := norm_add_le z y
    linarith
  have h1 : |g (z + y) - g z| * |h (x - z) - h x| ≤
      (|g (z + y)| + |g z|) * (M * ‖z‖ ^ a) :=
    mul_le_mul (abs_sub _ _) hMz (abs_nonneg _) (by positivity)
  have hg1 : |g (z + y)| ≤ C * ‖z + y‖ ^ (-p) := K.gb _ hzy
  have hg2 : |g z| ≤ C * ‖z‖ ^ (-p) := K.gb _ hz
  have hza : ‖z‖ ^ a ≤ (3 * r) ^ a :=
    Real.rpow_le_rpow hzn.le (by linarith) ha
  have hsplit1 : ‖z + y‖ ^ (-p) = ‖z + y‖ ^ (-q) * ‖z + y‖ ^ (γ - a) := by
    rw [← rpow_split hwn]; congr 1; rw [hq]; ring
  have hsplit2 : ‖z‖ ^ (-p + a) = ‖z‖ ^ (-q) * ‖z‖ ^ γ := by
    rw [← rpow_split hzn]; congr 1; rw [hq]; ring
  have hw1 : ‖z + y‖ ^ (γ - a) ≤ (3 * r) ^ (γ - a) :=
    Real.rpow_le_rpow hwn.le hzy3 (by linarith)
  have hz1 : ‖z‖ ^ γ ≤ (3 * r) ^ γ :=
    Real.rpow_le_rpow hzn.le (by linarith) (by linarith)
  have e3 : (3 * r) ^ (γ - a) * (3 * r) ^ a = (3 * r) ^ γ := by
    rw [← rpow_split hr3]; congr 1; ring
  have e4 : (3 * r) ^ γ = 3 ^ γ * r ^ γ := Real.mul_rpow (by norm_num) hr.le
  -- first term
  have t1 : |g (z + y)| * (M * ‖z‖ ^ a) ≤ C * M * 3 ^ γ * r ^ γ * ‖z + y‖ ^ (-q) := by
    calc |g (z + y)| * (M * ‖z‖ ^ a)
        ≤ (C * (‖z + y‖ ^ (-q) * (3 * r) ^ (γ - a))) * (M * (3 * r) ^ a) := by
          rw [hsplit1] at hg1
          refine mul_le_mul ?_ (mul_le_mul_of_nonneg_left hza hM0) (by positivity) (by positivity)
          exact hg1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw1 hq1) hC)
      _ = C * M * ‖z + y‖ ^ (-q) * ((3 * r) ^ (γ - a) * (3 * r) ^ a) := by ring
      _ = C * M * 3 ^ γ * r ^ γ * ‖z + y‖ ^ (-q) := by rw [e3, e4]; ring
  have t2 : |g z| * (M * ‖z‖ ^ a) ≤ C * M * 3 ^ γ * r ^ γ * ‖z‖ ^ (-q) := by
    calc |g z| * (M * ‖z‖ ^ a) ≤ (C * ‖z‖ ^ (-p)) * (M * ‖z‖ ^ a) :=
          mul_le_mul_of_nonneg_right hg2 (by positivity)
      _ = C * M * ‖z‖ ^ (-p + a) := by
          rw [rpow_split hzn]; ring
      _ = C * M * (‖z‖ ^ (-q) * ‖z‖ ^ γ) := by rw [hsplit2]
      _ ≤ C * M * (‖z‖ ^ (-q) * (3 * r) ^ γ) := by gcongr
      _ = C * M * 3 ^ γ * r ^ γ * ‖z‖ ^ (-q) := by rw [e4]; ring
  have hr2 : 0 ≤ (d : ℝ) * C * 2 ^ (p + 1) * M * r ^ γ * ‖z‖ ^ (-q) := by positivity
  calc |(g (z + y) - g z) * (h (x - z) - h x)|
      = |g (z + y) - g z| * |h (x - z) - h x| := hE
    _ ≤ (|g (z + y)| + |g z|) * (M * ‖z‖ ^ a) := h1
    _ = |g (z + y)| * (M * ‖z‖ ^ a) + |g z| * (M * ‖z‖ ^ a) := by ring
    _ ≤ C * M * 3 ^ γ * r ^ γ * ‖z + y‖ ^ (-q) + C * M * 3 ^ γ * r ^ γ * ‖z‖ ^ (-q) := add_le_add t1 t2
    _ ≤ _ := by nlinarith [mul_nonneg hΓ2 (mul_nonneg hrg hq1), mul_nonneg hΓ2 (mul_nonneg hrg hq2)]

/-- Far region `2‖y‖ < ‖z‖`. -/
theorem KB.E_far (K : KB d g G p C)
    {a γ M : ℝ} (_ha : 0 ≤ a) (_haγ : a ≤ γ) (hγ1 : γ ≤ 1)
    (hM0 : 0 ≤ M) {h : Torus d → ℝ} (hM : ∀ x z, |h (x - z) - h x| ≤ M * ‖z‖ ^ a)
    (x y z : Torus d) (hy : y ≠ 0) (hz : z ≠ 0) (hzy : z + y ≠ 0)
    (hB : 2 * ‖y‖ < ‖z‖) :
    |(g (z + y) - g z) * (h (x - z) - h x)| ≤
      (C * M * 3 ^ γ + d * C * 2 ^ (p + 1) * M) * ‖y‖ ^ γ *
        (‖z + y‖ ^ (-(p + γ - a)) + ‖z‖ ^ (-(p + γ - a))) := by
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hwn : 0 < ‖z + y‖ := norm_pos_iff.2 hzy
  have hC := K.C0
  set r : ℝ := ‖y‖ with hrdef
  set q : ℝ := p + γ - a with hq
  have hE : |(g (z + y) - g z) * (h (x - z) - h x)| =
      |g (z + y) - g z| * |h (x - z) - h x| := abs_mul _ _
  have hMz := hM x z
  have hr3 : (0 : ℝ) < 3 * r := by positivity
  have hrg : 0 ≤ r ^ γ := by positivity
  have hq1 : 0 ≤ ‖z + y‖ ^ (-q) := Real.rpow_nonneg hwn.le _
  have hq2 : 0 ≤ ‖z‖ ^ (-q) := Real.rpow_nonneg hzn.le _
  have hΓ1 : 0 ≤ C * M * 3 ^ γ := by positivity
  have hΓ2 : 0 ≤ (d : ℝ) * C * 2 ^ (p + 1) * M := by positivity
  have hdiff := K.diff_bound (y := y) (z := z) hB
  have hz1 : ‖z‖ ^ (γ - 1) ≤ (2 * r) ^ (γ - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hB.le (by linarith)
  have hsplit : ‖z‖ ^ (-(p + 1) + a) = ‖z‖ ^ (-q) * ‖z‖ ^ (γ - 1) := by
    rw [← rpow_split hzn]; congr 1; rw [hq]; ring
  have e6 : r ^ (γ - 1) * r = r ^ γ := by
    have := rpow_split hr (γ - 1) 1
    rw [Real.rpow_one] at this
    rw [← this]; congr 1; ring
  have e5 : (2 * r) ^ (γ - 1) * r = 2 ^ (γ - 1) * r ^ γ := by
    rw [Real.mul_rpow (by norm_num) hr.le, mul_assoc, e6]
  have h2g : (2 : ℝ) ^ (γ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hz2 : 0 ≤ ‖z‖ ^ (-q) * ‖z‖ ^ (γ - 1) := by positivity
  calc |(g (z + y) - g z) * (h (x - z) - h x)|
      = |g (z + y) - g z| * |h (x - z) - h x| := hE
    _ ≤ ((d * C * 2 ^ (p + 1)) * r * ‖z‖ ^ (-p - 1)) * (M * ‖z‖ ^ a) :=
        mul_le_mul hdiff hMz (abs_nonneg _) (by positivity)
    _ = (d * C * 2 ^ (p + 1) * M) * r * (‖z‖ ^ (-(p + 1) + a)) := by
        rw [show -(p + 1) + a = (-p - 1) + a by ring, rpow_split hzn]; ring
    _ = (d * C * 2 ^ (p + 1) * M) * r * (‖z‖ ^ (-q) * ‖z‖ ^ (γ - 1)) := by rw [hsplit]
    _ ≤ (d * C * 2 ^ (p + 1) * M) * r * (‖z‖ ^ (-q) * (2 * r) ^ (γ - 1)) := by gcongr
    _ = (d * C * 2 ^ (p + 1) * M) * (2 ^ (γ - 1) * r ^ γ) * ‖z‖ ^ (-q) := by
        rw [← e5]; ring
    _ ≤ (d * C * 2 ^ (p + 1) * M) * (1 * r ^ γ) * ‖z‖ ^ (-q) := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg hΓ1 (mul_nonneg hrg hq1), mul_nonneg hΓ1 (mul_nonneg hrg hq2),
          mul_nonneg hΓ2 (mul_nonneg hrg hq1), mul_nonneg hΓ2 (mul_nonneg hrg hq2)]

theorem KB.E_bound (K : KB d g G p C)
    {a γ M : ℝ} (ha : 0 ≤ a) (haγ : a ≤ γ) (hγ1 : γ ≤ 1)
    (hM0 : 0 ≤ M) {h : Torus d → ℝ} (hM : ∀ x z, |h (x - z) - h x| ≤ M * ‖z‖ ^ a)
    (x y z : Torus d) (hy : y ≠ 0) (hz : z ≠ 0) (hzy : z + y ≠ 0) :
    |(g (z + y) - g z) * (h (x - z) - h x)| ≤
      (C * M * 3 ^ γ + d * C * 2 ^ (p + 1) * M) * ‖y‖ ^ γ *
        (‖z + y‖ ^ (-(p + γ - a)) + ‖z‖ ^ (-(p + γ - a))) := by
  rcases le_or_gt ‖z‖ (2 * ‖y‖) with hA | hB
  · exact K.E_near ha haγ hM0 hM x y z hy hz hzy hA
  · exact K.E_far ha haγ hγ1 hM0 hM x y z hy hz hzy hB

/-! ### The convolution and its increments -/

theorem convFun_eq' (g h : Torus d → ℝ) (x : Torus d) :
    convFun g h x = ∫ z, g z * h (x - z) := by
  unfold convFun
  rw [← integral_sub_left_eq_self (fun y => g (x - y) * h y) volume x]
  simp

theorem exists_bound_of_cont {h : Torus d → ℝ} (hc : Continuous h) : ∃ B : ℝ, ∀ w, |h w| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hc.continuousOn
  exact ⟨B, fun w => by simpa using hB w (Set.mem_univ w)⟩

theorem integrable_mul_cont {f h : Torus d → ℝ} (hf : Integrable f) (hc : Continuous h) :
    Integrable (fun z => f z * h z) := by
  obtain ⟨B, hB⟩ := exists_bound_of_cont hc
  have := hf.bdd_mul hc.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
    simpa using hB z)
  simpa [mul_comm] using this

theorem conv_diff {g h : Torus d → ℝ} (hg : Integrable g) (hc : Continuous h) (x y : Torus d) :
    convFun g h (x + y) - convFun g h x = ∫ z, (g (z + y) - g z) * (h (x - z) - h x) := by
  have hgy : Integrable (fun z => g (z + y)) := hg.comp_add_right y
  have hcz : Continuous fun z => h (x - z) := hc.comp (continuous_const.sub continuous_id)
  have i1 : Integrable (fun z => g z * h (x - z)) := integrable_mul_cont hg hcz
  have i2 : Integrable (fun z => g (z + y) * h (x - z)) := integrable_mul_cont hgy hcz
  have key : ∀ z, (g (z + y) - g z) * (h (x - z) - h x) =
      (g (z + y) * h (x - z) - g z * h (x - z)) - h x * (g (z + y) - g z) := fun z => by ring
  simp_rw [key]
  have j1 : Integrable (fun z => g (z + y) * h (x - z) - g z * h (x - z)) := i2.sub i1
  have j2 : Integrable (fun z => h x * (g (z + y) - g z)) := (hgy.sub hg).const_mul _
  have j3 : Integrable (fun z => g (z + y) - g z) := hgy.sub hg
  rw [integral_sub j1 j2, integral_sub i2 i1, integral_const_mul,
    integral_sub hgy hg, integral_add_right_eq_self g y, convFun_eq', convFun_eq']
  have : ∫ z, g z * h (x + y - z) = ∫ z, g (z + y) * h (x - z) := by
    rw [← integral_add_right_eq_self (fun z => g z * h (x + y - z)) y]
    simp
  rw [this]
  simp

/-- **Hölder gain for the convolution** (increment form). -/
theorem KB.conv_holder_bound (K : KB d g G p C) {a γ M : ℝ} (ha : 0 ≤ a) (haγ : a ≤ γ)
    (hγ1 : γ ≤ 1) (hγθ : γ < a + (d - p)) (hM0 : 0 ≤ M) {h : Torus d → ℝ} (hc : Continuous h)
    (hM : ∀ x z, |h (x - z) - h x| ≤ M * ‖z‖ ^ a) (x y : Torus d) :
    |convFun g h (x + y) - convFun g h x| ≤
      (2 * (C * M * 3 ^ γ + d * C * 2 ^ (p + 1) * M) * ∫ z : Torus d, ‖z‖ ^ (-(p + γ - a))) *
        ‖y‖ ^ γ := by
  set q : ℝ := p + γ - a with hq
  have hqd : q < d := by rw [hq]; linarith
  have hI : Integrable (fun z : Torus d => ‖z‖ ^ (-q)) :=
    KernelGrad.integrable_norm_rpow_neg K.hd hqd
  have hI0 : 0 ≤ ∫ z : Torus d, ‖z‖ ^ (-q) :=
    integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  set Γ : ℝ := C * M * 3 ^ γ + d * C * 2 ^ (p + 1) * M with hΓ
  have hΓ0 : 0 ≤ Γ := by have := K.C0; positivity
  by_cases hy : y = 0
  · subst hy
    rw [add_zero, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hΓ0) hI0)
      (Real.rpow_nonneg (norm_nonneg _) _)
  have hr0 : 0 ≤ ‖y‖ ^ γ := Real.rpow_nonneg (norm_nonneg _) _
  rw [conv_diff K.gint hc, ← Real.norm_eq_abs]
  have hshift : Integrable (fun z : Torus d => ‖z + y‖ ^ (-q)) := hI.comp_add_right y
  have hB : Integrable (fun z : Torus d => Γ * ‖y‖ ^ γ * (‖z + y‖ ^ (-q) + ‖z‖ ^ (-q))) :=
    (hshift.add hI).const_mul _
  refine (norm_integral_le_of_norm_le hB ?_).trans ?_
  · filter_upwards [KernelGrad.torus_ae_ne' K.hd, ae_add_ne_zero K.hd y] with z hz hzy
    rw [Real.norm_eq_abs]
    exact K.E_bound ha haγ hγ1 hM0 hM x y z hy hz hzy
  · rw [integral_const_mul, integral_add hshift hI, integral_add_right_eq_self
      (fun z : Torus d => ‖z‖ ^ (-q)) y]
    apply le_of_eq
    ring


/-! ### Differentiation of the convolution with a `C¹` function -/

theorem measurable_rep' (d : ℕ) : Measurable (Torus.rep : Torus d → Euc d) := by
  have h : Measurable (fun (x : Torus d) (i : Fin d) =>
      ((AddCircle.equivIco (1 : ℝ) 0 (x i) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)) :=
    measurable_pi_iff.2 fun i => measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (measurable_pi_apply i))
  exact (WithLp.measurable_toLp 2 _).comp h

theorem convFun_hasFDerivAt {g h : Torus d → ℝ} (hg : Integrable g) (hh : Torus.IsCk 1 h)
    (v : Euc d) :
    HasFDerivAt (Torus.lift (convFun g h))
      (∫ z, g z • fderiv ℝ (Torus.lift h) (v - Torus.rep z)) v := by
  obtain ⟨L, hL0, hL⟩ := KernelGrad.norm_fderiv_le_of_isCk hh
  have hH : ContDiff ℝ 1 (Torus.lift h) := hh
  have hHd : Differentiable ℝ (Torus.lift h) := hH.differentiable one_ne_zero
  have hHc : Continuous (Torus.lift h) := hH.continuous
  have hHc' : Continuous (fderiv ℝ (Torus.lift h)) := hH.continuous_fderiv one_ne_zero
  obtain ⟨B, hB⟩ := exists_bound_of_cont (continuous_of_isCk hh)
  have e : Torus.lift (convFun g h) = fun w => ∫ z, g z * Torus.lift h (w - Torus.rep z) := by
    funext w
    simp only [Torus.lift, Function.comp]
    rw [convFun_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [KernelGrad.mk_sub, Torus.mk_rep]
  rw [e]
  have hrep := measurable_rep' d
  have hmeas : ∀ w, AEStronglyMeasurable (fun z : Torus d => g z * Torus.lift h (w - Torus.rep z)) := by
    intro w
    exact hg.aestronglyMeasurable.mul
      (hHc.measurable.comp (measurable_const.sub hrep)).aestronglyMeasurable
  have hint : Integrable (fun z : Torus d => g z * Torus.lift h (v - Torus.rep z)) := by
    refine hg.mul_bdd (c := B) (hHc.measurable.comp (measurable_const.sub hrep)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have := hB (Torus.mk (v - Torus.rep z))
    simpa [Torus.lift] using this
  have hmeas' : AEStronglyMeasurable (fun z : Torus d => g z • fderiv ℝ (Torus.lift h) (v - Torus.rep z)) := by
    exact hg.aestronglyMeasurable.smul
      (hHc'.measurable.comp (measurable_const.sub hrep)).aestronglyMeasurable
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun w z => g z * Torus.lift h (w - Torus.rep z))
    (F' := fun w z => g z • fderiv ℝ (Torus.lift h) (w - Torus.rep z)) (bound := fun z => ‖g z‖ * L)
    (s := Set.univ) Filter.univ_mem (Filter.Eventually.of_forall hmeas) hint hmeas'
    (Filter.Eventually.of_forall fun z w _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hL _) (norm_nonneg _))
    (hg.norm.mul_const L)
    (Filter.Eventually.of_forall fun z w _ => by
      have h1 := (hHd (w - Torus.rep z)).hasFDerivAt.comp w ((hasFDerivAt_id w).sub_const (Torus.rep z))
      have h2 := h1.const_mul (g z)
      simpa using h2)


theorem convFun_fderiv_integrable {g h : Torus d → ℝ} (hg : Integrable g) (hh : Torus.IsCk 1 h)
    (v : Euc d) :
    Integrable (fun z => g z • fderiv ℝ (Torus.lift h) (v - Torus.rep z)) := by
  obtain ⟨L, hL0, hL⟩ := KernelGrad.norm_fderiv_le_of_isCk hh
  have hH : ContDiff ℝ 1 (Torus.lift h) := hh
  have hHc' : Continuous (fderiv ℝ (Torus.lift h)) := hH.continuous_fderiv one_ne_zero
  have hrep := measurable_rep' d
  refine Integrable.mono' (hg.norm.mul_const L) (hg.aestronglyMeasurable.smul
      (hHc'.measurable.comp (measurable_const.sub hrep)).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun z => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hL _) (norm_nonneg _)

theorem convFun_isCk_one {g h : Torus d → ℝ} (hg : Integrable g) (hh : Torus.IsCk 1 h) :
    Torus.IsCk 1 (convFun g h) := by
  obtain ⟨L, hL0, hL⟩ := KernelGrad.norm_fderiv_le_of_isCk hh
  have hH : ContDiff ℝ 1 (Torus.lift h) := hh
  have hHc' : Continuous (fderiv ℝ (Torus.lift h)) := hH.continuous_fderiv one_ne_zero
  have hrep := measurable_rep' d
  unfold Torus.IsCk
  rw [contDiff_one_iff_fderiv]
  have hd : ∀ v, HasFDerivAt (Torus.lift (convFun g h))
      (∫ z, g z • fderiv ℝ (Torus.lift h) (v - Torus.rep z)) v := fun v => convFun_hasFDerivAt hg hh v
  refine ⟨fun v => (hd v).differentiableAt, ?_⟩
  have : fderiv ℝ (Torus.lift (convFun g h)) =
      fun v => ∫ z, g z • fderiv ℝ (Torus.lift h) (v - Torus.rep z) := funext fun v => (hd v).fderiv
  rw [this]
  refine continuous_of_dominated (bound := fun z => ‖g z‖ * L) (fun v => ?_) (fun v => ?_)
    (hg.norm.mul_const L) (Filter.Eventually.of_forall fun z => ?_)
  · exact (convFun_fderiv_integrable hg hh v).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hL _) (norm_nonneg _)
  · have h1 := hHc'.comp (continuous_id.sub (continuous_const (y := Torus.rep z)))
    exact (continuous_const (y := g z)).smul h1

theorem convFun_partialDeriv {g h : Torus d → ℝ} (hg : Integrable g) (hh : Torus.IsCk 1 h)
    (j : Fin d) (x : Torus d) :
    Torus.partialDeriv j (convFun g h) x = convFun g (Torus.partialDeriv j h) x := by
  have hd := convFun_hasFDerivAt hg hh (Torus.rep x)
  have e0 : Torus.partialDeriv j (convFun g h) x =
      fderiv ℝ (Torus.lift (convFun g h)) (Torus.rep x) (EuclideanSpace.single j 1) := rfl
  rw [e0, hd.fderiv, ContinuousLinearMap.integral_apply (convFun_fderiv_integrable hg hh _),
    convFun_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [smul_apply, smul_eq_mul]
  congr 1
  rw [← partialDeriv_mk j h hh, KernelGrad.mk_sub, Torus.mk_rep, Torus.mk_rep]


/-! ### The Hölder classes under convolution -/

theorem Hol0.increment {a : ℝ} {h : Torus d → ℝ} (H : MFHolder.Hol0 a h) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x z, |h (x - z) - h x| ≤ M * ‖z‖ ^ a := by
  obtain ⟨_, M, hM⟩ := H
  refine ⟨|M|, abs_nonneg M, fun x z => ?_⟩
  have h1 := hM (x - z) x
  rw [sub_sub_cancel_left, norm_neg] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity))

theorem KB.conv_hol0 (K : KB d g G p C) {a γ : ℝ} (ha : 0 ≤ a) (haγ : a ≤ γ) (hγ1 : γ ≤ 1)
    (hγθ : γ < a + (d - p)) {h : Torus d → ℝ} (H : MFHolder.Hol0 a h) :
    MFHolder.Hol0 γ (convFun g h) := by
  obtain ⟨M, hM0, hM⟩ := Hol0.increment H
  refine ⟨MFAux.continuous_convFun K.gint H.1,
    2 * (C * M * 3 ^ γ + d * C * 2 ^ (p + 1) * M) * ∫ z : Torus d, ‖z‖ ^ (-(p + γ - a)), fun x y => ?_⟩
  have := K.conv_holder_bound ha haγ hγ1 hγθ hM0 H.1 hM y (x - y)
  rw [add_sub_cancel] at this
  exact this

theorem KB.conv_HC (K : KB d g G p C) : ∀ (m : ℕ) {a γ : ℝ} {h : Torus d → ℝ}, 0 ≤ a → a ≤ γ →
    γ ≤ 1 → γ < a + (d - p) → MFHolder.HC m a h → MFHolder.HC m γ (convFun g h)
  | 0, _, _, _, ha, haγ, hγ1, hγθ, H => K.conv_hol0 ha haγ hγ1 hγθ H
  | m + 1, a, γ, h, ha, haγ, hγ1, hγθ, H => by
    refine ⟨convFun_isCk_one K.gint H.1, fun j => ?_⟩
    have e : Torus.partialDeriv j (convFun g h) = convFun g (Torus.partialDeriv j h) :=
      funext fun x => convFun_partialDeriv K.gint H.1 j x
    rw [e]
    exact K.conv_HC m ha haγ hγ1 hγθ (H.2 j)


/-! ### The gradient of the convolution with a Hölder function -/

/-- The candidate gradient `W h x = ∫ (h(x-z) - h(x)) ∇g(z) dz` (absolutely convergent when
`h` is `a`-Hölder and `a + (d - p) > 1`). -/
def Wgrad (G : Torus d → Euc d) (h : Torus d → ℝ) (x : Torus d) : Euc d :=
  ∫ z, (h (x - z) - h x) • G z

theorem KB.W_bound (K : KB d g G p C) {a M : ℝ} {h : Torus d → ℝ}
    (hM : ∀ x z, |h (x - z) - h x| ≤ M * ‖z‖ ^ a) (hM0 : 0 ≤ M) (x z : Torus d) (hz : z ≠ 0) :
    ‖(h (x - z) - h x) • G z‖ ≤ C * M * ‖z‖ ^ (-(p + 1 - a)) := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [norm_smul, Real.norm_eq_abs]
  have h1 := hM x z
  have h2 := K.Gb z hz
  have e : ‖z‖ ^ (-(p + 1 - a)) = ‖z‖ ^ (-p - 1) * ‖z‖ ^ a := by
    rw [← rpow_split hzn]; congr 1; ring
  rw [e]
  calc |h (x - z) - h x| * ‖G z‖ ≤ (M * ‖z‖ ^ a) * (C * ‖z‖ ^ (-p - 1)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by have := K.C0; positivity)
    _ = C * M * (‖z‖ ^ (-p - 1) * ‖z‖ ^ a) := by ring

theorem KB.W_integrable (K : KB d g G p C) {a M : ℝ} (hθ : 1 < a + (d - p))
    {h : Torus d → ℝ} (hc : Continuous h) (hM : ∀ x z, |h (x - z) - h x| ≤ M * ‖z‖ ^ a)
    (hM0 : 0 ≤ M) (x : Torus d) : Integrable (fun z => (h (x - z) - h x) • G z) := by
  have hqd : p + 1 - a < d := by linarith
  have hI : Integrable (fun z : Torus d => ‖z‖ ^ (-(p + 1 - a))) :=
    KernelGrad.integrable_norm_rpow_neg K.hd hqd
  refine Integrable.mono' (hI.const_mul (C * M)) ?_ ?_
  · exact (((hc.comp (continuous_const.sub continuous_id)).sub continuous_const).aestronglyMeasurable).smul
      K.Gmeas.aestronglyMeasurable
  · filter_upwards [KernelGrad.torus_ae_ne' K.hd] with z hz
    exact K.W_bound hM hM0 x z hz

/-- Hölder continuity of the candidate gradient. -/
theorem KB.W_holder (K : KB d g G p C) {a M γ' : ℝ} (ha : 0 ≤ a) (hθ : 1 < a + (d - p))
    (hγ'0 : 0 ≤ γ') (hγ'a : γ' ≤ a) (hγ'θ : γ' < a + (d - p) - 1)
    {h : Torus d → ℝ} (hc : Continuous h) (hM : ∀ x z, |h (x - z) - h x| ≤ M * ‖z‖ ^ a)
    (hM0 : 0 ≤ M) (x y : Torus d) :
    ‖Wgrad G h (x + y) - Wgrad G h x‖ ≤
      (2 * C * M * ∫ z : Torus d, ‖z‖ ^ (-(p + 1 - a + γ'))) * ‖y‖ ^ γ' := by
  set q : ℝ := p + 1 - a + γ' with hq
  have hqd : q < d := by rw [hq]; linarith
  have hI : Integrable (fun z : Torus d => ‖z‖ ^ (-q)) :=
    KernelGrad.integrable_norm_rpow_neg K.hd hqd
  have hI0 : 0 ≤ ∫ z : Torus d, ‖z‖ ^ (-q) :=
    integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  have hC := K.C0
  by_cases hy : y = 0
  · subst hy
    rw [add_zero, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) hI0) (Real.rpow_nonneg (norm_nonneg _) _)
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  set r : ℝ := ‖y‖ with hrdef
  have hr0 : 0 ≤ r ^ γ' := Real.rpow_nonneg hr.le _
  have hW1 := K.W_integrable hθ hc hM hM0 (x + y)
  have hW2 := K.W_integrable hθ hc hM hM0 x
  unfold Wgrad
  rw [← integral_sub hW1 hW2]
  have hB : Integrable (fun z : Torus d => (2 * C * M * r ^ γ') * ‖z‖ ^ (-q)) := hI.const_mul _
  refine (norm_integral_le_of_norm_le hB ?_).trans ?_
  · filter_upwards [KernelGrad.torus_ae_ne' K.hd] with z hz
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [← sub_smul]
    rw [norm_smul, Real.norm_eq_abs]
    have hD1 : |(h (x + y - z) - h (x + y)) - (h (x - z) - h x)| ≤ 2 * M * ‖z‖ ^ a := by
      calc _ ≤ |h (x + y - z) - h (x + y)| + |h (x - z) - h x| := abs_sub _ _
        _ ≤ M * ‖z‖ ^ a + M * ‖z‖ ^ a := add_le_add (hM _ _) (hM _ _)
        _ = 2 * M * ‖z‖ ^ a := by ring
    have hD2 : |(h (x + y - z) - h (x + y)) - (h (x - z) - h x)| ≤ 2 * M * r ^ a := by
      have e : (h (x + y - z) - h (x + y)) - (h (x - z) - h x) =
          (h (x - z + y) - h (x - z)) - (h (x + y) - h x) := by
        rw [sub_add_eq_add_sub]; ring
      rw [e]
      have h1 := hM (x - z + y) y
      have h2 := hM (x + y) y
      rw [add_sub_cancel_right] at h1 h2
      calc _ ≤ |h (x - z + y) - h (x - z)| + |h (x + y) - h x| := abs_sub _ _
        _ = |h (x - z) - h (x - z + y)| + |h x - h (x + y)| := by
            rw [abs_sub_comm (h (x - z + y)), abs_sub_comm (h (x + y))]
        _ ≤ M * r ^ a + M * r ^ a := add_le_add h1 h2
        _ = 2 * M * r ^ a := by ring
    have hG := K.Gb z hz
    have hsplit1 : ‖z‖ ^ (-p - 1 + a) = ‖z‖ ^ (-q) * ‖z‖ ^ γ' := by
      rw [← rpow_split hzn]; congr 1; rw [hq]; ring
    have hsplit2 : ‖z‖ ^ (-p - 1) = ‖z‖ ^ (-q) * ‖z‖ ^ (γ' - a) := by
      rw [← rpow_split hzn]; congr 1; rw [hq]; ring
    rcases le_or_gt ‖z‖ r with hz1 | hz1
    · calc _ ≤ (2 * M * ‖z‖ ^ a) * (C * ‖z‖ ^ (-p - 1)) :=
            mul_le_mul hD1 hG (norm_nonneg _) (by positivity)
        _ = 2 * C * M * ‖z‖ ^ (-p - 1 + a) := by
            rw [rpow_split hzn]; ring
        _ = 2 * C * M * (‖z‖ ^ (-q) * ‖z‖ ^ γ') := by rw [hsplit1]
        _ ≤ 2 * C * M * (‖z‖ ^ (-q) * r ^ γ') := by
            gcongr
        _ = _ := by ring
    · have hz2 : ‖z‖ ^ (γ' - a) ≤ r ^ (γ' - a) :=
        Real.rpow_le_rpow_of_nonpos hr hz1.le (by linarith)
      have e : r ^ a * r ^ (γ' - a) = r ^ γ' := by
        rw [← rpow_split hr]; congr 1; ring
      calc _ ≤ (2 * M * r ^ a) * (C * ‖z‖ ^ (-p - 1)) :=
            mul_le_mul hD2 hG (norm_nonneg _) (by positivity)
        _ = 2 * C * M * r ^ a * (‖z‖ ^ (-q) * ‖z‖ ^ (γ' - a)) := by rw [hsplit2]; ring
        _ ≤ 2 * C * M * r ^ a * (‖z‖ ^ (-q) * r ^ (γ' - a)) := by gcongr
        _ = 2 * C * M * (r ^ a * r ^ (γ' - a)) * ‖z‖ ^ (-q) := by ring
        _ = _ := by rw [e]
  · rw [integral_const_mul]
    apply le_of_eq
    ring


/-! ### Differentiability of the convolution with a Hölder function -/

theorem norm_mk_le_norm (w : Euc d) : ‖Torus.mk w‖ ≤ ‖w‖ :=
  norm_mk_le (norm_nonneg _) fun i => by
    have := PiLp.norm_apply_le w i
    simpa using this

theorem mk_ne_zero_of_small {w : Euc d} (hw0 : w ≠ 0) (hw : ‖w‖ < 1 / 2) : Torus.mk w ≠ 0 := by
  intro h
  apply hw0
  ext i
  have hi : ((w i : ℝ) : UnitAddCircle) = 0 := congrFun h i
  rw [AddCircle.coe_eq_zero_iff] at hi
  obtain ⟨n, hn⟩ := hi
  have h1 : |w i| < 1 / 2 := lt_of_le_of_lt (by simpa using PiLp.norm_apply_le w i) hw
  have h2 : (n : ℝ) = w i := by simpa using hn
  have h3 : |(n : ℝ)| < 1 / 2 := by rw [h2]; exact h1
  have h4 : n = 0 := by
    rw [abs_lt] at h3
    have h5 : n < 1 := by exact_mod_cast (by linarith [h3.2] : (n : ℝ) < 1)
    have h6 : -1 < n := by exact_mod_cast (by linarith [h3.1] : (-1 : ℝ) < n)
    omega
  simp [← h2, h4]

theorem E_integrable (hg : Integrable g) {h : Torus d → ℝ} (hc : Continuous h) (x y : Torus d) :
    Integrable (fun z => (g (z + y) - g z) * (h (x - z) - h x)) :=
  integrable_mul_cont ((hg.comp_add_right y).sub hg)
    ((hc.comp (continuous_const.sub continuous_id)).sub continuous_const)

theorem KB.R_identity (K : KB d g G p C) {a M : ℝ} (hθ : 1 < a + (d - p))
    {h : Torus d → ℝ} (hc : Continuous h) (hM : ∀ x z, |h (x - z) - h x| ≤ M * ‖z‖ ^ a)
    (hM0 : 0 ≤ M) (x : Torus d) (w : Euc d) :
    convFun g h (x + Torus.mk w) - convFun g h x - inner ℝ (Wgrad G h x) w =
      ∫ z, (g (z + Torus.mk w) - g z - inner ℝ (G z) w) * (h (x - z) - h x) := by
  have hW := K.W_integrable hθ hc hM hM0 x
  have hE := E_integrable K.gint hc x (Torus.mk w)
  have hGw : Integrable (fun z => (h (x - z) - h x) * inner ℝ (G z) w) := by
    have := (innerSL ℝ w).integrable_comp hW
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.comp, innerSL_apply_apply, real_inner_smul_right, real_inner_comm]
  have h1 : inner ℝ (Wgrad G h x) w = ∫ z, (h (x - z) - h x) * inner ℝ (G z) w := by
    unfold Wgrad
    rw [real_inner_comm, ← integral_inner hW]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [real_inner_smul_right, real_inner_comm]
  rw [h1, conv_diff K.gint hc, ← integral_sub hE hGw]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  ring


/-- The integrand of the remainder splits into a near part, dominated by an explicit integrable
function, and the far part `Θ`. -/
theorem KB.psi_bound (K : KB d g G p C) {a γ γ₃ M : ℝ} (ha : 0 ≤ a) (haγ : a ≤ γ) (hγ₃ : 0 ≤ γ₃)
    (hM0 : 0 ≤ M) {h : Torus d → ℝ} (hM : ∀ x z, |h (x - z) - h x| ≤ M * ‖z‖ ^ a)
    (x : Torus d) (w : Euc d) (hy : Torus.mk w ≠ 0) (z : Torus d) (hz : z ≠ 0)
    (hzy : z + Torus.mk w ≠ 0) :
    |(g (z + Torus.mk w) - g z - inner ℝ (G z) w) * (h (x - z) - h x)| ≤
      ((C * M * 3 ^ γ + d * C * 2 ^ (p + 1) * M) * ‖Torus.mk w‖ ^ γ *
          (‖z + Torus.mk w‖ ^ (-(p + γ - a)) + ‖z‖ ^ (-(p + γ - a))) +
        C * M * ‖w‖ * (2 * ‖Torus.mk w‖) ^ γ₃ * ‖z‖ ^ (-(p + 1 - a + γ₃))) +
      Set.indicator {z : Torus d | 2 * ‖Torus.mk w‖ < ‖z‖}
        (fun z => |(g (z + Torus.mk w) - g z - inner ℝ (G z) w) * (h (x - z) - h x)|) z := by
  set y : Torus d := Torus.mk w with hydef
  set r : ℝ := ‖y‖ with hrdef
  have hr : 0 < r := norm_pos_iff.2 hy
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hC := K.C0
  set q₃ : ℝ := p + 1 - a + γ₃ with hq₃
  set q : ℝ := p + γ - a with hq
  have hΞ : 0 ≤ (C * M * 3 ^ γ + d * C * 2 ^ (p + 1) * M) * r ^ γ *
          (‖z + y‖ ^ (-q) + ‖z‖ ^ (-q)) +
        C * M * ‖w‖ * (2 * r) ^ γ₃ * ‖z‖ ^ (-q₃) := by positivity
  rcases le_or_gt ‖z‖ (2 * r) with hA | hB
  · have hind : Set.indicator {z : Torus d | 2 * r < ‖z‖}
        (fun z => |(g (z + y) - g z - inner ℝ (G z) w) * (h (x - z) - h x)|) z = 0 :=
      Set.indicator_of_notMem (by simpa using hA) _
    rw [hind, add_zero]
    have hE := K.E_near ha haγ hM0 hM x y z hy hz hzy hA
    have hexp : (g (z + y) - g z - inner ℝ (G z) w) * (h (x - z) - h x) =
        (g (z + y) - g z) * (h (x - z) - h x) - inner ℝ (G z) w * (h (x - z) - h x) := by ring
    rw [hexp]
    refine (abs_sub _ _).trans ?_
    have h1 : |inner ℝ (G z) w * (h (x - z) - h x)| ≤
        C * M * ‖w‖ * (2 * r) ^ γ₃ * ‖z‖ ^ (-q₃) := by
      rw [abs_mul]
      have h2 : |inner ℝ (G z) w| ≤ C * ‖z‖ ^ (-p - 1) * ‖w‖ :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (K.Gb z hz) (norm_nonneg _))
      have h3 := hM x z
      have hs : ‖z‖ ^ (-p - 1 + a) = ‖z‖ ^ (-q₃) * ‖z‖ ^ γ₃ := by
        rw [← rpow_split hzn]; congr 1; rw [hq₃]; ring
      have h4 : ‖z‖ ^ γ₃ ≤ (2 * r) ^ γ₃ := Real.rpow_le_rpow hzn.le hA hγ₃
      calc |inner ℝ (G z) w| * |h (x - z) - h x|
          ≤ (C * ‖z‖ ^ (-p - 1) * ‖w‖) * (M * ‖z‖ ^ a) :=
            mul_le_mul h2 h3 (abs_nonneg _) (by positivity)
        _ = C * M * ‖w‖ * ‖z‖ ^ (-p - 1 + a) := by rw [rpow_split hzn]; ring
        _ = C * M * ‖w‖ * (‖z‖ ^ (-q₃) * ‖z‖ ^ γ₃) := by rw [hs]
        _ ≤ C * M * ‖w‖ * (‖z‖ ^ (-q₃) * (2 * r) ^ γ₃) := by gcongr
        _ = _ := by ring
    linarith
  · have hind : Set.indicator {z : Torus d | 2 * r < ‖z‖}
        (fun z => |(g (z + y) - g z - inner ℝ (G z) w) * (h (x - z) - h x)|) z =
        |(g (z + y) - g z - inner ℝ (G z) w) * (h (x - z) - h x)| :=
      Set.indicator_of_mem (by simpa using hB) _
    rw [hind]
    linarith


/-- The (normalised) far part of the remainder. -/
def Psi (g : Torus d → ℝ) (G : Torus d → Euc d) (h : Torus d → ℝ) (x : Torus d) (w : Euc d) : ℝ :=
  ∫ z, ‖w‖⁻¹ * Set.indicator {z : Torus d | 2 * ‖Torus.mk w‖ < ‖z‖}
        (fun z => |(g (z + Torus.mk w) - g z - inner ℝ (G z) w) * (h (x - z) - h x)|) z

theorem KB.remainder_bound (K : KB d g G p C) {a γ γ₃ M : ℝ} (ha : 0 ≤ a) (haγ : a ≤ γ)
    (hγ₁ : 1 ≤ γ) (hγθ : γ < a + (d - p)) (hγ₃ : 0 ≤ γ₃) (hγ₃θ : γ₃ < a + (d - p) - 1)
    (hθ : 1 < a + (d - p)) (hM0 : 0 ≤ M) {h : Torus d → ℝ} (hc : Continuous h)
    (hM : ∀ x z, |h (x - z) - h x| ≤ M * ‖z‖ ^ a) (x : Torus d) {w : Euc d} (hw0 : w ≠ 0)
    (hw : ‖w‖ < 1 / 2) :
    |convFun g h (x + Torus.mk w) - convFun g h x - inner ℝ (Wgrad G h x) w| ≤
      ‖w‖ * ((2 * (C * M * 3 ^ γ + d * C * 2 ^ (p + 1) * M) *
            (∫ z : Torus d, ‖z‖ ^ (-(p + γ - a))) * ‖w‖ ^ (γ - 1) +
          C * M * (∫ z : Torus d, ‖z‖ ^ (-(p + 1 - a + γ₃))) * (2 * ‖w‖) ^ γ₃) +
        Psi g G h x w) := by
  set y : Torus d := Torus.mk w with hydef
  have hy : y ≠ 0 := mk_ne_zero_of_small hw0 hw
  set r : ℝ := ‖y‖ with hrdef
  have hr : 0 < r := norm_pos_iff.2 hy
  have hrw : r ≤ ‖w‖ := norm_mk_le_norm w
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  set q : ℝ := p + γ - a with hq
  set q₃ : ℝ := p + 1 - a + γ₃ with hq₃
  have hqd : q < d := by rw [hq]; linarith
  have hq₃d : q₃ < d := by rw [hq₃]; linarith
  have hI : Integrable (fun z : Torus d => ‖z‖ ^ (-q)) := KernelGrad.integrable_norm_rpow_neg K.hd hqd
  have hI₃ : Integrable (fun z : Torus d => ‖z‖ ^ (-q₃)) := KernelGrad.integrable_norm_rpow_neg K.hd hq₃d
  have hI0 : 0 ≤ ∫ z : Torus d, ‖z‖ ^ (-q) :=
    integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  have hI₃0 : 0 ≤ ∫ z : Torus d, ‖z‖ ^ (-q₃) :=
    integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  have hC := K.C0
  set Γ : ℝ := C * M * 3 ^ γ + d * C * 2 ^ (p + 1) * M with hΓ
  have hΓ0 : 0 ≤ Γ := by positivity
  rw [K.R_identity hθ hc hM hM0 x w]
  -- integrability of the pieces
  have hW := K.W_integrable hθ hc hM hM0 x
  have hψ : Integrable (fun z => (g (z + y) - g z - inner ℝ (G z) w) * (h (x - z) - h x)) := by
    have hE := E_integrable K.gint hc x y
    have hGw : Integrable (fun z => (h (x - z) - h x) * inner ℝ (G z) w) := by
      have := (innerSL ℝ w).integrable_comp hW
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      simp only [innerSL_apply_apply, real_inner_smul_right, real_inner_comm]
    refine (hE.sub hGw).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply]
    ring
  have hΘ : Integrable (Set.indicator {z : Torus d | 2 * r < ‖z‖}
      (fun z => |(g (z + y) - g z - inner ℝ (G z) w) * (h (x - z) - h x)|)) :=
    hψ.abs.indicator (measurableSet_lt measurable_const measurable_norm)
  have hΞ : Integrable (fun z : Torus d => Γ * r ^ γ * (‖z + y‖ ^ (-q) + ‖z‖ ^ (-q)) +
      C * M * ‖w‖ * (2 * r) ^ γ₃ * ‖z‖ ^ (-q₃)) :=
    (((hI.comp_add_right y).add hI).const_mul _).add (hI₃.const_mul _)
  have hbound : ‖∫ z, (g (z + y) - g z - inner ℝ (G z) w) * (h (x - z) - h x)‖ ≤
      ∫ z, ((Γ * r ^ γ * (‖z + y‖ ^ (-q) + ‖z‖ ^ (-q)) +
          C * M * ‖w‖ * (2 * r) ^ γ₃ * ‖z‖ ^ (-q₃)) +
        Set.indicator {z : Torus d | 2 * r < ‖z‖}
          (fun z => |(g (z + y) - g z - inner ℝ (G z) w) * (h (x - z) - h x)|) z) := by
    refine norm_integral_le_of_norm_le (hΞ.add hΘ) ?_
    filter_upwards [KernelGrad.torus_ae_ne' K.hd, ae_add_ne_zero K.hd y] with z hz hzy
    rw [Real.norm_eq_abs]
    exact K.psi_bound ha haγ hγ₃ hM0 hM x w hy z hz hzy
  rw [Real.norm_eq_abs] at hbound
  refine hbound.trans ?_
  have iS : Integrable (fun z : Torus d => ‖z + y‖ ^ (-q) + ‖z‖ ^ (-q)) :=
    (hI.comp_add_right y).add hI
  have iA : Integrable (fun z : Torus d => Γ * r ^ γ * (‖z + y‖ ^ (-q) + ‖z‖ ^ (-q))) :=
    iS.const_mul _
  have iB : Integrable (fun z : Torus d => C * M * ‖w‖ * (2 * r) ^ γ₃ * ‖z‖ ^ (-q₃)) :=
    hI₃.const_mul _
  have iC : Integrable (fun z : Torus d => ‖z + y‖ ^ (-q)) := hI.comp_add_right y
  rw [integral_add hΞ hΘ, integral_add iA iB, integral_const_mul, integral_const_mul,
    integral_add iC hI, integral_add_right_eq_self (fun z : Torus d => ‖z‖ ^ (-q)) y]
  have hΨ : ∫ z, Set.indicator {z : Torus d | 2 * r < ‖z‖}
      (fun z => |(g (z + y) - g z - inner ℝ (G z) w) * (h (x - z) - h x)|) z = ‖w‖ * Psi g G h x w := by
    unfold Psi
    rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hwn.ne', one_mul]
  rw [hΨ]
  have e1 : r ^ γ ≤ ‖w‖ ^ γ := Real.rpow_le_rpow hr.le hrw (by linarith)
  have e2 : (2 * r) ^ γ₃ ≤ (2 * ‖w‖) ^ γ₃ := Real.rpow_le_rpow (by positivity) (by linarith) hγ₃
  have e3 : ‖w‖ ^ γ = ‖w‖ ^ (γ - 1) * ‖w‖ := by
    have := rpow_split hwn (γ - 1) 1
    rw [Real.rpow_one] at this
    rw [← this]; congr 1; ring
  have t1 : Γ * r ^ γ * ((∫ z : Torus d, ‖z‖ ^ (-q)) + (∫ z : Torus d, ‖z‖ ^ (-q))) ≤
      ‖w‖ * (2 * Γ * (∫ z : Torus d, ‖z‖ ^ (-q)) * ‖w‖ ^ (γ - 1)) := by
    calc Γ * r ^ γ * ((∫ z : Torus d, ‖z‖ ^ (-q)) + (∫ z : Torus d, ‖z‖ ^ (-q)))
        ≤ Γ * ‖w‖ ^ γ * ((∫ z : Torus d, ‖z‖ ^ (-q)) + (∫ z : Torus d, ‖z‖ ^ (-q))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e1 hΓ0) (add_nonneg hI0 hI0)
      _ = ‖w‖ * (2 * Γ * (∫ z : Torus d, ‖z‖ ^ (-q)) * ‖w‖ ^ (γ - 1)) := by rw [e3]; ring
  have t2 : C * M * ‖w‖ * (2 * r) ^ γ₃ * (∫ z : Torus d, ‖z‖ ^ (-q₃)) ≤
      ‖w‖ * (C * M * (∫ z : Torus d, ‖z‖ ^ (-q₃)) * (2 * ‖w‖) ^ γ₃) := by
    calc C * M * ‖w‖ * (2 * r) ^ γ₃ * (∫ z : Torus d, ‖z‖ ^ (-q₃))
        ≤ C * M * ‖w‖ * (2 * ‖w‖) ^ γ₃ * (∫ z : Torus d, ‖z‖ ^ (-q₃)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e2 (by positivity)) hI₃0
      _ = _ := by ring
  nlinarith [t1, t2]

end HRS.PDE.MFSchauder
