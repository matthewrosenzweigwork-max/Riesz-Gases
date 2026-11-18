import HRS.MC.CepH2Aux5

/-!
# CEPH2, helper 6: derivatives of the Gaussian and of its periodisation

`h2_per v` is the diagonally periodised Gaussian; it is `C²`, positive, periodic, and its first two derivatives are
the termwise sums.  Global bounds follow from periodicity and the Gaussian decay in the mean coordinate.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ}

/-- The inner product as a real bilinear continuous map. -/
def h2_ip (N : ℕ) : Ch N →L[ℝ] Ch N →L[ℝ] ℝ := innerSL ℝ

theorem h2_ip_apply (w : Ch N) : h2_ip N w = innerSL ℝ w := rfl

theorem h2_norm_ip_le : ‖h2_ip N‖ ≤ 1 := norm_innerSL_le ℝ

/-- First derivative of the Gaussian as a continuous linear map. -/
def h2_g1 (v : ℝ) (w : Ch N) : Ch N →L[ℝ] ℝ := (-(1 / v) * h2_g v w) • innerSL ℝ w

/-- Second derivative of the Gaussian. -/
def h2_g2 (v : ℝ) (w : Ch N) : Ch N →L[ℝ] Ch N →L[ℝ] ℝ :=
  (-(1 / v) * h2_g v w) • h2_ip N +
    ((-(1 / v)) • h2_g1 v w).smulRight (innerSL ℝ w)

theorem h2_hasFDerivAt_g {v : ℝ} (hv : 0 < v) (w : Ch N) : HasFDerivAt (h2_g v) (h2_g1 v w) w := by
  have h1 := (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have h2 := ((h1.const_mul (-(1 / (2 * v)))).exp).const_mul ((2 * Real.pi * v) ^ (-(N : ℝ) / 2))
  refine h2.congr_fderiv ?_
  ext h
  simp only [h2_g1, h2_g, smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  field_simp
  ring

theorem h2_hasFDerivAt_g1 {v : ℝ} (hv : 0 < v) (w : Ch N) : HasFDerivAt (h2_g1 v) (h2_g2 v w) w := by
  have hc : HasFDerivAt (fun w : Ch N => -(1 / v) * h2_g v w) ((-(1 / v)) • h2_g1 v w) w :=
    (h2_hasFDerivAt_g hv w).const_mul _
  have hf : HasFDerivAt (fun w : Ch N => innerSL ℝ w) (h2_ip N) w := (h2_ip N).hasFDerivAt
  exact hc.smul hf

theorem h2_fderiv_g {v : ℝ} (hv : 0 < v) : fderiv ℝ (h2_g (N := N) v) = h2_g1 v :=
  funext fun w => (h2_hasFDerivAt_g hv w).fderiv

theorem h2_fderiv_g1 {v : ℝ} (hv : 0 < v) : fderiv ℝ (h2_g1 (N := N) v) = h2_g2 v :=
  funext fun w => (h2_hasFDerivAt_g1 hv w).fderiv

theorem h2_contDiff_g (v : ℝ) : ContDiff ℝ ⊤ (h2_g (N := N) v) := by
  unfold h2_g
  exact contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ)))

theorem h2_continuous_g1 {v : ℝ} (hv : 0 < v) : Continuous (h2_g1 (N := N) v) := by
  have : h2_g1 (N := N) v = fderiv ℝ (h2_g v) := (h2_fderiv_g hv).symm
  rw [this]
  exact (h2_contDiff_g v).continuous_fderiv (by simp)

theorem h2_continuous_g2 {v : ℝ} (hv : 0 < v) : Continuous (h2_g2 (N := N) v) := by
  have : h2_g2 (N := N) v = fderiv ℝ (fderiv ℝ (h2_g v)) := by rw [h2_fderiv_g hv, h2_fderiv_g1 hv]
  rw [this]
  exact ((h2_contDiff_g v).fderiv_right (m := 1) (by simp)).continuous_fderiv (by simp)

theorem h2_norm_g1 {v : ℝ} (hv : 0 < v) (w : Ch N) : ‖h2_g1 v w‖ = (1 / v) * h2_g v w * ‖w‖ := by
  unfold h2_g1
  rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1 / v),
    abs_of_pos (h2_g_pos hv w)]

theorem h2_norm_g2_le {v : ℝ} (hv : 0 < v) (w : Ch N) :
    ‖h2_g2 v w‖ ≤ (1 / v) * h2_g v w + (1 / v) * (1 / v) * h2_g v w * ‖w‖ ^ 2 := by
  have hg := h2_g_pos hv w
  have h1 : ‖(-(1 / v) * h2_g v w) • h2_ip N‖ ≤ (1 / v) * h2_g v w := by
    calc ‖(-(1 / v) * h2_g v w) • h2_ip N‖
        ≤ ‖(-(1 / v) * h2_g v w)‖ * ‖h2_ip N‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ = (1 / v) * h2_g v w * ‖h2_ip N‖ := by
          rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1 / v), abs_of_pos hg]
      _ ≤ (1 / v) * h2_g v w * 1 := mul_le_mul_of_nonneg_left h2_norm_ip_le (by positivity)
      _ = _ := mul_one _
  have h2 : ‖((-(1 / v)) • h2_g1 v w).smulRight (innerSL ℝ w)‖ ≤ (1 / v) * (1 / v) * h2_g v w * ‖w‖ ^ 2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, innerSL_apply_norm, h2_norm_g1 hv, Real.norm_eq_abs,
      abs_neg, abs_of_pos (by positivity : 0 < 1 / v)]
    nlinarith [sq_nonneg ‖w‖]
  have e : h2_g2 v w = (-(1 / v) * h2_g v w) • h2_ip N + ((-(1 / v)) • h2_g1 v w).smulRight (innerSL ℝ w) := rfl
  rw [e]
  exact le_trans (norm_add_le ((-(1 / v) * h2_g v w) • h2_ip N) (((-(1 / v)) • h2_g1 v w).smulRight (innerSL ℝ w))) (add_le_add h1 h2)

/-- Gaussian domination of `g`, `g'`, `g''` with the common rate `1/(4v)`. -/
theorem h2_g_bounds {v : ℝ} (hv : 0 < v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Ch N, ‖h2_g v w‖ ≤ C * Real.exp (-(1 / (4 * v)) * ‖w‖ ^ 2) ∧
      ‖h2_g1 v w‖ ≤ C * Real.exp (-(1 / (4 * v)) * ‖w‖ ^ 2) ∧ ‖h2_g2 v w‖ ≤ C * Real.exp (-(1 / (4 * v)) * ‖w‖ ^ 2) := by
  set c0 : ℝ := (2 * Real.pi * v) ^ (-(N : ℝ) / 2) with hc0
  have hc0pos : 0 < c0 := by
    have : 0 < 2 * Real.pi * v := by positivity
    positivity
  set b : ℝ := 1 / (2 * v) with hb
  have hbpos : 0 < b := by positivity
  set K : ℝ := 1 + 2 / b with hK
  have hKpos : 0 < K := by positivity
  refine ⟨c0 * (1 + (1 / v) * K + 1 / v + (1 / v) * (1 / v) * (2 / b)), by positivity, fun w => ?_⟩
  have e2 : (1 / (4 * v)) = b / 2 := by rw [hb]; field_simp; ring
  rw [e2]
  set r : ℝ := ‖w‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hE1 : h2_g v w = c0 * Real.exp (-b * r ^ 2) := rfl
  have hp1 : 0 < Real.exp (-b * r ^ 2) := Real.exp_pos _
  have hp2 : 0 < Real.exp (-(b / 2) * r ^ 2) := Real.exp_pos _
  have L1 : Real.exp (-b * r ^ 2) ≤ Real.exp (-(b / 2) * r ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg hbpos.le (sq_nonneg r)])
  have L3 := h2_sq_exp_le hbpos r
  have L2 : r * Real.exp (-b * r ^ 2) ≤ K * Real.exp (-(b / 2) * r ^ 2) := by
    have h1 : r ≤ 1 + r ^ 2 := by nlinarith [sq_nonneg (r - 1)]
    calc r * Real.exp (-b * r ^ 2) ≤ (1 + r ^ 2) * Real.exp (-b * r ^ 2) := mul_le_mul_of_nonneg_right h1 hp1.le
      _ = Real.exp (-b * r ^ 2) + r ^ 2 * Real.exp (-b * r ^ 2) := by ring
      _ ≤ Real.exp (-(b / 2) * r ^ 2) + (2 / b) * Real.exp (-(b / 2) * r ^ 2) := add_le_add L1 L3
      _ = K * Real.exp (-(b / 2) * r ^ 2) := by rw [hK]; ring
  have hv1 : 0 < 1 / v := by positivity
  have hX1 : 0 ≤ c0 * (1 / v) * K * Real.exp (-(b / 2) * r ^ 2) := by positivity
  have hX2 : 0 ≤ c0 * Real.exp (-(b / 2) * r ^ 2) := by positivity
  have hX3 : 0 ≤ c0 * (1 / v) * Real.exp (-(b / 2) * r ^ 2) := by positivity
  have hX4 : 0 ≤ c0 * (1 / v) * (1 / v) * (2 / b) * Real.exp (-(b / 2) * r ^ 2) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.norm_of_nonneg (h2_g_pos hv w).le, hE1]
    nlinarith [mul_le_mul_of_nonneg_left L1 hc0pos.le]
  · rw [h2_norm_g1 hv, hE1]
    have := mul_le_mul_of_nonneg_left L2 (by positivity : 0 ≤ c0 * (1 / v))
    nlinarith
  · refine (h2_norm_g2_le hv w).trans ?_
    rw [hE1]
    have h5 := mul_le_mul_of_nonneg_left L1 (by positivity : 0 ≤ c0 * (1 / v))
    have h6 := mul_le_mul_of_nonneg_left L3 (by positivity : 0 ≤ c0 * (1 / v) * (1 / v))
    nlinarith

/-! ### The periodised Gaussian -/

theorem h2_norm_ge_mean [NeZero N] (z : Ch N) : Real.sqrt N * |h2_mean z| ≤ ‖z‖ := by
  have h := h2_norm_sq z
  have : (Real.sqrt N * |h2_mean z|) ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), sq_abs, h]; nlinarith [sq_nonneg ‖h2_perp z‖]
  exact (abs_le_of_sq_le_sq' this (norm_nonneg _)).2

/-- Uniform bound of a periodised Gaussian-bounded function, with transverse Gaussian decay. -/
theorem h2_periodise_norm_le [NeZero N] {F : Type*} [NormedAddCommGroup F] {φ : Ch N → F} {C c : ℝ} (hc : 0 < c)
    (hφb : ∀ w, ‖φ w‖ ≤ C * Real.exp (-c * ‖w‖ ^ 2)) (w : Ch N) :
    ‖∑' m : ℤ, φ (w + (m : ℝ) • cep_diag N)‖ ≤
      C * (∑' m : ℤ, Real.exp (-c * (max (|(m : ℝ)| * Real.sqrt N - Real.sqrt N) 0) ^ 2)) *
        Real.exp (-c * ‖h2_perp w‖ ^ 2) := by
  have hC : 0 ≤ C := by
    have := hφb 0
    have h2 : 0 < Real.exp (-c * ‖(0 : Ch N)‖ ^ 2) := Real.exp_pos _
    by_contra h
    have h' : C < 0 := not_le.1 h
    nlinarith [norm_nonneg (φ 0)]
  set j : ℤ := ⌊h2_mean w⌋ with hj
  set w' : Ch N := w + ((-j : ℤ) : ℝ) • cep_diag N with hw'
  have hshift : ∑' m : ℤ, φ (w + (m : ℝ) • cep_diag N) = ∑' m : ℤ, φ (w' + (m : ℝ) • cep_diag N) := by
    conv_rhs => rw [← (Equiv.addRight j).tsum_eq (fun m : ℤ => φ (w' + (m : ℝ) • cep_diag N))]
    refine tsum_congr fun m => ?_
    congr 1
    simp only [hw', Equiv.coe_addRight, Int.cast_add, Int.cast_neg]
    module
  have hmean : h2_mean w' = h2_mean w - j := by
    rw [hw', h2_mean_add_diag]; push_cast; ring
  have hs0 : 0 ≤ h2_mean w' := by rw [hmean]; linarith [Int.floor_le (h2_mean w)]
  have hs1 : h2_mean w' < 1 := by rw [hmean]; linarith [Int.lt_floor_add_one (h2_mean w)]
  have hperp : h2_perp w' = h2_perp w := by rw [hw']; exact h2_perp_add_diag _ _
  have hterm : ∀ m : ℤ, ‖φ (w' + (m : ℝ) • cep_diag N)‖ ≤
      C * Real.exp (-c * (max (|(m : ℝ)| * Real.sqrt N - Real.sqrt N) 0) ^ 2) * Real.exp (-c * ‖h2_perp w‖ ^ 2) := by
    intro m
    set z : Ch N := w' + (m : ℝ) • cep_diag N with hz
    have hzm : h2_mean z = h2_mean w' + m := by rw [hz, h2_mean_add_diag]
    have hzp : h2_perp z = h2_perp w := by rw [hz, h2_perp_add_diag, hperp]
    have h1 : Real.sqrt N * |h2_mean z| ≤ ‖z‖ := h2_norm_ge_mean z
    have h2 : |(m : ℝ)| * Real.sqrt N - Real.sqrt N ≤ Real.sqrt N * |h2_mean z| := by
      rw [hzm]
      have h3 : |(m : ℝ)| - 1 ≤ |h2_mean w' + m| := by
        have := abs_sub_abs_le_abs_sub (m : ℝ) (-(h2_mean w'))
        rw [abs_neg, abs_of_nonneg hs0] at this
        have e : (m : ℝ) - -h2_mean w' = h2_mean w' + m := by ring
        rw [e] at this
        linarith [abs_of_nonneg hs0]
      nlinarith [Real.sqrt_nonneg (N : ℝ)]
    have h4 : max (|(m : ℝ)| * Real.sqrt N - Real.sqrt N) 0 ≤ ‖z‖ :=
      max_le (h2.trans h1) (norm_nonneg _)
    have h5 : ‖z‖ ^ 2 = ‖h2_perp w‖ ^ 2 + N * h2_mean z ^ 2 := by rw [h2_norm_sq z, hzp]
    have h6 : (max (|(m : ℝ)| * Real.sqrt N - Real.sqrt N) 0) ^ 2 ≤ N * h2_mean z ^ 2 := by
      have h7 : (max (|(m : ℝ)| * Real.sqrt N - Real.sqrt N) 0) ^ 2 ≤ (Real.sqrt N * |h2_mean z|) ^ 2 :=
        pow_le_pow_left₀ (le_max_right _ _) (max_le h2 (by positivity)) 2
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), sq_abs] at h7
      exact h7
    calc ‖φ z‖ ≤ C * Real.exp (-c * ‖z‖ ^ 2) := hφb z
      _ ≤ C * (Real.exp (-c * (max (|(m : ℝ)| * Real.sqrt N - Real.sqrt N) 0) ^ 2) *
            Real.exp (-c * ‖h2_perp w‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          rw [← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          rw [h5]
          nlinarith
      _ = _ := by ring
  have hsum : HasSum (fun m : ℤ => C * Real.exp (-c * (max (|(m : ℝ)| * Real.sqrt N - Real.sqrt N) 0) ^ 2) *
      Real.exp (-c * ‖h2_perp w‖ ^ 2))
      (C * (∑' m : ℤ, Real.exp (-c * (max (|(m : ℝ)| * Real.sqrt N - Real.sqrt N) 0) ^ 2)) *
        Real.exp (-c * ‖h2_perp w‖ ^ 2)) :=
    (((h2_summable_lat (N := N) (T := Real.sqrt N) hc).hasSum.mul_left C).mul_right _)
  rw [hshift]
  exact tsum_of_norm_bounded hsum hterm

/-- Periodised Gaussian and its derivatives (termwise sums). -/
def h2_per (v : ℝ) (w : Ch N) : ℝ := ∑' m : ℤ, h2_g v (w + (m : ℝ) • cep_diag N)

def h2_per1 (v : ℝ) (w : Ch N) : Ch N →L[ℝ] ℝ := ∑' m : ℤ, h2_g1 v (w + (m : ℝ) • cep_diag N)

def h2_per2 (v : ℝ) (w : Ch N) : Ch N →L[ℝ] Ch N →L[ℝ] ℝ := ∑' m : ℤ, h2_g2 v (w + (m : ℝ) • cep_diag N)

theorem h2_tsum_periodic {F : Type*} [AddCommMonoid F] [TopologicalSpace F] (φ : Ch N → F) (w : Ch N) :
    ∑' m : ℤ, φ (w + cep_diag N + (m : ℝ) • cep_diag N) = ∑' m : ℤ, φ (w + (m : ℝ) • cep_diag N) := by
  rw [← (Equiv.addRight (1 : ℤ)).tsum_eq (fun m : ℤ => φ (w + (m : ℝ) • cep_diag N))]
  refine tsum_congr fun m => ?_
  simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one]
  congr 1
  module

theorem h2_per_periodic (v : ℝ) (w : Ch N) : h2_per v (w + cep_diag N) = h2_per v w :=
  h2_tsum_periodic (h2_g v) w

theorem h2_per1_periodic (v : ℝ) (w : Ch N) : h2_per1 v (w + cep_diag N) = h2_per1 v w :=
  h2_tsum_periodic (h2_g1 v) w

theorem h2_per2_periodic (v : ℝ) (w : Ch N) : h2_per2 v (w + cep_diag N) = h2_per2 v w :=
  h2_tsum_periodic (h2_g2 v) w

section
variable [NeZero N]

theorem h2_hasFDerivAt_per {v : ℝ} (hv : 0 < v) (w : Ch N) : HasFDerivAt (h2_per v) (h2_per1 v w) w := by
  obtain ⟨C, hC, hb⟩ := h2_g_bounds (N := N) hv
  exact (h2_periodise_hasFDerivAt (φ := h2_g (N := N) v) (φ' := h2_g1 (N := N) v) (h2_hasFDerivAt_g hv)
    (c := 1 / (4 * v)) (C := C) (by positivity) (fun w => (hb w).1) (fun w => (hb w).2.1) w).2

theorem h2_hasFDerivAt_per1 {v : ℝ} (hv : 0 < v) (w : Ch N) : HasFDerivAt (h2_per1 v) (h2_per2 v w) w := by
  obtain ⟨C, hC, hb⟩ := h2_g_bounds (N := N) hv
  exact (h2_periodise_hasFDerivAt (φ := h2_g1 (N := N) v) (φ' := h2_g2 (N := N) v) (h2_hasFDerivAt_g1 hv)
    (c := 1 / (4 * v)) (C := C) (by positivity) (fun w => (hb w).2.1) (fun w => (hb w).2.2) w).2

theorem h2_continuous_per2 {v : ℝ} (hv : 0 < v) : Continuous (h2_per2 (N := N) v) := by
  obtain ⟨C, hC, hb⟩ := h2_g_bounds (N := N) hv
  exact h2_periodise_continuous (φ := h2_g2 (N := N) v) (h2_continuous_g2 hv) (c := 1 / (4 * v)) (C := C)
    (by positivity) (fun w => (hb w).2.2)

theorem h2_contDiff_per {v : ℝ} (hv : 0 < v) : ContDiff ℝ 2 (h2_per (N := N) v) := by
  have h1 : ContDiff ℝ 1 (h2_per1 (N := N) v) := by
    have := (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 0) (f := h2_per1 (N := N) v)).2
      ⟨h2_per2 v, contDiff_zero.2 (h2_continuous_per2 hv), h2_hasFDerivAt_per1 hv⟩
    simpa using this
  have := (contDiff_succ_iff_hasFDerivAt (𝕜 := ℝ) (n := 1) (f := h2_per (N := N) v)).2
    ⟨h2_per1 v, h1, h2_hasFDerivAt_per hv⟩
  simpa [one_add_one_eq_two] using this

theorem h2_fderiv_per {v : ℝ} (hv : 0 < v) : fderiv ℝ (h2_per (N := N) v) = h2_per1 v :=
  funext fun w => (h2_hasFDerivAt_per hv w).fderiv

theorem h2_fderiv_per1 {v : ℝ} (hv : 0 < v) : fderiv ℝ (h2_per1 (N := N) v) = h2_per2 v :=
  funext fun w => (h2_hasFDerivAt_per1 hv w).fderiv

theorem h2_summable_g_trans {v : ℝ} (hv : 0 < v) (w : Ch N) :
    Summable (fun m : ℤ => h2_g v (w + (m : ℝ) • cep_diag N)) :=
  (h2_periodise_hasFDerivAt (φ := h2_g (N := N) v) (φ' := h2_g1 (N := N) v) (h2_hasFDerivAt_g hv)
    (c := 1 / (4 * v)) (C := (h2_g_bounds (N := N) hv).choose) (by positivity)
    (fun w => (h2_g_bounds (N := N) hv).choose_spec.2 w |>.1) (fun w => (h2_g_bounds (N := N) hv).choose_spec.2 w |>.2.1) w).1

theorem h2_per_pos {v : ℝ} (hv : 0 < v) (w : Ch N) : 0 < h2_per v w :=
  (h2_summable_g_trans hv w).tsum_pos (fun _ => (h2_g_pos hv _).le) 0 (h2_g_pos hv _)

/-- Global bounds with transverse Gaussian decay. -/
theorem h2_per_bounds {v : ℝ} (hv : 0 < v) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : Ch N, ‖h2_per v w‖ ≤ B * Real.exp (-(1 / (4 * v)) * ‖h2_perp w‖ ^ 2) ∧
      ‖h2_per1 v w‖ ≤ B * Real.exp (-(1 / (4 * v)) * ‖h2_perp w‖ ^ 2) ∧
      ‖h2_per2 v w‖ ≤ B * Real.exp (-(1 / (4 * v)) * ‖h2_perp w‖ ^ 2) := by
  obtain ⟨C, hC, hb⟩ := h2_g_bounds (N := N) hv
  have hc : 0 < 1 / (4 * v) := by positivity
  set S : ℝ := ∑' m : ℤ, Real.exp (-(1 / (4 * v)) * (max (|(m : ℝ)| * Real.sqrt N - Real.sqrt N) 0) ^ 2) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun m => (Real.exp_pos _).le
  refine ⟨C * S, mul_nonneg hC hS0, fun w => ⟨?_, ?_, ?_⟩⟩
  · exact h2_periodise_norm_le (φ := h2_g (N := N) v) (C := C) hc (fun w => (hb w).1) w
  · exact h2_periodise_norm_le (φ := h2_g1 (N := N) v) (C := C) hc (fun w => (hb w).2.1) w
  · exact h2_periodise_norm_le (φ := h2_g2 (N := N) v) (C := C) hc (fun w => (hb w).2.2) w

end

end HRS.MC.CepH2
