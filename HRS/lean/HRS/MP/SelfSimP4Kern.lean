import HRS.MP.SelfSimP4Spec

/-!
# MP-SSP4KERN: `p4_kernel` (truncated kernels and the potential hypotheses)

Namespace `HRS.MP.SelfSimP4Impl`, helpers `p4k_`.  Theorem `p4_kernel_proof`, tied to `HRS.MP.SelfSimP4.p4_kernel`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP4Impl

/-! ### Radial functions on `Euc d` -/

theorem p4k_radial_grad (d : ℕ) (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (x : Euc d) :
    HasGradientAt (fun y : Euc d => h (‖y‖ ^ 2)) ((2 * deriv h (‖x‖ ^ 2)) • x) x := by
  have h1 : HasFDerivAt (fun y : Euc d => ‖y‖ ^ 2) (2 • (innerSL ℝ x)) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h2 : HasDerivAt h (deriv h (‖x‖ ^ 2)) (‖x‖ ^ 2) :=
    ((hh.differentiable (by simp)) _).hasDerivAt
  have h3 := h2.comp_hasFDerivAt x h1
  rw [hasGradientAt_iff_hasFDerivAt]
  have e : InnerProductSpace.toDual ℝ (Euc d) ((2 * deriv h (‖x‖ ^ 2)) • x) =
      deriv h (‖x‖ ^ 2) • (2 • (innerSL ℝ x)) := by
    ext v
    simp [InnerProductSpace.toDual_apply_apply, real_inner_comm]
    ring
  rw [e]
  exact h3

theorem p4k_radial_lip (d : ℕ) (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (L : ℝ)
    (hL : ∀ t : ℝ, 0 ≤ t → |2 * deriv h t| + 2 * t * |2 * deriv (deriv h) t| ≤ L) :
    ∃ K : ℝ≥0, LipschitzWith K (fun x : Euc d => (2 * deriv h (‖x‖ ^ 2)) • x) := by
  have hd1 : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.mp hh).2
  have hd2 : Differentiable ℝ (deriv h) := (contDiff_infty_iff_deriv.mp hd1).1
  have key : ∀ x : Euc d, HasFDerivAt (fun x : Euc d => (2 * deriv h (‖x‖ ^ 2)) • x)
      ((2 * deriv h (‖x‖ ^ 2)) • ContinuousLinearMap.id ℝ (Euc d) +
        ((2 * deriv (deriv h) (‖x‖ ^ 2)) • (2 • innerSL ℝ x)).smulRight x) x := by
    intro x
    have h1 : HasFDerivAt (fun y : Euc d => ‖y‖ ^ 2) (2 • (innerSL ℝ x)) x :=
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    have h2 : HasDerivAt (fun t => 2 * deriv h t) (2 * deriv (deriv h) (‖x‖ ^ 2)) (‖x‖ ^ 2) :=
      ((hd2 _).hasDerivAt).const_mul 2
    have h3 := h2.comp_hasFDerivAt x h1
    exact h3.smul (hasFDerivAt_id x)
  refine ⟨Real.toNNReal L, lipschitzWith_of_nnnorm_fderiv_le (fun x => (key x).differentiableAt) ?_⟩
  intro x
  rw [(key x).fderiv]
  have hn : ‖(2 • innerSL ℝ x : Euc d →L[ℝ] ℝ)‖ ≤ 2 * ‖x‖ := by
    calc ‖(2 • innerSL ℝ x : Euc d →L[ℝ] ℝ)‖ ≤ 2 * ‖innerSL ℝ x‖ := by
          rw [two_smul]
          calc _ ≤ ‖innerSL ℝ x‖ + ‖innerSL ℝ x‖ := norm_add_le _ _
            _ = _ := by ring
      _ ≤ 2 * ‖x‖ := by
          have := innerSL_apply_norm (𝕜 := ℝ) x
          rw [this]
  have hb : ‖(2 * deriv h (‖x‖ ^ 2)) • ContinuousLinearMap.id ℝ (Euc d) +
      ((2 * deriv (deriv h) (‖x‖ ^ 2)) • (2 • innerSL ℝ x)).smulRight x‖ ≤ L := by
    refine (norm_add_le _ _).trans ?_
    have e1 : ‖(2 * deriv h (‖x‖ ^ 2)) • ContinuousLinearMap.id ℝ (Euc d)‖ ≤
        |2 * deriv h (‖x‖ ^ 2)| := by
      rw [norm_smul, Real.norm_eq_abs]
      calc _ ≤ |2 * deriv h (‖x‖ ^ 2)| * 1 :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (abs_nonneg _)
        _ = _ := mul_one _
    have e2 : ‖((2 * deriv (deriv h) (‖x‖ ^ 2)) • (2 • innerSL ℝ x)).smulRight x‖ ≤
        2 * ‖x‖ ^ 2 * |2 * deriv (deriv h) (‖x‖ ^ 2)| := by
      rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
      have := mul_le_mul_of_nonneg_left hn (abs_nonneg (2 * deriv (deriv h) (‖x‖ ^ 2)))
      nlinarith [norm_nonneg x, abs_nonneg (2 * deriv (deriv h) (‖x‖ ^ 2))]
    have := hL (‖x‖ ^ 2) (sq_nonneg _)
    linarith
  rw [← NNReal.coe_le_coe]
  simp only [coe_nnnorm, Real.coe_toNNReal']
  exact hb.trans (le_max_left _ _)

/-! ### The profile -/

/-- Smooth positive modification `q_a(t) ≥ t` of the identity, equal to `t` for `t ≥ a/2`. -/
def p4k_q (a t : ℝ) : ℝ :=
  (1 - Real.smoothTransition (2 * t / a)) * (a / 2) + Real.smoothTransition (2 * t / a) * t

/-- `Φ_s(√y)` as a function of `y = ‖x‖²`. -/
def p4k_psi (s y : ℝ) : ℝ := if s = 0 then -(1 / 2) * Real.log y else y ^ (-s / 2)

def p4k_h (s a t : ℝ) : ℝ := p4k_psi s (p4k_q a t)

theorem p4k_q_contDiff (a : ℝ) : ContDiff ℝ ∞ (p4k_q a) := by
  unfold p4k_q
  have hs : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition (2 * t / a)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).div_const a)
  exact ((contDiff_const.sub hs).mul contDiff_const).add (hs.mul contDiff_id)

theorem p4k_q_eq {a t : ℝ} (ha : 0 < a) (ht : a / 2 ≤ t) : p4k_q a t = t := by
  have h1 : 1 ≤ 2 * t / a := by rw [le_div_iff₀ ha]; linarith
  unfold p4k_q
  rw [Real.smoothTransition.one_of_one_le h1]; ring

theorem p4k_q_ge {a : ℝ} (ha : 0 < a) (t : ℝ) : t ≤ p4k_q a t := by
  by_cases ht : a / 2 ≤ t
  · rw [p4k_q_eq ha ht]
  · push_neg at ht
    unfold p4k_q
    have h0 := Real.smoothTransition.nonneg (2 * t / a)
    have h1 := Real.smoothTransition.le_one (2 * t / a)
    nlinarith

theorem p4k_q_pos {a : ℝ} (ha : 0 < a) (t : ℝ) : 0 < p4k_q a t := by
  by_cases ht : 0 < t
  · have := p4k_q_ge ha t
    linarith
  · push_neg at ht
    unfold p4k_q
    have : Real.smoothTransition (2 * t / a) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le)
    rw [this]; linarith

theorem p4k_q_le {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 ≤ t) : p4k_q a t ≤ t + a / 2 := by
  unfold p4k_q
  have h0 := Real.smoothTransition.nonneg (2 * t / a)
  have h1 := Real.smoothTransition.le_one (2 * t / a)
  nlinarith

theorem p4k_psi_contDiffAt (s : ℝ) {y : ℝ} (hy : 0 < y) : ContDiffAt ℝ ∞ (p4k_psi s) y := by
  unfold p4k_psi
  by_cases hs : s = 0
  · simp only [hs, if_true]
    exact contDiffAt_const.mul (Real.contDiffAt_log.2 hy.ne')
  · simp only [hs, if_false]
    exact Real.contDiffAt_rpow_const_of_ne hy.ne'

theorem p4k_h_contDiff (s : ℝ) {a : ℝ} (ha : 0 < a) : ContDiff ℝ ∞ (p4k_h s a) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  exact (p4k_psi_contDiffAt s (p4k_q_pos ha t)).comp t (p4k_q_contDiff a).contDiffAt

theorem p4k_psi_anti {s : ℝ} (hs : 0 ≤ s) {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) :
    p4k_psi s z ≤ p4k_psi s y := by
  unfold p4k_psi
  by_cases h0 : s = 0
  · simp only [h0, if_true]
    have := Real.log_le_log hy hyz
    linarith
  · simp only [h0, if_false]
    exact Real.rpow_le_rpow_of_nonpos hy hyz (by linarith)

theorem p4k_psi_norm_sq (d : ℕ) (s : ℝ) (x : Euc d) :
    p4k_psi s (‖x‖ ^ 2) = rieszKernel d s x := by
  unfold p4k_psi rieszKernel
  by_cases h0 : s = 0
  · simp only [h0, if_true]
    rw [Real.log_pow]; push_cast; ring
  · simp only [h0, if_false]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
    congr 1; push_cast; ring

/-! ### Derivatives of the profile away from the origin -/

def p4k_psi1 (s y : ℝ) : ℝ := if s = 0 then -(1 / 2) * y⁻¹ else (-s / 2) * y ^ (-s / 2 - 1)

def p4k_psi2 (s y : ℝ) : ℝ :=
  if s = 0 then (1 / 2) * (y ^ 2)⁻¹ else (-s / 2) * ((-s / 2 - 1) * y ^ (-s / 2 - 1 - 1))

theorem p4k_psi_hasDeriv (s : ℝ) {y : ℝ} (hy : 0 < y) : HasDerivAt (p4k_psi s) (p4k_psi1 s y) y := by
  unfold p4k_psi p4k_psi1
  by_cases hs : s = 0
  · simp only [hs, if_true]
    exact (Real.hasDerivAt_log hy.ne').const_mul _
  · simp only [hs, if_false]
    exact Real.hasDerivAt_rpow_const (Or.inl hy.ne')

theorem p4k_psi1_hasDeriv (s : ℝ) {y : ℝ} (hy : 0 < y) : HasDerivAt (p4k_psi1 s) (p4k_psi2 s y) y := by
  unfold p4k_psi1 p4k_psi2
  by_cases hs : s = 0
  · simp only [hs, if_true]
    have := (hasDerivAt_inv hy.ne').const_mul (-(1 / 2 : ℝ))
    convert this using 1
    field_simp
  · simp only [hs, if_false]
    exact (Real.hasDerivAt_rpow_const (Or.inl hy.ne')).const_mul _

/-- The Lipschitz-gradient bound for the profile. -/
theorem p4k_bound (s : ℝ) (hs : 0 ≤ s) {a : ℝ} (ha : 0 < a) :
    ∃ L : ℝ, ∀ t : ℝ, 0 ≤ t →
      |2 * deriv (p4k_h s a) t| + 2 * t * |2 * deriv (deriv (p4k_h s a)) t| ≤ L := by
  have hh := p4k_h_contDiff s ha
  have hd1 : ContDiff ℝ ∞ (deriv (p4k_h s a)) := (contDiff_infty_iff_deriv.mp hh).2
  -- explicit derivatives for `t > a/2`
  have hE : ∀ t : ℝ, a / 2 < t → p4k_h s a =ᶠ[𝓝 t] p4k_psi s := by
    intro t ht
    filter_upwards [Ioi_mem_nhds ht] with u hu
    unfold p4k_h
    rw [p4k_q_eq ha (le_of_lt hu)]
  have hD1 : ∀ t : ℝ, a / 2 < t → deriv (p4k_h s a) t = p4k_psi1 s t := by
    intro t ht
    have h0 : 0 < t := by linarith
    exact ((p4k_psi_hasDeriv s h0).congr_of_eventuallyEq (hE t ht)).deriv
  have hD2 : ∀ t : ℝ, a / 2 < t → deriv (deriv (p4k_h s a)) t = p4k_psi2 s t := by
    intro t ht
    have h0 : 0 < t := by linarith
    have hev : deriv (p4k_h s a) =ᶠ[𝓝 t] p4k_psi1 s := by
      filter_upwards [Ioi_mem_nhds ht] with u hu
      exact hD1 u hu
    exact ((p4k_psi1_hasDeriv s h0).congr_of_eventuallyEq hev).deriv
  -- compact part
  have hc : Continuous (fun t : ℝ => |2 * deriv (p4k_h s a) t| +
      2 * t * |2 * deriv (deriv (p4k_h s a)) t|) := by
    have c1 : Continuous (deriv (p4k_h s a)) := hd1.continuous
    have c2 : Continuous (deriv (deriv (p4k_h s a))) := (contDiff_infty_iff_deriv.mp hd1).2.continuous
    fun_prop
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := 0) (b := a)).exists_bound_of_continuousOn hc.continuousOn
  -- far part
  by_cases h0 : s = 0
  · refine ⟨max C (3 / a), fun t ht0 => ?_⟩
    by_cases hta : t ≤ a
    · have := hC t ⟨ht0, hta⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
      exact this.trans (le_max_left _ _)
    · push_neg at hta
      refine le_trans ?_ (le_max_right _ _)
      rw [hD1 t (by linarith), hD2 t (by linarith)]
      unfold p4k_psi1 p4k_psi2
      simp only [h0, if_true]
      have htp : 0 < t := by linarith
      have e : |2 * (-(1 / 2) * t⁻¹)| + 2 * t * |2 * (1 / 2 * (t ^ 2)⁻¹)| = 3 / t := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 2 * (1 / 2 * (t ^ 2)⁻¹))]
        rw [show 2 * (-(1 / 2) * t⁻¹) = -t⁻¹ by ring, abs_neg, abs_of_nonneg (by positivity)]
        field_simp
        ring
      rw [e]
      exact div_le_div_of_nonneg_left (by norm_num) ha hta.le
  · set K := s * (s + 3) * a ^ (-s / 2 - 1) with hK
    refine ⟨max C K, fun t ht0 => ?_⟩
    by_cases hta : t ≤ a
    · have := hC t ⟨ht0, hta⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
      exact this.trans (le_max_left _ _)
    · push_neg at hta
      refine le_trans ?_ (le_max_right _ _)
      rw [hD1 t (by linarith), hD2 t (by linarith)]
      unfold p4k_psi1 p4k_psi2
      simp only [h0, if_false]
      have htp : 0 < t := by linarith
      have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm h0)
      set P := t ^ (-s / 2 - 1) with hP
      have hPpos : 0 < P := Real.rpow_pos_of_pos htp _
      have hPP : t ^ (-s / 2 - 1 - 1) = P / t := by
        rw [Real.rpow_sub htp, Real.rpow_one]
      have e : |2 * (-s / 2 * P)| + 2 * t * |2 * (-s / 2 * ((-s / 2 - 1) * (P / t)))| =
          s * (s + 3) * P := by
        have e1 : 2 * (-s / 2 * P) = -(s * P) := by ring
        have e2 : 2 * (-s / 2 * ((-s / 2 - 1) * (P / t))) = s * (s / 2 + 1) * P / t := by ring
        rw [e1, e2, abs_neg, abs_of_nonneg (by positivity),
          abs_of_nonneg (by positivity)]
        field_simp
        ring
      rw [hPP, e, hK]
      have : P ≤ a ^ (-s / 2 - 1) :=
        Real.rpow_le_rpow_of_nonpos ha hta.le (by linarith)
      have h3 : 0 ≤ s * (s + 3) := by positivity
      exact mul_le_mul_of_nonneg_left this h3

/-! ### The truncated kernel -/

theorem p4k_isKernel (d : ℕ) (s : ℝ) (hs : 0 ≤ s) {r₀ : ℝ} (hr0 : 0 < r₀) (hr1 : r₀ ≤ 1) :
    IsP4Kernel d s r₀ (fun x : Euc d => p4k_h s (r₀ ^ 2) (‖x‖ ^ 2)) := by
  have ha : 0 < r₀ ^ 2 := by positivity
  have hh := p4k_h_contDiff s ha
  refine ⟨⟨hr0, hr1⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hh.of_le (by simp)).comp (contDiff_norm_sq ℝ)
  · intro x; simp
  · obtain ⟨L, hL⟩ := p4k_bound s hs ha
    obtain ⟨K, hK⟩ := p4k_radial_lip d (p4k_h s (r₀ ^ 2)) hh L hL
    refine ⟨K, ?_⟩
    have : gradient (fun x : Euc d => p4k_h s (r₀ ^ 2) (‖x‖ ^ 2)) =
        fun x : Euc d => (2 * deriv (p4k_h s (r₀ ^ 2)) (‖x‖ ^ 2)) • x :=
      funext fun x => (p4k_radial_grad d _ hh x).gradient
    rw [this]; exact hK
  · intro x hx
    rw [← p4k_psi_norm_sq]
    unfold p4k_h
    have hx2 : 0 < ‖x‖ ^ 2 := by positivity
    exact p4k_psi_anti hs hx2 (p4k_q_ge ha _)
  · intro x hx
    rw [← p4k_psi_norm_sq]
    unfold p4k_h
    rw [p4k_q_eq ha]
    have : r₀ ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ hr0.le hx 2
    linarith
  · intro x
    unfold p4k_h p4k_psi
    have hlog : 0 ≤ Real.log (1 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
    by_cases h0 : s = 0
    · simp only [h0, if_true]
      have hq := p4k_q_le ha (sq_nonneg ‖x‖)
      have hqp := p4k_q_pos ha (‖x‖ ^ 2)
      have h1 : p4k_q (r₀ ^ 2) (‖x‖ ^ 2) ≤ (1 + ‖x‖) ^ 2 := by
        nlinarith [norm_nonneg x]
      have := Real.log_le_log hqp h1
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    · simp only [h0, if_false]
      have := Real.rpow_nonneg (p4k_q_pos ha (‖x‖ ^ 2)).le (-s / 2)
      linarith
  · intro hs' x
    unfold p4k_h p4k_psi
    have : s ≠ 0 := hs'.ne'
    simp only [this, if_false]
    exact Real.rpow_nonneg (p4k_q_pos ha (‖x‖ ^ 2)).le _

/-! ### The potential: derivative and drift -/

variable {d : ℕ}

theorem p4k_sum_swap {N : ℕ} (f : Fin N → Fin N → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, f i j = ∑ j, ∑ i ∈ Finset.univ.erase j, f i j := by
  have h : ∀ g : Fin N → Fin N → ℝ, ∑ i, ∑ j ∈ Finset.univ.erase i, g i j =
      ∑ i, ∑ j, if j ≠ i then g i j else 0 := fun g => by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter, Finset.filter_ne']
  rw [h]
  have h2 : ∑ j, ∑ i ∈ Finset.univ.erase j, f i j = ∑ j, ∑ i, if i ≠ j then f i j else 0 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_filter, Finset.filter_ne']
  rw [h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h, Ne.symm h]

theorem p4k_inner_grad (k : Euc d → ℝ) (y w : Euc d) :
    inner ℝ (gradient k y) w = fderiv ℝ k y w := by
  unfold gradient
  exact InnerProductSpace.toDual_symm_apply

theorem p4k_grad_odd {k : Euc d → ℝ} (hk : Differentiable ℝ k) (hev : ∀ x, k (-x) = k x) (y : Euc d) :
    gradient k (-y) = - gradient k y := by
  have h1 : fderiv ℝ (fun x => k (-x)) y = -fderiv ℝ k (-y) := by
    have := ((hk (-y)).hasFDerivAt.comp y (hasFDerivAt_id y).fun_neg).fderiv
    change fderiv ℝ (k ∘ Neg.neg) y = _
    rw [this]
    ext v; simp
  have h2 : (fun x => k (-x)) = k := funext hev
  rw [h2] at h1
  unfold gradient
  rw [h1]
  simp [map_neg]


def p4k_pairSum (k : Euc d → ℝ) (N : ℕ) (Ξ : EucConfig d N) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, k (Ξ i - Ξ j)

theorem p4k_pairSum_hasFDeriv {k : Euc d → ℝ} (hk : Differentiable ℝ k) {N : ℕ} (Ξ : EucConfig d N) :
    HasFDerivAt (p4k_pairSum k N)
      (∑ i, ∑ j ∈ Finset.univ.erase i, (fderiv ℝ k (Ξ i - Ξ j)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i -
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j)) Ξ := by
  unfold p4k_pairSum
  refine HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ => ?_
  exact (hk (Ξ i - Ξ j)).hasFDerivAt.comp Ξ ((hasFDerivAt_apply i Ξ).sub (hasFDerivAt_apply j Ξ))

theorem p4k_pair_apply {k : Euc d → ℝ} (hk : Differentiable ℝ k) (hev : ∀ x, k (-x) = k x) {N : ℕ}
    (Ξ v : EucConfig d N) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, (fderiv ℝ k (Ξ i - Ξ j)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i -
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j)) v =
      2 * ∑ i, inner ℝ (∑ j ∈ Finset.univ.erase i, gradient k (Ξ i - Ξ j)) (v i) := by
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.proj_apply]
  simp only [← p4k_inner_grad, inner_sub_right, Finset.sum_sub_distrib, sum_inner]
  have h2 := p4k_sum_swap (fun i j => inner ℝ (gradient k (Ξ i - Ξ j)) (v j))
  rw [h2]
  have h3 : ∑ j, ∑ i ∈ Finset.univ.erase j, inner ℝ (gradient k (Ξ i - Ξ j)) (v j) =
      - ∑ i, ∑ j ∈ Finset.univ.erase i, inner ℝ (gradient k (Ξ i - Ξ j)) (v i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Ξ i - Ξ j = -(Ξ j - Ξ i) := by abel
    rw [this, p4k_grad_odd hk hev, inner_neg_left]
  rw [h3]; ring

theorem p4k_p4InnerL_apply {N : ℕ} (y v : EucConfig d N) : p4InnerL y v = ∑ i, inner ℝ (y i) (v i) := by
  simp [p4InnerL, ContinuousLinearMap.sum_apply]

theorem p4k_hasFDeriv_pot {k : Euc d → ℝ} (hk : Differentiable ℝ k) (hev : ∀ x, k (-x) = k x)
    (s : ℝ) (N : ℕ) (τ : ℝ) (Ξ : EucConfig d N) :
    HasFDerivAt (p4Pot k s N τ) (-(p4InnerL (p4Drift k s N τ Ξ))) Ξ := by
  have h1 := (p4k_pairSum_hasFDeriv hk Ξ).const_mul (aSelfSim s τ / (2 * N))
  have h2 : HasFDerivAt (fun Ξ : EucConfig d N => ∑ i, ‖Ξ i‖ ^ 2)
      (∑ i, (2 • (innerSL ℝ (Ξ i)).comp (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin N => Euc d) i))) Ξ :=
    HasFDerivAt.fun_sum fun i _ => (hasFDerivAt_apply i Ξ).norm_sq
  have h3 := h1.add (h2.const_mul (1 / 4 : ℝ))
  refine (show HasFDerivAt (p4Pot k s N τ) _ Ξ from h3).congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rw [p4k_pair_apply hk hev, p4k_p4InnerL_apply]
  have e : ∀ i, inner ℝ (p4Drift k s N τ Ξ i) (v i) =
      -((aSelfSim s τ / N) * inner ℝ (∑ j ∈ Finset.univ.erase i, gradient k (Ξ i - Ξ j)) (v i) +
        (1 / 2) * inner ℝ (Ξ i) (v i)) := fun i => by
    simp only [p4Drift, PiLp.neg_apply, inner_neg_left, inner_add_left, real_inner_smul_left]
  simp only [e, Finset.sum_neg_distrib, neg_neg, Finset.sum_add_distrib, ← Finset.mul_sum,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.proj_apply, innerSL_apply_apply, nsmul_eq_mul]
  have hc : aSelfSim s τ / (2 * N) * 2 = aSelfSim s τ / N := by
    rcases eq_or_ne (N : ℝ) 0 with h | h
    · simp [h]
    · field_simp
  rw [← hc]
  push_cast
  ring


/-! ### Consequences of `IsP4Kernel` -/

theorem p4k_bddAbove {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (hs : 0 ≤ s) :
    ∃ B : ℝ, ∀ x, k x ≤ B := by
  obtain ⟨hr0, -⟩ := hk.scale
  have hc : Continuous k := hk.smooth.continuous
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euc d) r₀).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C (max (-Real.log r₀) (r₀ ^ (-s))), fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ r₀
  · have := hC x (by simpa using hx)
    exact (le_of_abs_le (by simpa [Real.norm_eq_abs] using this)).trans (le_max_left _ _)
  · push_neg at hx
    rw [hk.eq_far x hx.le]
    unfold rieszKernel
    refine le_trans ?_ ((le_max_right _ _).trans' (le_refl _))
    by_cases h0 : s = 0
    · simp only [h0, ite_true]
      have := Real.log_le_log hr0 hx.le
      exact (by linarith : -Real.log ‖x‖ ≤ -Real.log r₀).trans (le_max_left _ _)
    · simp only [h0, ite_false]
      exact (Real.rpow_le_rpow_of_nonpos hr0 hx.le (by linarith)).trans (le_max_right _ _)

theorem p4k_grad_cont {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) :
    Continuous (gradient k) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp
    (hk.smooth.continuous_fderiv (by simp))

theorem p4k_aSelfSim_cont (s : ℝ) : Continuous (aSelfSim s) := by
  unfold aSelfSim
  fun_prop

theorem p4k_aSelfSim_pos (s τ : ℝ) : 0 < aSelfSim s τ := Real.exp_pos _

theorem p4k_aSelfSim_le_one {s : ℝ} (hs : 0 ≤ s) {τ : ℝ} (hτ : 0 ≤ τ) : aSelfSim s τ ≤ 1 := by
  unfold aSelfSim
  rw [Real.exp_le_one_iff]
  have : 0 ≤ s * τ := mul_nonneg hs hτ
  linarith

theorem p4k_cont_drift {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (N : ℕ) :
    Continuous (Function.uncurry (p4Drift k s N)) := by
  have hG := p4k_grad_cont hk
  have ha := p4k_aSelfSim_cont s
  refine continuous_pi fun i => ?_
  unfold p4Drift Function.uncurry
  simp only
  have hX : ∀ j : Fin N, Continuous fun p : ℝ × EucConfig d N => p.2 j :=
    fun j => (continuous_apply j).comp continuous_snd
  refine Continuous.neg (Continuous.add ?_ ?_)
  · refine Continuous.smul (Continuous.div_const (ha.comp continuous_fst) _) ?_
    refine continuous_finsetSum _ fun j _ => hG.comp ((hX i).sub (hX j))
  · exact (hX i).const_smul (1 / 2 : ℝ)

theorem p4k_cont_pot {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (N : ℕ) :
    Continuous (Function.uncurry (p4Pot k s N)) := by
  have hc := hk.smooth.continuous
  have ha := p4k_aSelfSim_cont s
  unfold p4Pot Function.uncurry
  simp only
  have hX : ∀ j : Fin N, Continuous fun p : ℝ × EucConfig d N => p.2 j :=
    fun j => (continuous_apply j).comp continuous_snd
  refine Continuous.add ?_ ?_
  · refine Continuous.mul (Continuous.div_const (ha.comp continuous_fst) _) ?_
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => hc.comp ((hX i).sub (hX j))
  · refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
    exact ((hX i).norm).pow 2


theorem p4k_drift_lip_gen {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (N : ℕ) (A : ℝ≥0) :
    ∃ K : ℝ≥0, ∀ τ : ℝ, aSelfSim s τ ≤ A → LipschitzWith K (p4Drift k s N τ) := by
  obtain ⟨L, hL⟩ := hk.lipGrad
  refine ⟨2 * L * A + 1, fun τ ha1 => ?_⟩
  have ha0 := p4k_aSelfSim_pos s τ
  refine LipschitzWith.of_dist_le_mul fun Ξ Ξ' => ?_
  have hδ : 0 ≤ dist Ξ Ξ' := dist_nonneg
  rw [dist_pi_le_iff (by positivity)]
  intro i
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos i
  -- pointwise bounds
  have hcoord : ∀ j, ‖(Ξ - Ξ') j‖ ≤ dist Ξ Ξ' := fun j => by
    rw [dist_eq_norm]; exact norm_le_pi_norm (Ξ - Ξ') j
  have hterm : ∀ j, ‖gradient k (Ξ i - Ξ j) - gradient k (Ξ' i - Ξ' j)‖ ≤ L * (2 * dist Ξ Ξ') := by
    intro j
    have h1 := hL.dist_le_mul (Ξ i - Ξ j) (Ξ' i - Ξ' j)
    rw [dist_eq_norm, dist_eq_norm] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ L.2)
    have e : Ξ i - Ξ j - (Ξ' i - Ξ' j) = (Ξ - Ξ') i - (Ξ - Ξ') j := by simp; abel
    rw [e]
    calc _ ≤ ‖(Ξ - Ξ') i‖ + ‖(Ξ - Ξ') j‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [hcoord i, hcoord j]
  have hsum : ‖∑ j ∈ Finset.univ.erase i, gradient k (Ξ i - Ξ j) -
      ∑ j ∈ Finset.univ.erase i, gradient k (Ξ' i - Ξ' j)‖ ≤ N * (L * (2 * dist Ξ Ξ')) := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have : ((Finset.univ.erase i).card : ℝ) ≤ N := by
      exact_mod_cast (Finset.card_erase_le).trans (by simp)
    exact this
  rw [dist_eq_norm]
  have e : p4Drift k s N τ Ξ i - p4Drift k s N τ Ξ' i =
      -((aSelfSim s τ / N) • (∑ j ∈ Finset.univ.erase i, gradient k (Ξ i - Ξ j) -
        ∑ j ∈ Finset.univ.erase i, gradient k (Ξ' i - Ξ' j)) + (1 / 2 : ℝ) • (Ξ i - Ξ' i)) := by
    simp only [p4Drift]
    simp only [smul_sub, neg_sub_neg]
    abel
  show ‖p4Drift k s N τ Ξ i - p4Drift k s N τ Ξ' i‖ ≤ _
  rw [e, norm_neg]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ aSelfSim s τ / N)]
  have h1 : aSelfSim s τ / N * ‖∑ j ∈ Finset.univ.erase i, gradient k (Ξ i - Ξ j) -
      ∑ j ∈ Finset.univ.erase i, gradient k (Ξ' i - Ξ' j)‖ ≤ (A : ℝ) * (L * (2 * dist Ξ Ξ')) := by
    calc _ ≤ aSelfSim s τ / N * (N * (L * (2 * dist Ξ Ξ'))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = aSelfSim s τ * (L * (2 * dist Ξ Ξ')) := by field_simp
      _ ≤ (A : ℝ) * (L * (2 * dist Ξ Ξ')) :=
          mul_le_mul_of_nonneg_right ha1 (by positivity)
  have h2 : |(1 / 2 : ℝ)| * ‖Ξ i - Ξ' i‖ ≤ 1 * dist Ξ Ξ' := by
    rw [abs_of_pos (by norm_num)]
    have := hcoord i
    simp only [Pi.sub_apply] at this
    linarith
  push_cast
  nlinarith

theorem p4k_drift_lip {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (hs : 0 ≤ s) (N : ℕ) :
    ∃ K : ℝ≥0, ∀ τ : ℝ, 0 ≤ τ → LipschitzWith K (p4Drift k s N τ) := by
  obtain ⟨K, hK⟩ := p4k_drift_lip_gen hk N 1
  exact ⟨K, fun τ hτ => hK τ (by simpa using p4k_aSelfSim_le_one hs hτ)⟩


/-! ### Pair sums -/

theorem p4k_sum_up {N : ℕ} (f : Fin N → Fin N → ℝ) {c : ℝ} (hc : 0 ≤ c) (hf : ∀ i j, f i j ≤ c) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, f i j ≤ N * N * c := by
  calc ∑ i, ∑ j ∈ Finset.univ.erase i, f i j ≤ ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, c :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hf i j
    _ ≤ ∑ i : Fin N, (N : ℝ) * c := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ hc
        exact_mod_cast (Finset.card_erase_le).trans (by simp)
    _ = N * N * c := by
        rw [Finset.sum_const, nsmul_eq_mul]; simp; ring

theorem p4k_sum_abs {N : ℕ} (f : Fin N → Fin N → ℝ) {c : ℝ} (hc : 0 ≤ c) (hf : ∀ i j, |f i j| ≤ c) :
    |∑ i, ∑ j ∈ Finset.univ.erase i, f i j| ≤ N * N * c := by
  rw [abs_le]
  constructor
  · have := p4k_sum_up (fun i j => -f i j) hc fun i j => by linarith [(abs_le.mp (hf i j)).1]
    simp only [Finset.sum_neg_distrib] at this
    linarith
  · exact p4k_sum_up f hc fun i j => (abs_le.mp (hf i j)).2

theorem p4k_k_abs {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) {B : ℝ} (hB : ∀ x, k x ≤ B)
    (y : Euc d) : |k y| ≤ |B| + ‖y‖ := by
  have hl := hk.lower y
  have h1 : Real.log (1 + ‖y‖) ≤ ‖y‖ := by
    have := Real.log_le_sub_one_of_pos (by linarith [norm_nonneg y] : 0 < 1 + ‖y‖)
    linarith
  rw [abs_le]
  constructor
  · linarith [abs_nonneg B]
  · linarith [hB y, le_abs_self B, norm_nonneg y]

theorem p4k_pair_abs {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) {B : ℝ} (hB : ∀ x, k x ≤ B)
    {N : ℕ} (Ξ : EucConfig d N) :
    |p4k_pairSum k N Ξ| ≤ N * N * ((|B| + 1) * (1 + ‖Ξ‖ ^ 2)) := by
  unfold p4k_pairSum
  refine p4k_sum_abs (fun i j => k (Ξ i - Ξ j)) (by positivity) fun i j => ?_
  refine (p4k_k_abs hk hB _).trans ?_
  have h2 : ‖Ξ i - Ξ j‖ ≤ 2 * ‖Ξ‖ := by
    calc ‖Ξ i - Ξ j‖ ≤ ‖Ξ i‖ + ‖Ξ j‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [norm_le_pi_norm Ξ i, norm_le_pi_norm Ξ j]
  nlinarith [abs_nonneg B, sq_nonneg (‖Ξ‖ - 1), sq_nonneg ‖Ξ‖, norm_nonneg Ξ]

theorem p4k_pair_lower {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k)
    {N : ℕ} (Ξ : EucConfig d N) :
    -((N : ℝ) * N * (2 * ‖Ξ‖)) ≤ p4k_pairSum k N Ξ := by
  unfold p4k_pairSum
  have := p4k_sum_up (fun i j => -k (Ξ i - Ξ j)) (by positivity : 0 ≤ 2 * ‖Ξ‖) fun i j => by
    have h2 : ‖Ξ i - Ξ j‖ ≤ 2 * ‖Ξ‖ := by
      calc ‖Ξ i - Ξ j‖ ≤ ‖Ξ i‖ + ‖Ξ j‖ := norm_sub_le _ _
        _ ≤ _ := by linarith [norm_le_pi_norm Ξ i, norm_le_pi_norm Ξ j]
    have h1 : Real.log (1 + ‖Ξ i - Ξ j‖) ≤ ‖Ξ i - Ξ j‖ := by
      have := Real.log_le_sub_one_of_pos (by linarith [norm_nonneg (Ξ i - Ξ j)] : 0 < 1 + ‖Ξ i - Ξ j‖)
      linarith
    have := hk.lower (Ξ i - Ξ j)
    linarith
  simp only [Finset.sum_neg_distrib] at this
  linarith

theorem p4k_pair_nonneg {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (hs : 0 < s)
    {N : ℕ} (Ξ : EucConfig d N) : 0 ≤ p4k_pairSum k N Ξ := by
  unfold p4k_pairSum
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hk.nonneg hs _


/-! ### Time derivative, confinement, assembly of `P4PotHyp` -/

/-- The time derivative of the potential. -/
def p4k_dV (k : Euc d → ℝ) (s : ℝ) (N : ℕ) (τ : ℝ) (Ξ : EucConfig d N) : ℝ :=
  -(s / 2) * (aSelfSim s τ / (2 * N)) * p4k_pairSum k N Ξ

theorem p4k_hasDeriv_time (k : Euc d → ℝ) (s : ℝ) (N : ℕ) (τ : ℝ) (Ξ : EucConfig d N) :
    HasDerivAt (fun σ => p4Pot k s N σ Ξ) (p4k_dV k s N τ Ξ) τ := by
  have h1 : HasDerivAt (fun σ : ℝ => -s * σ / 2) (-s * 1 / 2) τ :=
    ((hasDerivAt_id τ).const_mul (-s)).div_const 2
  have hA : HasDerivAt (aSelfSim s) (aSelfSim s τ * (-s * 1 / 2)) τ := by
    unfold aSelfSim; exact h1.exp
  have h2 := (((hA.div_const (2 * (N : ℝ))).mul_const (p4k_pairSum k N Ξ)).add_const
    ((1 / 4 : ℝ) * ∑ i, ‖Ξ i‖ ^ 2))
  refine (show HasDerivAt (fun σ => p4Pot k s N σ Ξ) _ τ from h2).congr_deriv ?_
  unfold p4k_dV
  ring

theorem p4k_dV_cont {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (N : ℕ) :
    Continuous (Function.uncurry (p4k_dV k s N)) := by
  have hc := hk.smooth.continuous
  have ha := p4k_aSelfSim_cont s
  unfold p4k_dV p4k_pairSum Function.uncurry
  simp only
  have hX : ∀ j : Fin N, Continuous fun p : ℝ × EucConfig d N => p.2 j :=
    fun j => (continuous_apply j).comp continuous_snd
  refine Continuous.mul (Continuous.mul continuous_const
    (Continuous.div_const (ha.comp continuous_fst) _)) ?_
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => hc.comp ((hX i).sub (hX j))

theorem p4k_dV_nonpos {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (hs : 0 ≤ s) (N : ℕ)
    (τ : ℝ) (Ξ : EucConfig d N) : p4k_dV k s N τ Ξ ≤ 0 := by
  unfold p4k_dV
  rcases hs.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have h1 := p4k_pair_nonneg hk hpos Ξ
    have h2 := p4k_aSelfSim_pos s τ
    have : 0 ≤ (s / 2) * (aSelfSim s τ / (2 * N)) * p4k_pairSum k N Ξ := by positivity
    linarith

theorem p4k_dV_bound {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (hs : 0 ≤ s) (N : ℕ) :
    ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ → ∀ Ξ : EucConfig d N, |p4k_dV k s N τ Ξ| ≤ C * (1 + ‖Ξ‖ ^ 2) := by
  obtain ⟨B, hB⟩ := p4k_bddAbove hk hs
  refine ⟨(s / 2) * (N / 2) * (|B| + 1), fun τ hτ Ξ => ?_⟩
  have ha1 := p4k_aSelfSim_le_one hs hτ
  have ha0 := p4k_aSelfSim_pos s τ
  have hP := p4k_pair_abs hk hB Ξ
  unfold p4k_dV
  rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ s / 2),
    abs_of_nonneg (by positivity : 0 ≤ aSelfSim s τ / (2 * N))]
  have hcN : aSelfSim s τ / (2 * N) * ((N : ℝ) * N) ≤ N / 2 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · have hN : (0 : ℝ) < N := by exact_mod_cast h
      have : aSelfSim s τ / (2 * N) * ((N : ℝ) * N) = aSelfSim s τ * N / 2 := by field_simp
      rw [this]
      nlinarith
  have hM : 0 ≤ (|B| + 1) * (1 + ‖Ξ‖ ^ 2) := by positivity
  calc s / 2 * (aSelfSim s τ / (2 * N)) * |p4k_pairSum k N Ξ|
      ≤ s / 2 * (aSelfSim s τ / (2 * N)) * ((N : ℝ) * N * ((|B| + 1) * (1 + ‖Ξ‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left hP (by positivity)
    _ = s / 2 * (aSelfSim s τ / (2 * N) * ((N : ℝ) * N)) * ((|B| + 1) * (1 + ‖Ξ‖ ^ 2)) := by ring
    _ ≤ s / 2 * (N / 2) * ((|B| + 1) * (1 + ‖Ξ‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_right ?_ hM
        exact mul_le_mul_of_nonneg_left hcN (by positivity)
    _ = _ := by ring

theorem p4k_conf_gen {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (N : ℕ)
    (τ : ℝ) (Ξ : EucConfig d N) :
    (1 / 8 : ℝ) * ‖Ξ‖ ^ 2 - 2 * (aSelfSim s τ * N) ^ 2 ≤ p4Pot k s N τ Ξ := by
  have ha0 := p4k_aSelfSim_pos s τ
  have hP := p4k_pair_lower hk Ξ
  have hcN : aSelfSim s τ / (2 * N) * ((N : ℝ) * N) ≤ aSelfSim s τ * N / 2 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · have hN : (0 : ℝ) < N := by exact_mod_cast h
      have : aSelfSim s τ / (2 * N) * ((N : ℝ) * N) = aSelfSim s τ * N / 2 := by field_simp
      rw [this]
  have hc0 : 0 ≤ aSelfSim s τ / (2 * N) := by positivity
  have h1 : aSelfSim s τ / (2 * N) * (-((N : ℝ) * N * (2 * ‖Ξ‖))) ≤
      aSelfSim s τ / (2 * N) * p4k_pairSum k N Ξ := mul_le_mul_of_nonneg_left hP hc0
  have h2 : -(aSelfSim s τ * N * ‖Ξ‖) ≤ aSelfSim s τ / (2 * N) * (-((N : ℝ) * N * (2 * ‖Ξ‖))) := by
    have : aSelfSim s τ / (2 * N) * (-((N : ℝ) * N * (2 * ‖Ξ‖))) =
        -(2 * ‖Ξ‖ * (aSelfSim s τ / (2 * N) * ((N : ℝ) * N))) := by ring
    rw [this]
    nlinarith [norm_nonneg Ξ]
  have h3 : ‖Ξ‖ ^ 2 ≤ ∑ i, ‖Ξ i‖ ^ 2 := by
    have hr : 0 ≤ Real.sqrt (∑ i, ‖Ξ i‖ ^ 2) := Real.sqrt_nonneg _
    have : ‖Ξ‖ ≤ Real.sqrt (∑ i, ‖Ξ i‖ ^ 2) := by
      rw [pi_norm_le_iff_of_nonneg hr]
      intro i
      refine Real.le_sqrt_of_sq_le ?_
      exact Finset.single_le_sum (f := fun i => ‖Ξ i‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
    calc ‖Ξ‖ ^ 2 ≤ (Real.sqrt (∑ i, ‖Ξ i‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
  have e : p4Pot k s N τ Ξ = aSelfSim s τ / (2 * N) * p4k_pairSum k N Ξ +
      (1 / 4) * ∑ i, ‖Ξ i‖ ^ 2 := rfl
  rw [e]
  nlinarith [sq_nonneg (‖Ξ‖ - 4 * (aSelfSim s τ * N))]

theorem p4k_conf {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (hs : 0 ≤ s) (N : ℕ)
    (τ : ℝ) (hτ : 0 ≤ τ) (Ξ : EucConfig d N) :
    (1 / 8 : ℝ) * ‖Ξ‖ ^ 2 - 2 * (N : ℝ) ^ 2 ≤ p4Pot k s N τ Ξ := by
  have h := p4k_conf_gen hk N τ Ξ
  have ha1 := p4k_aSelfSim_le_one hs hτ
  have ha0 := p4k_aSelfSim_pos s τ
  have : (aSelfSim s τ * N) ^ 2 ≤ (N : ℝ) ^ 2 := by
    have : aSelfSim s τ * N ≤ N := by nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact pow_le_pow_left₀ (by positivity) this 2
  linarith

theorem p4k_potHyp {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) (hs : 0 ≤ s) (N : ℕ)
    (T : ℝ) (hT : 0 ≤ T) : P4PotHyp (p4Pot k s N) (p4Drift k s N) T where
  grad := fun τ x => p4k_hasFDeriv_pot (hk.smooth.differentiable (by simp)) hk.even s N τ x
  cont_b := p4k_cont_drift hk N
  lip := by
    obtain ⟨K, hK⟩ := p4k_drift_lip hk hs N
    exact ⟨K, fun τ hτ => hK τ hτ.1⟩
  cont_V := p4k_cont_pot hk N
  dtime := by
    obtain ⟨C, hC⟩ := p4k_dV_bound hk hs N
    exact ⟨p4k_dV k s N, p4k_dV_cont hk N, fun τ x => p4k_hasDeriv_time k s N τ x,
      fun τ _ x => p4k_dV_nonpos hk hs N τ x, C, fun τ hτ x => hC τ hτ.1 x⟩
  conf := ⟨1 / 8, 2 * (N : ℝ) ^ 2, by norm_num, fun τ hτ x => p4k_conf hk hs N τ hτ.1 x⟩

theorem p4_kernel_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (N : ℕ) :
    ∃ gM : ℕ → Euc d → ℝ, ∀ M : ℕ, IsP4Kernel d s (1 / ((M : ℝ) + 1)) (gM M) ∧
      ∀ T : ℝ, 0 ≤ T → P4PotHyp (p4Pot (gM M) s N) (p4Drift (gM M) s N) T := by
  refine ⟨fun M x => p4k_h s ((1 / ((M : ℝ) + 1)) ^ 2) (‖x‖ ^ 2), fun M => ?_⟩
  have hr0 : 0 < 1 / ((M : ℝ) + 1) := by positivity
  have hr1 : 1 / ((M : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hk := p4k_isKernel d s hs0 hr0 hr1
  exact ⟨hk, fun T hT => p4k_potHyp hk hs0 N T hT⟩

example := (@p4_kernel_proof : type_of% @HRS.MP.SelfSimP4.p4_kernel)

end HRS.MP.SelfSimP4Impl
