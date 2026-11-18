import HRS.MS.MfeConfAux103
import HRS.MP.SelfSimP4Kern

/-!
# S.B.1, packet F9 (part 7): radial force bound of the concrete truncated kernels (R01 of the Pro note SB1-Regularization)

For the family `k_r(x) = h_{s,r²}(|x|²)`, `h = ψ_s ∘ q_a`, of `p4k_isKernel`: `|x| |∇k_r(x)| ≤ A (k_r(x) + log(1+|x|) + 1)` with `A`
independent of `r ∈ (0,1]` (`sb1_p4k_grad_bound`), because `q_a' = σ(v) + σ'(v)(v-1)` is bounded independently of `a`
(`sb1_q_deriv`) and `t ≤ q_a(t)`.  Consequences: the pointwise power bound `|∇k_r(z)| ≤ A |z|^{-s-1}` (`sb1_p4k_grad_pow`).
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

/-- the derivative of the profile `q_a` -/
theorem sb1_q_hasDeriv {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (p4k_q a) (Real.smoothTransition (2 * t / a) +
      deriv Real.smoothTransition (2 * t / a) * (2 * t / a - 1)) t := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * t / a) (2 / a) t := by
    have := ((hasDerivAt_id t).const_mul (2 : ℝ)).div_const a
    convert this using 1 <;> simp
  have h2 := ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) (2 * t / a)).hasDerivAt.comp t h1
  have h3 := (((h2.const_sub 1).mul_const (a / 2)).add (h2.mul (hasDerivAt_id t)))
  have hfun : p4k_q a = (fun y => (1 - (Real.smoothTransition ∘ fun t : ℝ => 2 * t / a) y) * (a / 2)) +
      (Real.smoothTransition ∘ fun t : ℝ => 2 * t / a) * id := rfl
  rw [hfun]
  refine h3.congr_deriv ?_
  simp only [Function.comp, id]
  field_simp
  ring

theorem sb1_q_deriv_bound : ∃ Aq : ℝ, 0 ≤ Aq ∧ ∀ {a : ℝ}, 0 < a → ∀ t : ℝ, |deriv (p4k_q a) t| ≤ Aq := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2.continuous
  obtain ⟨S', hS'⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  have hS'0 : 0 ≤ S' := (norm_nonneg _).trans (hS' 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨1 + S', by positivity, fun {a} ha t => ?_⟩
  rw [(sb1_q_hasDeriv ha t).deriv]
  set v := 2 * t / a with hv
  have hσ0 := Real.smoothTransition.nonneg v
  have hσ1 := Real.smoothTransition.le_one v
  by_cases hv0 : v ≤ 0
  · have hz : Real.smoothTransition v = 0 := Real.smoothTransition.zero_of_nonpos hv0
    have hd : deriv Real.smoothTransition v = 0 := by
      rcases hv0.lt_or_eq with h | h
      · have : Real.smoothTransition =ᶠ[𝓝 v] fun _ => 0 := by
          filter_upwards [Iio_mem_nhds h] with u hu using Real.smoothTransition.zero_of_nonpos hu.le
        rw [this.deriv_eq]; simp
      · have h' : deriv Real.smoothTransition v = 0 := by
          have := hS' 0 ⟨le_rfl, zero_le_one⟩
          -- derivative vanishes at the left endpoint by continuity of the derivative
          have hlim : Tendsto (deriv Real.smoothTransition) (𝓝[<] 0) (𝓝 (deriv Real.smoothTransition 0)) :=
            (hc.tendsto 0).mono_left nhdsWithin_le_nhds
          have hlim0 : Tendsto (deriv Real.smoothTransition) (𝓝[<] 0) (𝓝 0) := by
            refine tendsto_const_nhds.congr' ?_
            filter_upwards [self_mem_nhdsWithin] with u hu
            have : Real.smoothTransition =ᶠ[𝓝 u] fun _ => 0 := by
              filter_upwards [Iio_mem_nhds (Set.mem_Iio.1 hu)] with w hw
                using Real.smoothTransition.zero_of_nonpos hw.le
            rw [this.deriv_eq]; simp
          rw [h]
          exact tendsto_nhds_unique hlim hlim0
        exact h'
    rw [hz, hd]; simp; linarith
  · push Not at hv0
    by_cases hv1 : 1 < v
    · have ho : Real.smoothTransition v = 1 := Real.smoothTransition.one_of_one_le hv1.le
      have hd : deriv Real.smoothTransition v = 0 := by
        have : Real.smoothTransition =ᶠ[𝓝 v] fun _ => 1 := by
          filter_upwards [Ioi_mem_nhds hv1] with u hu using Real.smoothTransition.one_of_one_le hu.le
        rw [this.deriv_eq]; simp
      rw [ho, hd]; simp; linarith
    · push Not at hv1
      have hb := hS' v ⟨hv0.le, hv1⟩
      rw [Real.norm_eq_abs] at hb
      have hvm : |v - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      calc |Real.smoothTransition v + deriv Real.smoothTransition v * (v - 1)|
          ≤ |Real.smoothTransition v| + |deriv Real.smoothTransition v * (v - 1)| := abs_add_le _ _
        _ ≤ 1 + S' * 1 := by
            rw [abs_of_nonneg hσ0, abs_mul]
            exact add_le_add hσ1 (mul_le_mul hb hvm (abs_nonneg _) hS'0)
        _ = 1 + S' := by ring

theorem sb1_p4k_grad_bound (d : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ x : Euc d,
      ‖x‖ * ‖gradient (fun x : Euc d => p4k_h s (r ^ 2) (‖x‖ ^ 2)) x‖ ≤
        A * (if s = 0 then 1 else p4k_h s (r ^ 2) (‖x‖ ^ 2)) := by
  obtain ⟨Aq, hAq0, hAq⟩ := sb1_q_deriv_bound
  refine ⟨(s + 1) * Aq, by positivity, fun r hr hr1 x => ?_⟩
  have ha : 0 < r ^ 2 := by positivity
  have hker := p4k_isKernel d s hs hr hr1
  have hlow := hker.lower x
  have hlog : 0 ≤ Real.log (1 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
  set a := r ^ 2 with hadef
  set t := ‖x‖ ^ 2 with ht
  have hh := p4k_h_contDiff s ha
  have hgrad := (p4k_radial_grad d _ hh x).gradient
  have hq := p4k_q_pos ha t
  have hqt := p4k_q_ge ha t
  have ht0 : 0 ≤ t := sq_nonneg _
  have hder : deriv (p4k_h s a) t = p4k_psi1 s (p4k_q a t) * deriv (p4k_q a) t := by
    have h1 := (p4k_psi_hasDeriv s hq).comp t (sb1_q_hasDeriv ha t)
    have h2 : HasDerivAt (p4k_h s a) _ t := h1
    rw [h2.deriv, (sb1_q_hasDeriv ha t).deriv]
  have hq' := hAq ha t
  rw [hgrad, norm_smul, Real.norm_eq_abs, hder]
  have hx2 : ‖x‖ * (|2 * (p4k_psi1 s (p4k_q a t) * deriv (p4k_q a) t)| * ‖x‖) =
      2 * t * (|p4k_psi1 s (p4k_q a t)| * |deriv (p4k_q a) t|) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), ht]
    ring
  rw [hx2]
  have hhx : p4k_h s a t = p4k_psi s (p4k_q a t) := rfl
  rw [hhx]
  have htq : t * (p4k_q a t)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]; exact (div_le_one hq).2 hqt
  have htq0 : 0 ≤ t * (p4k_q a t)⁻¹ := mul_nonneg ht0 (inv_pos.2 hq).le
  have hy0 : 0 ≤ |deriv (p4k_q a) t| := abs_nonneg _
  by_cases h0 : s = 0
  · have e1 : p4k_psi1 s (p4k_q a t) = -(1 / 2) * (p4k_q a t)⁻¹ := by simp [p4k_psi1, h0]
    have e2 : p4k_psi s (p4k_q a t) = -(1 / 2) * Real.log (p4k_q a t) := by simp [p4k_psi, h0]
    have e3 : |p4k_psi1 s (p4k_q a t)| = (1 / 2) * (p4k_q a t)⁻¹ := by
      rw [e1, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_pos (inv_pos.2 hq)]
    rw [e3, e2]
    have e4 : 2 * t * ((1 / 2 * (p4k_q a t)⁻¹) * |deriv (p4k_q a) t|) = (t * (p4k_q a t)⁻¹) * |deriv (p4k_q a) t| := by ring
    rw [e4]
    have h5 : (t * (p4k_q a t)⁻¹) * |deriv (p4k_q a) t| ≤ Aq :=
      calc _ ≤ 1 * |deriv (p4k_q a) t| := mul_le_mul_of_nonneg_right htq hy0
        _ ≤ Aq := by linarith
    rw [h0]
    simp only [if_true]
    nlinarith
  · have hs' : 0 < s := lt_of_le_of_ne hs (Ne.symm h0)
    have e1 : p4k_psi1 s (p4k_q a t) = (-s / 2) * (p4k_q a t) ^ (-s / 2 - 1) := by simp [p4k_psi1, h0]
    have e2 : p4k_psi s (p4k_q a t) = (p4k_q a t) ^ (-s / 2) := by simp [p4k_psi, h0]
    have hqs : 0 ≤ (p4k_q a t) ^ (-s / 2) := Real.rpow_nonneg hq.le _
    have e3 : |p4k_psi1 s (p4k_q a t)| = (s / 2) * ((p4k_q a t) ^ (-s / 2) * (p4k_q a t)⁻¹) := by
      rw [e1, abs_mul, abs_of_neg (by linarith : -s / 2 < 0), abs_of_pos (Real.rpow_pos_of_pos hq _),
        Real.rpow_sub_one hq.ne', div_eq_mul_inv]
      ring
    rw [e3, e2]
    have e4 : 2 * t * ((s / 2 * ((p4k_q a t) ^ (-s / 2) * (p4k_q a t)⁻¹)) * |deriv (p4k_q a) t|) =
        s * (p4k_q a t) ^ (-s / 2) * ((t * (p4k_q a t)⁻¹) * |deriv (p4k_q a) t|) := by ring
    rw [e4]
    have h5 : (t * (p4k_q a t)⁻¹) * |deriv (p4k_q a) t| ≤ Aq :=
      calc _ ≤ 1 * |deriv (p4k_q a) t| := mul_le_mul_of_nonneg_right htq hy0
        _ ≤ Aq := by linarith
    have h5' : 0 ≤ (t * (p4k_q a t)⁻¹) * |deriv (p4k_q a) t| := mul_nonneg htq0 hy0
    have h6 : s * (p4k_q a t) ^ (-s / 2) * ((t * (p4k_q a t)⁻¹) * |deriv (p4k_q a) t|) ≤
        s * (p4k_q a t) ^ (-s / 2) * Aq :=
      mul_le_mul_of_nonneg_left h5 (mul_nonneg hs'.le hqs)
    simp only [h0, if_false]
    nlinarith [mul_nonneg hAq0 hqs]

end HRS.MS.MfeConf
