import HRS.Equilibrium.Parametrix.PX3aAuxAA

/-!
# Packet PX4a auxiliaries A: local kernels of order `s` and their near/far splitting

`LocKer d s k`: `k` is smooth off `0`, supported in `‖v‖ < 1/64`, with `‖D^n k(v)‖ ≲ ‖v‖^{-(s+n)}`
(`0 < s < d`).  The splitting `k = kN ρ + kF ρ` (`kN = ζ_ρ k` integrable, `kF = (1-ζ_ρ) k` smooth
with compact support and derivative bounds `‖D^n kF(y)‖ ≲ ‖y‖^{-(s+n)}` on `‖y‖ ≥ ρ/2`) is the
analogue of `Ln`, `Lf` of the Newton potential (PX3a).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Hypotheses on a local kernel of order `s`. -/
structure LocKer (d : ℕ) (s : ℝ) (k : Euc d → ℝ) : Prop where
  s_pos : 0 < s
  s_lt : s < d
  smooth : ContDiffOn ℝ ∞' k {0}ᶜ
  supp : ∀ v : Euc d, 1 / 64 ≤ ‖v‖ → k v = 0
  bound : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Euc d, v ≠ 0 →
    ‖iteratedFDeriv ℝ n k v‖ ≤ C * ‖v‖ ^ (-(s + n))

/-- Near part `ζ_ρ k`. -/
def kN (k : Euc d → ℝ) (ρ : ℝ) (y : Euc d) : ℝ := px3a_zeta d ρ y * k y

/-- Far part `(1 - ζ_ρ) k`. -/
def kF (k : Euc d → ℝ) (ρ : ℝ) (y : Euc d) : ℝ := (1 - px3a_zeta d ρ y) * k y

/-- A globally smooth kernel agreeing with `k` for `‖y‖ ≥ ρ/4`. -/
def kH (k : Euc d → ℝ) (ρ : ℝ) (y : Euc d) : ℝ := (1 - px3a_zeta d (ρ / 4) y) * k y

lemma kN_add_kF (k : Euc d → ℝ) (ρ : ℝ) (y : Euc d) : kN k ρ y + kF k ρ y = k y := by
  unfold kN kF; ring

lemma kF_eq {ρ : ℝ} (hρ : 0 < ρ) (k : Euc d → ℝ) (y : Euc d) :
    kF k ρ y = (1 - px3a_zeta d ρ y) * kH k ρ y := by
  unfold kF kH
  rcases le_or_gt ‖y‖ (ρ / 2) with h | h
  · rw [px3a_zeta_eq_one hρ h]; ring
  · rw [px3a_zeta_eq_zero (by linarith : ρ / 4 > 0) (by linarith)]; ring

lemma kH_eq_of_le {ρ : ℝ} (hρ : 0 < ρ) (k : Euc d → ℝ) {y : Euc d} (hy : ρ / 4 ≤ ‖y‖) :
    kH k ρ y = k y := by
  unfold kH
  rw [px3a_zeta_eq_zero (by linarith : ρ / 4 > 0) hy]; ring

namespace LocKer

variable {s : ℝ} {k : Euc d → ℝ}

lemma measurable (h : LocKer d s k) : Measurable k :=
  measurable_of_continuousOn_compl_singleton 0 h.smooth.continuousOn

lemma kH_contDiff (h : LocKer d s k) {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ∞) : ContDiff ℝ n (kH k ρ) := by
  have h2 := contDiff_mul_of_tsupport (E := Euc d) isOpen_compl_singleton
    ((contDiff_const.sub (px3a_zeta_contDiff (d := d) (ρ / 4) n)))
    (h.smooth.of_le (by exact_mod_cast le_top)) (tsupport_one_sub_zeta_subset hρ)
  exact h2

lemma kF_contDiff (h : LocKer d s k) {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ∞) : ContDiff ℝ n (kF k ρ) := by
  have : kF k ρ = fun y => (1 - px3a_zeta d ρ y) * kH k ρ y := by
    funext y; exact kF_eq hρ k y
  rw [this]
  exact (contDiff_const.sub (px3a_zeta_contDiff ρ n)).mul (h.kH_contDiff hρ n)

lemma kF_hasCompactSupport (h : LocKer d s k) (ρ : ℝ) : HasCompactSupport (kF k ρ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (1 / 64)) (fun y hy => ?_)
  have : 1 / 64 ≤ ‖y‖ := by simpa using (by simpa using hy : 1 / 64 < ‖y‖).le
  simp [kF, h.supp y this]

lemma kF_measurable (h : LocKer d s k) {ρ : ℝ} (hρ : 0 < ρ) : Measurable (kF k ρ) :=
  (h.kF_contDiff hρ 0).continuous.measurable

lemma kN_measurable (h : LocKer d s k) (ρ : ℝ) : Measurable (kN k ρ) :=
  ((px3a_zeta_contDiff (d := d) ρ 0).continuous.measurable).mul h.measurable

lemma kF_bdd (h : LocKer d s k) {ρ : ℝ} (hρ : 0 < ρ) : ∃ C : ℝ, ∀ y, ‖kF k ρ y‖ ≤ C :=
  (h.kF_contDiff hρ 0).continuous.bounded_above_of_compact_support (h.kF_hasCompactSupport ρ)

lemma kN_eq_zero {ρ : ℝ} (hρ : 0 < ρ) {y : Euc d} (hy : ρ ≤ ‖y‖) : kN k ρ y = 0 := by
  simp [kN, px3a_zeta_eq_zero hρ hy]

lemma norm_kN_le (h : LocKer d s k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ) (y : Euc d), y ≠ 0 → ‖kN k ρ y‖ ≤ C * ‖y‖ ^ (-s) := by
  obtain ⟨C, hC0, hC⟩ := h.bound 0
  refine ⟨C, hC0, fun ρ y hy => ?_⟩
  have := hC y hy
  rw [norm_iteratedFDeriv_zero] at this
  simp only [Nat.cast_zero, add_zero] at this
  calc ‖kN k ρ y‖ = px3a_zeta d ρ y * ‖k y‖ := by
        simp only [kN, norm_mul, Real.norm_of_nonneg (px3a_zeta_nonneg ρ y)]
    _ ≤ 1 * ‖k y‖ := by gcongr; exact px3a_zeta_le_one ρ y
    _ ≤ _ := by rw [one_mul]; exact this

lemma kN_integrable (hd : 1 ≤ d) (h : LocKer d s k) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Integrable (kN k ρ) := by
  obtain ⟨C, hC0, hC⟩ := h.norm_kN_le
  have hsupp : Function.support (kN k ρ) ⊆ Metric.ball (0 : Euc d) ρ := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right]
    by_contra hh
    exact hy (kN_eq_zero hρ (not_lt.mp hh))
  rw [← integrableOn_iff_integrable_of_support_subset hsupp]
  have hb : IntegrableOn (fun w : Euc d => C * (‖w‖ ^ (-s) * (1 + |Real.log ‖w‖|) ^ 0))
      (Metric.ball (0 : Euc d) ρ) :=
    (integrableOn_rpow_log hd h.s_lt 0 hρ1).const_mul C
  refine hb.mono' (h.kN_measurable ρ).aestronglyMeasurable ?_
  have hae := ae_restrict_of_ae (μ := (volume : Measure (Euc d))) (s := Metric.ball (0 : Euc d) ρ)
    (ae_ne_zero_euc (d := d) hd)
  filter_upwards [hae] with w hw0
  simpa using hC ρ w hw0

lemma kF_zero_of_lt {ρ : ℝ} (hρ : 0 < ρ) (k : Euc d → ℝ) {y : Euc d} (hy : ‖y‖ < ρ / 2) (j : ℕ) :
    iteratedFDeriv ℝ j (kF k ρ) y = 0 := by
  have : kF k ρ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy] with u hu
    have hu' : ‖u‖ < ρ / 2 := hu
    simp [kF, px3a_zeta_eq_one hρ hu'.le]
  rw [(this.iteratedFDeriv ℝ j).eq_of_nhds]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · ext v; simp [iteratedFDeriv_zero_eq_comp]
  · have := iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := Euc d) (by omega : j ≠ 0) (0 : ℝ)
    exact congrFun this y

set_option maxHeartbeats 1600000 in
/-- Derivative bounds of the far kernel on `‖y‖ ≥ ρ/2`. -/
lemma kF_bound_aux (h : LocKer d s k) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ∀ y : Euc d, ρ / 2 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ n (kF k ρ) y‖ ≤ C * ‖y‖ ^ (-(s + n)) := by
  obtain ⟨S, hS0, hS⟩ := px3a_zeta_deriv_bound (d := d) n
  have hM : ∀ j, ∃ M : ℝ, 0 ≤ M ∧ ∀ v : Euc d, v ≠ 0 →
      ‖iteratedFDeriv ℝ j k v‖ ≤ M * ‖v‖ ^ (-(s + j)) := fun j => h.bound j
  choose M hM0 hMb using hM
  set Mm : ℝ := ∑ j ∈ Finset.range (n + 1), M j with hMm
  have hMm0 : 0 ≤ Mm := Finset.sum_nonneg fun j _ => hM0 j
  have hMle : ∀ j ≤ n, M j ≤ Mm := fun j hj =>
    Finset.single_le_sum (f := M) (fun i _ => hM0 i) (Finset.mem_range.mpr (by omega))
  refine ⟨2 ^ n * ((1 + S) * Mm), by positivity, fun ρ hρ y hy1 => ?_⟩
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le (by positivity) hy1
  have hyne : y ≠ 0 := norm_pos_iff.mp hy0
  set e : ℝ := -(s + n) with he
  have hkF : kF k ρ = fun y => (1 - px3a_zeta d ρ y) * kH k ρ y := by
    funext y; exact kF_eq hρ k y
  have hf1 : ContDiff ℝ ∞' (fun y : Euc d => 1 - px3a_zeta d ρ y) :=
    contDiff_const.sub (px3a_zeta_contDiff ρ _)
  have hL : ContDiff ℝ ∞' (kH k ρ) := h.kH_contDiff hρ _
  rw [hkF]
  refine (norm_iteratedFDeriv_mul_le (N := ∞') hf1 hL y (by exact_mod_cast le_top)).trans ?_
  have hHk : ∀ j, ‖iteratedFDeriv ℝ j (kH k ρ) y‖ ≤ M j * ‖y‖ ^ (-(s + j)) := by
    intro j
    have hev : kH k ρ =ᶠ[𝓝 y] k := by
      filter_upwards [(isOpen_lt (continuous_const : Continuous fun _ : Euc d => ρ / 4)
        continuous_norm).mem_nhds (by linarith : ρ / 4 < ‖y‖)] with u hu
      exact kH_eq_of_le hρ k (le_of_lt hu)
    rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]
    exact hMb j y hyne
  have hterm : ∀ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (fun y : Euc d => 1 - px3a_zeta d ρ y) y‖ *
        ‖iteratedFDeriv ℝ (n - i) (kH k ρ) y‖ ≤ (n.choose i : ℝ) * ((1 + S) * Mm * ‖y‖ ^ e) := by
    intro i hi
    have hij : i ≤ n := by have := Finset.mem_range.mp hi; omega
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hyr : 0 ≤ ‖y‖ ^ e := Real.rpow_nonneg (norm_nonneg _) _
    have hHk' := hHk (n - i)
    have hHk0 : 0 ≤ ‖iteratedFDeriv ℝ (n - i) (kH k ρ) y‖ := norm_nonneg _
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, LinearIsometryEquiv.norm_map]
      have h1 : ‖(1 : ℝ) - px3a_zeta d ρ y‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [px3a_zeta_le_one ρ y])]
        linarith [px3a_zeta_nonneg ρ y]
      have hnn : (n - 0 : ℕ) = n := by omega
      rw [hnn] at hHk'
      calc ‖(1 : ℝ) - px3a_zeta d ρ y‖ * ‖iteratedFDeriv ℝ n (kH k ρ) y‖
          ≤ 1 * (M n * ‖y‖ ^ (-(s + (n : ℝ)))) :=
            mul_le_mul h1 (by simpa using hHk') (norm_nonneg _) zero_le_one
        _ ≤ (1 + S) * Mm * ‖y‖ ^ e := by
            have := hMle n le_rfl
            have h2 : M n * ‖y‖ ^ (-(s + (n : ℝ))) ≤ Mm * ‖y‖ ^ e :=
              mul_le_mul_of_nonneg_right this hyr
            nlinarith [mul_nonneg hS0 (mul_nonneg hMm0 hyr)]
    · have hnorm : ‖iteratedFDeriv ℝ i (fun y => 1 - px3a_zeta d ρ y) y‖ =
          ‖iteratedFDeriv ℝ i (px3a_zeta d ρ) y‖ :=
        norm_iteratedFDeriv_one_sub (px3a_zeta_contDiff ρ _) hipos y
      rw [hnorm]
      by_cases hyρ : ρ < ‖y‖
      · rw [iteratedFDeriv_zeta_eq_zero_of_gt hρ hipos hyρ, norm_zero, zero_mul]
        positivity
      · have hyρ' : ‖y‖ ≤ ρ := not_lt.mp hyρ
        have hS1 : ‖iteratedFDeriv ℝ i (px3a_zeta d ρ) y‖ ≤ S * (ρ⁻¹) ^ i := hS ρ hρ i hij y
        have hρi : (ρ⁻¹) ^ i ≤ (‖y‖⁻¹) ^ i :=
          pow_le_pow_left₀ (by positivity) (inv_anti₀ hy0 hyρ') i
        have hyi : (‖y‖⁻¹) ^ i = ‖y‖ ^ (-(i : ℝ)) := by
          rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, inv_pow]
        have hMi : M (n - i) ≤ Mm := hMle _ (by omega)
        have hexp : ‖y‖ ^ (-(i : ℝ)) * ‖y‖ ^ (-(s + ((n - i : ℕ) : ℝ))) = ‖y‖ ^ e := by
          rw [← Real.rpow_add hy0]; congr 1; rw [he]; push_cast [Nat.cast_sub hij]; ring
        calc ‖iteratedFDeriv ℝ i (px3a_zeta d ρ) y‖ * ‖iteratedFDeriv ℝ (n - i) (kH k ρ) y‖
            ≤ (S * ‖y‖ ^ (-(i : ℝ))) * (M (n - i) * ‖y‖ ^ (-(s + ((n - i : ℕ) : ℝ)))) := by
              refine mul_le_mul ?_ hHk' hHk0 (by positivity)
              exact hS1.trans (by rw [← hyi]; exact mul_le_mul_of_nonneg_left hρi hS0)
          _ = S * M (n - i) * ‖y‖ ^ e := by rw [← hexp]; ring
          _ ≤ (1 + S) * Mm * ‖y‖ ^ e := by
              have : S * M (n - i) ≤ (1 + S) * Mm := by
                nlinarith [hM0 (n - i), mul_nonneg hS0 hMm0]
              exact mul_le_mul_of_nonneg_right this hyr
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((1 + S) * Mm * ‖y‖ ^ e) :=
        Finset.sum_le_sum hterm
    _ = 2 ^ n * ((1 + S) * Mm) * ‖y‖ ^ e := by
        rw [← Finset.sum_mul]
        have : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [this]; ring

lemma kF_bound (h : LocKer d s k) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ → ∀ y : Euc d,
      ‖iteratedFDeriv ℝ n (kF k ρ) y‖ ≤ C * (if ρ / 2 ≤ ‖y‖ then ‖y‖ ^ (-(s + n)) else 0) := by
  obtain ⟨C, hC0, hC⟩ := h.kF_bound_aux n
  refine ⟨C, hC0, fun ρ hρ y => ?_⟩
  by_cases hy : ρ / 2 ≤ ‖y‖
  · rw [if_pos hy]; exact hC ρ hρ y hy
  · rw [if_neg hy, mul_zero, kF_zero_of_lt hρ k (not_le.mp hy) n]; simp

end LocKer

end HRS.Parx

end
