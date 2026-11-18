import HRS.Equilibrium.Parametrix.PX4aAuxF

/-!
# Packet PX4a auxiliaries G: the local part of the Riesz kernel

`rieszK = ζ_{1/128} · g` is a `LocKer` of order `s`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The local part `ζ_{1/128} g` of the Riesz kernel (as a function on `ℝ^d`). -/
def rieszK (d : ℕ) (s : ℝ) (v : Euc d) : ℝ := px3a_zeta d (1 / 128) v * periodicRiesz d s (Torus.mk v)

lemma rieszK_eq_zero {s : ℝ} {v : Euc d} (hv : 1 / 128 ≤ ‖v‖) : rieszK d s v = 0 := by
  unfold rieszK
  rw [px3a_zeta_eq_zero (by norm_num : (0 : ℝ) < 1 / 128) hv, zero_mul]

lemma iteratedFDeriv_rieszK_eq_zero (s : ℝ) {v : Euc d} (hv : 1 / 128 < ‖v‖) (n : ℕ) :
    iteratedFDeriv ℝ n (rieszK d s) v = 0 := by
  have : rieszK d s =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hv] with u hu
    exact rieszK_eq_zero hu.le
  rw [(this.iteratedFDeriv ℝ n).eq_of_nhds]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext w; simp [iteratedFDeriv_zero_eq_comp]
  · have := iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := Euc d) (by omega : n ≠ 0) (0 : ℝ)
    exact congrFun this v

set_option maxHeartbeats 1600000 in
lemma rieszK_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Euc d, v ≠ 0 →
      ‖iteratedFDeriv ℝ n (rieszK d s) v‖ ≤ C * ‖v‖ ^ (-(s + n)) := by
  obtain ⟨S, hS0, hS⟩ := px3a_zeta_deriv_bound (d := d) n
  have hkb := kerBound_periodicRiesz (d := d) hd hs0 hsd n
  have hM : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ (j ≤ n → ∀ y w : Euc d, Torus.mk y ≠ 0 → Torus.mk w = Torus.mk y →
      (∀ i, |w i| ≤ 1 / 2) →
      ‖iteratedFDeriv ℝ j (Torus.lift (periodicRiesz d s)) y‖ ≤ C * (‖w‖ ^ (-s - j) + 1)) := by
    intro j
    by_cases hj : j ≤ n
    · obtain ⟨C, hC0, hC⟩ := hkb.bound j hj
      exact ⟨C, hC0, fun _ => hC⟩
    · exact ⟨0, le_rfl, fun h => absurd h hj⟩
  choose M hM0 hMb using hM
  set Mm : ℝ := ∑ j ∈ Finset.range (n + 1), M j with hMm
  have hMm0 : 0 ≤ Mm := Finset.sum_nonneg fun j _ => hM0 j
  have hMle : ∀ j ≤ n, M j ≤ Mm := fun j hj =>
    Finset.single_le_sum (f := M) (fun i _ => hM0 i) (Finset.mem_range.mpr (by omega))
  refine ⟨2 ^ n * (2 * S * 2 ^ n * (1 + Mm)), by positivity, fun v hv0 => ?_⟩
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hnn : 0 ≤ ‖v‖ ^ (-(s + (n : ℝ))) := Real.rpow_nonneg hvpos.le _
  by_cases hv : ‖v‖ < 1 / 64
  swap
  · rw [iteratedFDeriv_rieszK_eq_zero s (by linarith [not_lt.mp hv]) n]
    simp only [norm_zero]
    positivity
  have hmk : Torus.mk v ≠ 0 := by
    refine box_ne_zero hv0 (fun i => ?_)
    have := PiLp.norm_apply_le v i
    simp only [Real.norm_eq_abs] at this
    linarith
  set U' : Set (Euc d) := {y : Euc d | Torus.mk y ≠ 0} with hU'
  have hU'o : IsOpen U' := isOpen_mk_ne_zero'
  have hvU : v ∈ U' := hmk
  have hgs : ContDiffOn ℝ ∞' (Torus.lift (periodicRiesz d s)) U' :=
    KernelGrad.contDiffOn_periodicRiesz hd hs0.le hsd
  have hzs : ContDiffOn ℝ ∞' (px3a_zeta d (1 / 128)) U' :=
    (px3a_zeta_contDiff (d := d) (1 / 128) ⊤).contDiffOn
  have hmul := norm_iteratedFDerivWithin_mul_le (n := n) hzs hgs hU'o.uniqueDiffOn hvU
    (by exact_mod_cast le_top)
  have e0 : iteratedFDeriv ℝ n (rieszK d s) v =
      iteratedFDerivWithin ℝ n (fun y => px3a_zeta d (1 / 128) y * Torus.lift (periodicRiesz d s) y) U' v := by
    rw [iteratedFDerivWithin_of_isOpen n hU'o hvU]; rfl
  rw [e0]
  refine hmul.trans ?_
  have eZ : ∀ i, iteratedFDerivWithin ℝ i (px3a_zeta d (1 / 128)) U' v =
      iteratedFDeriv ℝ i (px3a_zeta d (1 / 128)) v := fun i => iteratedFDerivWithin_of_isOpen i hU'o hvU
  have eG : ∀ i, iteratedFDerivWithin ℝ i (Torus.lift (periodicRiesz d s)) U' v =
      iteratedFDeriv ℝ i (Torus.lift (periodicRiesz d s)) v := fun i => iteratedFDerivWithin_of_isOpen i hU'o hvU
  simp only [eZ, eG]
  have hv1 : ‖v‖ ≤ 1 := by linarith
  have hterm : ∀ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (px3a_zeta d (1 / 128)) v‖ *
        ‖iteratedFDeriv ℝ (n - i) (Torus.lift (periodicRiesz d s)) v‖ ≤
      (n.choose i : ℝ) * ((2 * S * 2 ^ n * (1 + Mm)) * ‖v‖ ^ (-(s + (n : ℝ)))) := by
    intro i hi
    have hij : i ≤ n := by have := Finset.mem_range.mp hi; omega
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hzi := hS (1 / 128) (by norm_num) i hij v
    have hgi := hMb (n - i) (by omega) v v hmk rfl (fun i' => by
      have := PiLp.norm_apply_le v i'
      simp only [Real.norm_eq_abs] at this
      linarith)
    have e128 : ((1 / 128 : ℝ)⁻¹) = 128 := by norm_num
    rw [e128] at hzi
    -- ‖v‖^{-(s+n-i)} ≥ 1
    have hexp : -(s + ((n - i : ℕ) : ℝ)) ≤ 0 := by
      have : (0 : ℝ) ≤ ((n - i : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have h1 : (1 : ℝ) ≤ ‖v‖ ^ (-(s + ((n - i : ℕ) : ℝ))) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hvpos hv1 hexp
    have hg2 : ‖iteratedFDeriv ℝ (n - i) (Torus.lift (periodicRiesz d s)) v‖ ≤
        2 * M (n - i) * ‖v‖ ^ (-(s + ((n - i : ℕ) : ℝ))) := by
      refine hgi.trans ?_
      have : -s - ((n - i : ℕ) : ℝ) = -(s + ((n - i : ℕ) : ℝ)) := by ring
      rw [this]
      nlinarith [hM0 (n - i)]
    have h128 : (128 : ℝ) ^ i * ‖v‖ ^ i ≤ 2 ^ n := by
      have h2 : (128 : ℝ) ^ i * ‖v‖ ^ i = (128 * ‖v‖) ^ i := by rw [mul_pow]
      rw [h2]
      have : 128 * ‖v‖ ≤ 2 := by linarith
      calc (128 * ‖v‖) ^ i ≤ 2 ^ i := pow_le_pow_left₀ (by positivity) this i
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hij
    have hpow : ‖v‖ ^ (-(s + ((n - i : ℕ) : ℝ))) = ‖v‖ ^ (-(s + (n : ℝ))) * ‖v‖ ^ (i : ℝ) := by
      rw [← Real.rpow_add hvpos]; congr 1; push_cast [Nat.cast_sub hij]; ring
    rw [Real.rpow_natCast] at hpow
    have hMk : M (n - i) ≤ Mm := hMle _ (by omega)
    calc ‖iteratedFDeriv ℝ i (px3a_zeta d (1 / 128)) v‖ *
          ‖iteratedFDeriv ℝ (n - i) (Torus.lift (periodicRiesz d s)) v‖
        ≤ (S * 128 ^ i) * (2 * M (n - i) * ‖v‖ ^ (-(s + ((n - i : ℕ) : ℝ)))) :=
          mul_le_mul hzi hg2 (norm_nonneg _) (by positivity)
      _ = 2 * S * M (n - i) * ((128 ^ i * ‖v‖ ^ i) * ‖v‖ ^ (-(s + (n : ℝ)))) := by
          rw [hpow]; ring
      _ ≤ 2 * S * M (n - i) * (2 ^ n * ‖v‖ ^ (-(s + (n : ℝ)))) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h128 hnn)
            (mul_nonneg (mul_nonneg (by norm_num) hS0) (hM0 _))
      _ ≤ (2 * S * 2 ^ n * (1 + Mm)) * ‖v‖ ^ (-(s + (n : ℝ))) := by
          have : 2 * S * M (n - i) * 2 ^ n ≤ 2 * S * 2 ^ n * (1 + Mm) := by
            have := hMk
            nlinarith [mul_nonneg hS0 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n), hM0 (n - i)]
          nlinarith [this, hnn]
  calc _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((2 * S * 2 ^ n * (1 + Mm)) * ‖v‖ ^ (-(s + (n : ℝ)))) :=
        Finset.sum_le_sum hterm
    _ = 2 ^ n * (2 * S * 2 ^ n * (1 + Mm)) * ‖v‖ ^ (-(s + (n : ℝ))) := by
        rw [← Finset.sum_mul]
        have : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [this]; ring

theorem locKer_riesz (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) : LocKer d s (rieszK d s) where
  s_pos := hs0
  s_lt := hsd
  smooth := by
    intro v hv
    by_cases hm : Torus.mk v = 0
    · have h1 := one_le_norm_of_mk_eq_zero hm hv
      have : rieszK d s =ᶠ[𝓝 v] fun _ => (0 : ℝ) := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
          (show (1 / 2 : ℝ) < ‖v‖ by linarith)] with u hu
        exact rieszK_eq_zero (by have : (1 / 2 : ℝ) < ‖u‖ := hu; linarith)
      exact (contDiffAt_const.congr_of_eventuallyEq this).contDiffWithinAt
    · have hg : ContDiffAt ℝ ∞' (Torus.lift (periodicRiesz d s)) v :=
        (KernelGrad.contDiffOn_periodicRiesz hd hs0.le hsd).contDiffAt (isOpen_mk_ne_zero'.mem_nhds hm)
      exact ((px3a_zeta_contDiff (d := d) (1 / 128) ⊤).contDiffAt.mul hg).contDiffWithinAt
  supp v hv := rieszK_eq_zero (by linarith)
  bound n := rieszK_bound hd hs0 hsd n

end HRS.Parx

end
