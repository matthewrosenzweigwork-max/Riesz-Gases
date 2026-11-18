import HRS.MS.SA16TCo1
import HRS.MS.SA16StrongLeib

/-!
# S.A.16 (SA16T) Co2: the smoothed and cut-off coefficient `χ_{n+1} (ρ_n ⋆ g)`

For `g ∈ C^k` with `|g(y)| ≤ C0 + L|y|` and `‖D^j g‖ ≤ L` (`1 ≤ j ≤ k`), `f_n = χ_{n+1} (ρ_n ⋆ g)` is `C^∞` and
`‖D^j f_n‖ ≤ Bu` for `1 ≤ j ≤ k`, with `Bu` depending only on `d, k, C0, L` (not on `n`).  (`f_n` itself is bounded by
`C0 + L (2n+3)`, not uniformly in `n`: only the derivatives of order `≥ 1` enter the energy estimate.)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Co2
variable {d : ℕ}

/-- the cutoff radius -/
def sa16t_R (n : ℕ) : ℝ := (n : ℝ) + 1

lemma sa16t_R_ge (n : ℕ) : 1 ≤ sa16t_R n := by
  unfold sa16t_R; have := n.cast_nonneg (α := ℝ); linarith

/-- the smoothed, cut-off coefficient -/
def sa16t_bc (d n : ℕ) (g : Euc d → ℝ) : Euc d → ℝ :=
  fun x => sa16j_chi d (sa16t_R n) x * sa16j_conv (sa16y_rho d n) g x

lemma sa16t_chi_decay (d m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 1 ≤ R → ∀ i ≤ m, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ i (sa16j_chi d R) x‖ ≤ B * (R⁻¹) ^ i := by
  obtain ⟨B, hB0, hB⟩ := (sa16j_bump d).hasCompactSupport.exists_bound_iteratedFDeriv
    (sa16j_bump d).contDiff m
  refine ⟨B, hB0, fun R hR i hi x => ?_⟩
  set g : Euc d →L[ℝ] Euc d := R⁻¹ • ContinuousLinearMap.id ℝ (Euc d) with hg
  have hfun : sa16j_chi d R = (⇑(sa16j_bump d)) ∘ g := by
    funext y; simp [hg, sa16j_chi]
  have hR0 : 0 < R := by linarith
  have hgn : ‖g‖ ≤ R⁻¹ := by
    refine (norm_smul_le R⁻¹ (ContinuousLinearMap.id ℝ (Euc d))).trans ?_
    rw [Real.norm_of_nonneg (inv_nonneg.2 hR0.le)]
    calc R⁻¹ * ‖ContinuousLinearMap.id ℝ (Euc d)‖ ≤ R⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_nonneg.2 hR0.le)
      _ = R⁻¹ := mul_one _
  rw [hfun, g.iteratedFDeriv_comp_right (sa16j_bump d).contDiff x (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _ : Fin i, ‖g‖ ≤ (R⁻¹) ^ i := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (norm_nonneg _) hgn i
  calc ‖iteratedFDeriv ℝ i (sa16j_bump d) (g x)‖ * ∏ _ : Fin i, ‖g‖ ≤ B * (R⁻¹) ^ i :=
        mul_le_mul (hB i hi _) hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _) hB0

lemma sa16t_chi_tsupport (R : ℝ) (hR : 0 < R) : tsupport (sa16j_chi d R) ⊆ closedBall (0 : Euc d) (2 * R) := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  by_contra hn
  rw [mem_closedBall_zero_iff, not_le] at hn
  apply hy
  show sa16j_chi d R y = 0
  unfold sa16j_chi
  refine (sa16j_bump d).zero_of_le_dist ?_
  show (2 : ℝ) ≤ dist (R⁻¹ • y) 0
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
  rw [← div_eq_inv_mul, le_div_iff₀ hR]
  linarith

lemma sa16t_vanish {R : ℝ} (hR : 0 < R) (h : Euc d → ℝ) {x : Euc d} (hx : 2 * R < ‖x‖) (j : ℕ) :
    iteratedFDeriv ℝ j (fun y => sa16j_chi d R y * h y) x = 0 := by
  by_contra hne
  have h1 := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := fun y => sa16j_chi d R y * h y) j hne
  have h2 := tsupport_mul_subset_left (f := sa16j_chi d R) (g := h) h1
  have h3 := sa16t_chi_tsupport R hR h2
  rw [mem_closedBall_zero_iff] at h3
  linarith

lemma sa16t_conv_le {k u : Euc d → ℝ} {R A : ℝ} (hk : Integrable k) (hks : ∀ z, R < ‖z‖ → k z = 0)
    (x : Euc d) (hA : ∀ z, ‖z‖ ≤ R → |u (x - z)| ≤ A) :
    ‖∫ z, k z * u (x - z)‖ ≤ (∫ z, |k z|) * A := by
  have hpt : ∀ z, ‖k z * u (x - z)‖ ≤ |k z| * A := by
    intro z
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hz : R < ‖z‖
    · rw [hks z hz]; simp
    · push Not at hz
      exact mul_le_mul_of_nonneg_left (hA z hz) (abs_nonneg _)
  have hint : Integrable (fun z => |k z| * A) := hk.abs.mul_const A
  rw [← integral_mul_const]
  exact norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)

lemma sa16t_rho_abs_int (n : ℕ) : ∫ z, |sa16y_rho d n z| = 1 := by
  have : ∀ z, |sa16y_rho d n z| = sa16y_rho d n z := fun z => abs_of_nonneg (sa16y_rho_nonneg n z)
  simp_rw [this]; exact sa16y_rho_int n

lemma sa16t_rho_supp (n : ℕ) (z : Euc d) (hz : 1 < ‖z‖) : sa16y_rho d n z = 0 := by
  refine sa16y_rho_supp n z (lt_of_le_of_lt ?_ hz)
  have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_one this]; linarith [n.cast_nonneg (α := ℝ)]

/-- linear growth of the mollification -/
lemma sa16t_mollify_growth {g : Euc d → ℝ} {C0 L : ℝ} (hC0 : 0 ≤ C0) (hL : 0 ≤ L)
    (hg : ∀ y, |g y| ≤ C0 + L * ‖y‖) (n : ℕ) (x : Euc d) :
    |sa16j_conv (sa16y_rho d n) g x| ≤ C0 + L * (‖x‖ + 1) := by
  unfold sa16j_conv
  have := sa16t_conv_le (k := sa16y_rho d n) (u := g) (R := 1) (A := C0 + L * (‖x‖ + 1))
    (sa16y_rho_integrable n) (fun z hz => sa16t_rho_supp n z hz) x (fun z hz => by
      refine (hg _).trans ?_
      have : ‖x - z‖ ≤ ‖x‖ + 1 := (norm_sub_le _ _).trans (by linarith)
      nlinarith)
  rwa [sa16t_rho_abs_int, one_mul, Real.norm_eq_abs] at this

/-- derivative bounds of the mollification (derivative on `g`) -/
lemma sa16t_mollify_deriv {g : Euc d → ℝ} {k : ℕ} {L : ℝ} (hg : ContDiff ℝ k g)
    (hgb : ∀ j, 1 ≤ j → j ≤ k → ∀ y, ‖iteratedFDeriv ℝ j g y‖ ≤ L) (n : ℕ) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (x : Euc d) : ‖iteratedFDeriv ℝ j (sa16j_conv (sa16y_rho d n) g) x‖ ≤ ((d : ℝ) + 1) ^ k * L := by
  have hL : 0 ≤ L := (norm_nonneg _).trans (hgb j hj1 hjk 0)
  have hsupp : ∀ z, 1 / ((n : ℝ) + 1) < ‖z‖ → sa16y_rho d n z = 0 := fun z hz => sa16y_rho_supp n z hz
  refine (sa16j_norm_iter_le _ x j).trans ?_
  have hjr : j + (k - j) = k := by omega
  have hterm : ∀ r : Fin j → Fin d, |partialDeriv r (sa16j_conv (sa16y_rho d n) g) x| ≤ L := by
    intro r
    have hg' : ContDiff ℝ ((j + (k - j) : ℕ) : WithTop ℕ∞) g := by rw [hjr]; exact hg
    rw [sa16y_conv_pdN hsupp (by positivity) (sa16y_rho_integrable n) j (k - j) r g hg']
    exact sa16y_mollify_bound n (sa16y_pd_contDiffN hg' r).continuous
      (fun y => (sa16y_pd_le_iter g y r).trans (hgb j hj1 hjk y)) x
  calc ∑ r : Fin j → Fin d, |partialDeriv r (sa16j_conv (sa16y_rho d n) g) x|
      ≤ ∑ r : Fin j → Fin d, L := Finset.sum_le_sum fun r _ => hterm r
    _ = (d : ℝ) ^ j * L := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
        simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
    _ ≤ ((d : ℝ) + 1) ^ k * L := by
        refine mul_le_mul_of_nonneg_right ?_ hL
        calc (d : ℝ) ^ j ≤ ((d : ℝ) + 1) ^ j := pow_le_pow_left₀ (Nat.cast_nonneg d) (by linarith) _
          _ ≤ ((d : ℝ) + 1) ^ k :=
            pow_le_pow_right₀ (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith) hjk

/-- the uniform derivative bound of `sa16t_bc` -/
def sa16t_Bu (Bχ : ℝ) (d k : ℕ) (C0 L : ℝ) : ℝ :=
  2 ^ k * (max 1 Bχ * (C0 + 3 * L + ((d : ℝ) + 1) ^ k * L))

theorem sa16t_bc_bounds (d k : ℕ) :
    ∃ Bχ : ℝ, 0 ≤ Bχ ∧ ∀ (g : Euc d → ℝ) (C0 L : ℝ), 0 ≤ C0 → 0 ≤ L → ContDiff ℝ k g →
      (∀ y, |g y| ≤ C0 + L * ‖y‖) → (∀ j, 1 ≤ j → j ≤ k → ∀ y, ‖iteratedFDeriv ℝ j g y‖ ≤ L) → ∀ n : ℕ,
      ContDiff ℝ ∞ (sa16t_bc d n g) ∧ (∀ x, |sa16t_bc d n g x| ≤ C0 + L * (2 * sa16t_R n + 1)) ∧
      ∀ j, 1 ≤ j → j ≤ k → ∀ x, ‖iteratedFDeriv ℝ j (sa16t_bc d n g) x‖ ≤ sa16t_Bu Bχ d k C0 L := by
  obtain ⟨Bχ, hB0, hBχ⟩ := sa16t_chi_decay d k
  refine ⟨Bχ, hB0, fun g C0 L hC0 hL hg hgl hgb n => ?_⟩
  have hR1 := sa16t_R_ge n
  have hR0 : 0 < sa16t_R n := by linarith
  have hgc : Continuous g := hg.continuous
  have hhs : ContDiff ℝ ∞ (sa16j_conv (sa16y_rho d n) g) := sa16y_mollify_smooth n hgc
  have hbc : sa16t_bc d n g = fun x => sa16j_chi d (sa16t_R n) x * sa16j_conv (sa16y_rho d n) g x := rfl
  have hχs := sa16j_chi_contDiff d (sa16t_R n)
  refine ⟨hχs.mul hhs, fun x => ?_, fun j hj1 hjk x => ?_⟩
  · by_cases hx : 2 * sa16t_R n < ‖x‖
    · have h0 := congrArg norm (sa16t_vanish hR0 (sa16j_conv (sa16y_rho d n) g) hx 0)
      rw [norm_iteratedFDeriv_zero, norm_zero] at h0
      show |sa16j_chi d (sa16t_R n) x * sa16j_conv (sa16y_rho d n) g x| ≤ _
      rw [← Real.norm_eq_abs, h0]; positivity
    · push Not at hx
      simp only [sa16t_bc, abs_mul]
      have h1 : |sa16j_chi d (sa16t_R n) x| ≤ 1 := by
        rw [abs_of_nonneg (by exact (sa16j_bump d).nonneg)]; exact (sa16j_bump d).le_one
      have h2 := sa16t_mollify_growth hC0 hL hgl n x
      calc |sa16j_chi d (sa16t_R n) x| * |sa16j_conv (sa16y_rho d n) g x| ≤ 1 * (C0 + L * (‖x‖ + 1)) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        _ ≤ C0 + L * (2 * sa16t_R n + 1) := by nlinarith
  · set R := sa16t_R n
    set Ku : ℝ := max 1 Bχ * (C0 + 3 * L + ((d : ℝ) + 1) ^ k * L) with hKu
    have hKu0 : 0 ≤ Ku := by rw [hKu]; positivity
    by_cases hx : 2 * R < ‖x‖
    · rw [hbc, sa16t_vanish hR0 _ hx j, norm_zero]
      unfold sa16t_Bu; positivity
    · push Not at hx
      have hL' := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (hχs.of_le (by exact_mod_cast le_top))
        (hhs.of_le (by exact_mod_cast le_top)) x (n := j) (N := (j : ℕ∞ω)) le_rfl
      rw [hbc]
      refine hL'.trans ?_
      have hterm : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (sa16j_chi d R) x‖ *
          ‖iteratedFDeriv ℝ (j - i) (sa16j_conv (sa16y_rho d n) g) x‖ ≤ (j.choose i : ℝ) * Ku := by
        intro i hi
        have hi' : i ≤ j := by have := Finset.mem_range.1 hi; omega
        have hc : (0 : ℝ) ≤ j.choose i := Nat.cast_nonneg _
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hc
        have hχi := hBχ R hR1 i (hi'.trans hjk) x
        have hRi : (R⁻¹) ^ i ≤ 1 := pow_le_one₀ (inv_nonneg.2 hR0.le) (inv_le_one_of_one_le₀ hR1)
        have hmax1 : (1 : ℝ) ≤ max 1 Bχ := le_max_left _ _
        have hmaxB : Bχ ≤ max 1 Bχ := le_max_right _ _
        have hdk : 0 ≤ ((d : ℝ) + 1) ^ k * L := by positivity
        have hhd : 0 ≤ C0 + 3 * L + ((d : ℝ) + 1) ^ k * L := by positivity
        rcases Nat.eq_zero_or_pos i with h0 | hipos
        · subst h0
          have h1 : ‖iteratedFDeriv ℝ 0 (sa16j_chi d R) x‖ ≤ 1 := by
            rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (by exact (sa16j_bump d).nonneg)]
            exact (sa16j_bump d).le_one
          have h2 := sa16t_mollify_deriv hg hgb n (j := j - 0) (by omega) (by omega) x
          calc ‖iteratedFDeriv ℝ 0 (sa16j_chi d R) x‖ * ‖iteratedFDeriv ℝ (j - 0) (sa16j_conv (sa16y_rho d n) g) x‖
              ≤ 1 * (((d : ℝ) + 1) ^ k * L) := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
            _ ≤ Ku := by
                rw [hKu, one_mul]
                calc ((d : ℝ) + 1) ^ k * L ≤ C0 + 3 * L + ((d : ℝ) + 1) ^ k * L := by linarith
                  _ = 1 * (C0 + 3 * L + ((d : ℝ) + 1) ^ k * L) := (one_mul _).symm
                  _ ≤ _ := mul_le_mul_of_nonneg_right hmax1 hhd
        · by_cases hij : i = j
          · subst hij
            have h2 : ‖iteratedFDeriv ℝ (i - i) (sa16j_conv (sa16y_rho d n) g) x‖ ≤ C0 + L * (2 * R + 1) := by
              rw [Nat.sub_self, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
              refine (sa16t_mollify_growth hC0 hL hgl n x).trans ?_
              nlinarith
            have h3 : (R⁻¹) ^ i ≤ R⁻¹ := by
              calc (R⁻¹) ^ i ≤ (R⁻¹) ^ 1 := pow_le_pow_of_le_one (inv_nonneg.2 hR0.le)
                    (inv_le_one_of_one_le₀ hR1) hipos
                _ = R⁻¹ := pow_one _
            have h4 : R⁻¹ * (C0 + L * (2 * R + 1)) ≤ C0 + 3 * L := by
              have hRi1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR1
              have e : R⁻¹ * (C0 + L * (2 * R + 1)) = R⁻¹ * C0 + 2 * L + R⁻¹ * L := by
                field_simp; ring
              rw [e]
              nlinarith [mul_le_mul_of_nonneg_right hRi1 hC0, mul_le_mul_of_nonneg_right hRi1 hL]
            calc ‖iteratedFDeriv ℝ i (sa16j_chi d R) x‖ * ‖iteratedFDeriv ℝ (i - i) (sa16j_conv (sa16y_rho d n) g) x‖
                ≤ (Bχ * R⁻¹) * (C0 + L * (2 * R + 1)) :=
                  mul_le_mul (hχi.trans (mul_le_mul_of_nonneg_left h3 hB0)) h2 (norm_nonneg _)
                    (by positivity)
              _ = Bχ * (R⁻¹ * (C0 + L * (2 * R + 1))) := by ring
              _ ≤ Bχ * (C0 + 3 * L) := mul_le_mul_of_nonneg_left h4 hB0
              _ ≤ Ku := by
                  rw [hKu]
                  exact mul_le_mul hmaxB (by linarith) (by positivity) (by positivity)
          · have hji : 1 ≤ j - i := by omega
            have h2 := sa16t_mollify_deriv hg hgb n (j := j - i) hji (by omega) x
            calc ‖iteratedFDeriv ℝ i (sa16j_chi d R) x‖ * ‖iteratedFDeriv ℝ (j - i) (sa16j_conv (sa16y_rho d n) g) x‖
                ≤ Bχ * (((d : ℝ) + 1) ^ k * L) :=
                  mul_le_mul (hχi.trans (mul_le_of_le_one_right hB0 hRi)) h2 (norm_nonneg _) hB0
              _ ≤ Ku := by
                  rw [hKu]
                  exact mul_le_mul hmaxB (by linarith) hdk (by positivity)
      calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (sa16j_chi d R) x‖ *
            ‖iteratedFDeriv ℝ (j - i) (sa16j_conv (sa16y_rho d n) g) x‖
          ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Ku := Finset.sum_le_sum hterm
        _ = 2 ^ j * Ku := by
            rw [← Finset.sum_mul]
            have : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
              exact_mod_cast Nat.sum_range_choose j
            rw [this]
        _ ≤ sa16t_Bu Bχ d k C0 L := by
            unfold sa16t_Bu
            exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hjk) hKu0

end Co2

end HRS.Whole.AppendixA.Phase2SA16R
