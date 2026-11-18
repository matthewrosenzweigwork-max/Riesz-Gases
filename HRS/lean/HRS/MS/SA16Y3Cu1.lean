import HRS.MS.SA16JetInterface
import HRS.MS.SA16Y3Dc1

/-!
# S.A.16 (SA16Y3) Cu1: uniform derivative bounds for the truncated drift `χ_R · b` (truncation route, step (a))

`sa16y3_chi_decay`: `‖∂^i χ_R x‖ ≤ C_i (R⁻¹)^i` (scaling `iteratedFDeriv_comp_const_smul`).
`sa16y3_chi_zero_far`: `∂^i χ_R x = 0` for `2R < ‖x‖`.
`sa16y3_cut_mul_der_bound`: for `|b x| ≤ A + L‖x‖` and `‖∂^j b‖ ≤ L` (`1 ≤ j ≤ k`), `‖∂^j (χ_R b)‖` is bounded uniformly in `R ≥ 1`, `x`, `1 ≤ j ≤ k`; the constant `C` depends only on `d, k, A, L` and is chosen BEFORE `b` (uniform over all such `b`).
No zeroth-order bound on `χ_R b` is claimed (it grows like `R`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

variable {d : ℕ}

lemma sa16y3_chi_decay (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ x : EuclideanSpace ℝ (Fin d),
    ‖iteratedFDeriv ℝ i (sa16j_chi d R) x‖ ≤ C * (R⁻¹) ^ i := by
  obtain ⟨C, hC0, hC⟩ := (sa16j_bump d).hasCompactSupport.exists_bound_iteratedFDeriv
    (sa16j_bump d).contDiff i
  refine ⟨C, hC0, fun R hR x => ?_⟩
  have hsm : ContDiff ℝ i (sa16j_bump d) := (sa16j_bump d).contDiff.of_le (by exact_mod_cast le_top)
  have hfun : sa16j_chi d R = fun z => sa16j_bump d (R⁻¹ • z) := rfl
  have hder := congrFun (iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (R⁻¹) hsm) x
  rw [hfun, hder, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR), mul_comm]
  exact mul_le_mul_of_nonneg_right (hC i le_rfl (R⁻¹ • x)) (pow_nonneg (inv_nonneg.2 hR.le) i)

lemma sa16y3_chi_zero_far (i : ℕ) {R : ℝ} (hR : 0 < R) {x : EuclideanSpace ℝ (Fin d)} (hx : 2 * R < ‖x‖) :
    iteratedFDeriv ℝ i (sa16j_chi d R) x = 0 := by
  have hev : sa16j_chi d R =ᶠ[𝓝 x] 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    show sa16j_bump d (R⁻¹ • y) = 0
    apply (sa16j_bump d).zero_of_le_dist
    rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le)]
    have h2 : 2 ≤ R⁻¹ * ‖y‖ := by
      rw [← div_eq_inv_mul, le_div_iff₀ hR]
      linarith
    simpa [sa16j_bump] using h2
  have h1 := (hev.iteratedFDeriv ℝ (n := i)).eq_of_nhds
  rw [h1]
  simp

lemma sa16y3_cut_mul_der_bound {k : ℕ} {A L : ℝ} (hA0 : 0 ≤ A) (hL0 : 0 ≤ L) :
    ∃ C : ℝ, ∀ b : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ b → (∀ x, |b x| ≤ A + L * ‖x‖) →
      (∀ j, 1 ≤ j → j ≤ k → ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ L) →
      ∀ R : ℝ, 1 ≤ R → ∀ j, 1 ≤ j → j ≤ k → ∀ x : EuclideanSpace ℝ (Fin d),
      ‖iteratedFDeriv ℝ j (fun y => sa16j_chi d R y * b y) x‖ ≤ C := by
  choose Cd hCd0 hCd using fun i : ℕ => sa16y3_chi_decay (d := d) i
  set Cmax : ℝ := ∑ i ∈ Finset.range (k + 1), Cd i with hCmax
  have hCd_le : ∀ i, i ≤ k → Cd i ≤ Cmax := fun i hi =>
    Finset.single_le_sum (f := Cd) (fun i _ => hCd0 i) (Finset.mem_range.2 (by omega))
  have hCmax0 : 0 ≤ Cmax := Finset.sum_nonneg fun i _ => hCd0 i
  set M : ℝ := Cmax + A + 3 * L + 1 with hM
  have hM1 : 1 ≤ M := by rw [hM]; linarith
  have hCM : Cmax ≤ M := by rw [hM]; linarith
  have hLM : L ≤ M := by rw [hM]; linarith
  have hAM : A + 2 * L ≤ M := by rw [hM]; linarith
  refine ⟨((k : ℝ) + 1) * 2 ^ k * (M * M), fun b hb hA hL R hR j hj1 hjk x => ?_⟩
  have hR0 : 0 < R := by linarith
  have hχs : ContDiff ℝ ∞ (sa16j_chi d R) := sa16j_chi_contDiff d _
  have hleib := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (j : ℕ∞ω))
    (hχs.of_le (by exact_mod_cast le_top)) (hb.of_le (by exact_mod_cast le_top)) x (n := j) le_rfl
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (sa16j_chi d R) x‖ * ‖iteratedFDeriv ℝ (j - i) b x‖ ≤
        2 ^ k * (M * M) := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.1 hi)
    by_cases h0 : i = 0
    · subst h0
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, norm_iteratedFDeriv_zero, Nat.sub_zero]
      have hχ0 : ‖sa16j_chi d R x‖ ≤ M := by
        have := hCd 0 R hR0 x
        simp only [pow_zero, mul_one, norm_iteratedFDeriv_zero] at this
        exact this.trans ((hCd_le 0 (Nat.zero_le _)).trans hCM)
      have hbj : ‖iteratedFDeriv ℝ j b x‖ ≤ M := (hL j hj1 hjk x).trans hLM
      calc ‖sa16j_chi d R x‖ * ‖iteratedFDeriv ℝ j b x‖ ≤ M * M :=
            mul_le_mul hχ0 hbj (norm_nonneg _) (by linarith)
        _ ≤ 2 ^ k * (M * M) := le_mul_of_one_le_left (by positivity) h2k
    · by_cases hij : i = j
      · subst hij
        rw [Nat.sub_self, Nat.choose_self, Nat.cast_one, one_mul, norm_iteratedFDeriv_zero]
        by_cases hfar : 2 * R < ‖x‖
        · rw [sa16y3_chi_zero_far i hR0 hfar, norm_zero, zero_mul]
          positivity
        · have hdec := hCd i R hR0 x
          have ht1 : (R⁻¹) ^ i ≤ 1 := pow_le_one₀ (inv_nonneg.2 hR0.le) (inv_le_one_of_one_le₀ hR)
          obtain ⟨i', hi'⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          subst hi'
          have htR : (R⁻¹) ^ (i' + 1) * R ≤ 1 := by
            rw [pow_succ, mul_assoc, inv_mul_cancel₀ hR0.ne', mul_one]
            exact pow_le_one₀ (inv_nonneg.2 hR0.le) (inv_le_one_of_one_le₀ hR)
          have hbx : ‖b x‖ ≤ A + L * (2 * R) := by
            have := hA x
            rw [Real.norm_eq_abs] at *
            have hx : ‖x‖ ≤ 2 * R := not_lt.1 hfar
            nlinarith [norm_nonneg x]
          have hCi : Cd (i' + 1) ≤ Cmax := hCd_le _ (by omega)
          have hC0 : 0 ≤ Cd (i' + 1) := hCd0 _
          calc ‖iteratedFDeriv ℝ (i' + 1) (sa16j_chi d R) x‖ * ‖b x‖
              ≤ (Cd (i' + 1) * (R⁻¹) ^ (i' + 1)) * (A + L * (2 * R)) :=
                mul_le_mul hdec hbx (norm_nonneg _) (by positivity)
            _ = Cd (i' + 1) * ((R⁻¹) ^ (i' + 1) * (A + 2 * L * R)) := by ring
            _ ≤ Cd (i' + 1) * (A + 2 * L) := by
                apply mul_le_mul_of_nonneg_left _ hC0
                nlinarith [pow_nonneg (inv_nonneg.2 hR0.le) (i' + 1)]
            _ ≤ M * M := by
                apply mul_le_mul (hCi.trans hCM) (by linarith) (by positivity) (by linarith)
            _ ≤ 2 ^ k * (M * M) := le_mul_of_one_le_left (by positivity) h2k
      · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr h0
        have hij' : i < j := lt_of_le_of_ne hi' hij
        have hdec := hCd i R hR0 x
        have ht1 : (R⁻¹) ^ i ≤ 1 := pow_le_one₀ (inv_nonneg.2 hR0.le) (inv_le_one_of_one_le₀ hR)
        have hA1 : ‖iteratedFDeriv ℝ i (sa16j_chi d R) x‖ ≤ M :=
          (hdec.trans (mul_le_of_le_one_right (hCd0 i) ht1)).trans ((hCd_le i (by omega)).trans hCM)
        have hbd : ‖iteratedFDeriv ℝ (j - i) b x‖ ≤ M :=
          (hL (j - i) (by omega) (by omega) x).trans hLM
        have hC2 : (j.choose i : ℝ) ≤ 2 ^ k := by
          have h1 : j.choose i ≤ 2 ^ j := Nat.choose_le_two_pow j i
          have h2 : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hjk
          exact_mod_cast h1.trans h2
        have hCnn : (0 : ℝ) ≤ (j.choose i : ℝ) := by positivity
        calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (sa16j_chi d R) x‖ * ‖iteratedFDeriv ℝ (j - i) b x‖
            ≤ 2 ^ k * M * M :=
              mul_le_mul (mul_le_mul hC2 hA1 (norm_nonneg _) (by positivity)) hbd (norm_nonneg _)
                (by positivity)
          _ = 2 ^ k * (M * M) := by ring
  calc ‖iteratedFDeriv ℝ j (fun y => sa16j_chi d R y * b y) x‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (sa16j_chi d R) x‖ *
          ‖iteratedFDeriv ℝ (j - i) b x‖ := hleib
    _ ≤ ∑ i ∈ Finset.range (j + 1), 2 ^ k * (M * M) := Finset.sum_le_sum hterm
    _ = ((j : ℝ) + 1) * (2 ^ k * (M * M)) := by simp
    _ ≤ ((k : ℝ) + 1) * (2 ^ k * (M * M)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : j + 1 ≤ k + 1 := by omega
        exact_mod_cast this
    _ = ((k : ℝ) + 1) * 2 ^ k * (M * M) := by ring

end HRS.Whole.AppendixA.Phase2SA16R
