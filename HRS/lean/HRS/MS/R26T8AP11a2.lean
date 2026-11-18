import HRS.MS.R26T8AP11a1
import HRS.MS.R26T8AG1
import HRS.MS.R26T8AP11lb
import HRS.MS.R26T8AShear4

/-!
# S8.2 T8A packet P11 (helper a2): multiplying a conormal pair function by a smooth function of `x`
`r26t8a_conormal_mul_x`: if `G` is `Conormal k b M σ A` and `a : ℝ^d → ℝ` is `C^k` with all jets of order `≤ k` bounded by `B`, then
`(x, y) ↦ a x * G x y` is `Conormal k b M σ (2^k (k+1)^2 B A)`.  (Coefficient depending on `x = X + z/2`, i.e. on both
`X` and `z`; uses the two-variable nested Leibniz rule and the shear bound for the jets of `a (Y + w/2)`.)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_nest_const_w {p q : ℕ} (hq : q ≠ 0) (a : Euc d → ℝ) (X z : Euc d) :
    r26t8a_nest p q (fun Yw : Euc d × Euc d => a Yw.1) X z = 0 := by
  unfold r26t8a_nest
  have h : (fun Y => iteratedFDeriv ℝ q (fun w : Euc d => a Y) z) =
      fun _ => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ) := by
    funext Y; exact congrFun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := Euc d) hq (a Y)) z
  rw [h]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · ext m; simp
  · have := congrFun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) hp.ne'
      (0 : ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ)) X
    simpa using this

theorem r26t8a_nest_shift_bound {k : ℕ} {a : Euc d → ℝ} (ha : ContDiff ℝ (k : WithTop ℕ∞) a) {B : ℝ}
    (hab : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ B) (hB : 0 ≤ B) {i j : ℕ} (hij : i + j ≤ k) (X z : Euc d) :
    ‖r26t8a_nest i j (fun Yw : Euc d × Euc d => a (Yw.1 + (1 / 2 : ℝ) • Yw.2)) X z‖ ≤ B := by
  set Ψa : Euc d × Euc d → ℝ := fun Yw => a Yw.1 with hΨa
  have hΨ : ContDiff ℝ ((i + j : ℕ) : WithTop ℕ∞) Ψa :=
    (ha.comp contDiff_fst).of_le (by exact_mod_cast hij)
  have h := r26t8a_shear (1 / 2 : ℝ) i j Ψa hΨ X z
  refine h.trans ?_
  rw [Finset.sum_eq_single j]
  · rw [Nat.sub_self, Nat.choose_self, Nat.cast_one, one_mul, r26t8a_nest_zero]
    have : ‖iteratedFDeriv ℝ (i + j) (fun Y => Ψa (Y, z)) (X + (1 / 2 : ℝ) • z)‖ ≤ B := hab _ hij _
    have hl : |(1 / 2 : ℝ)| ^ j ≤ 1 := pow_le_one₀ (abs_nonneg _) (by norm_num [abs_of_pos])
    calc _ ≤ 1 * ‖iteratedFDeriv ℝ (i + j) (fun Y => Ψa (Y, z)) (X + (1 / 2 : ℝ) • z)‖ :=
          mul_le_mul_of_nonneg_right hl (norm_nonneg _)
      _ ≤ B := by rw [one_mul]; exact this
  · intro t ht htj
    have : j - t ≠ 0 := by have := Finset.mem_range.1 ht; omega
    rw [r26t8a_nest_const_w this, norm_zero, mul_zero]
  · intro hj; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self j)) hj

theorem r26t8a_conormal_mul_x {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k b : ℕ} {M σ A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) {a : Euc d → ℝ} (ha : ContDiff ℝ (k : WithTop ℕ∞) a)
    (hab : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ B) {G : Euc d → Euc d → ℝ}
    (hG : Conormal k b M σ A G) :
    Conormal k b M σ (2 ^ k * ((k + 1 : ℝ) ^ 2 * B * A)) (fun x y => a x * G x y) := by
  refine ⟨(ha.comp contDiff_fst).contDiffOn.mul hG.1, fun p q hpq X z hz => ?_⟩
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  set R : ℝ := 2 * ‖z‖ with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  have hρ : 0 < ‖z‖ / 2 := by positivity
  set c : Euc d × Euc d → ℝ := fun Yw => a (Yw.1 + (1 / 2 : ℝ) • Yw.2) with hc
  set Ψ : Euc d × Euc d → ℝ := fun Yw => r26t8a_psiCut chi R Yw.2 * midPair G Yw.1 Yw.2 with hΨ
  have hcd : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) c :=
    (ha.of_le (by exact_mod_cast hpq)).comp (contDiff_fst.add (contDiff_snd.const_smul _))
  have hΨd : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Ψ :=
    (r26t8a_gtilde_contDiff hchi hRpos hG.1).of_le (by exact_mod_cast hpq)
  have e1 : mixedJet p q (fun x y => a x * G x y) X z =
      r26t8a_nest p q (fun Yw => (ContinuousLinearMap.mul ℝ ℝ) (c Yw) (Ψ Yw)) X z := by
    show r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (fun x y => a x * G x y) Yw.1 Yw.2) X z = _
    refine r26t8a_nest_congr_ball p q _ _ hρ X z (fun Y w hw => ?_)
    have h1 : ‖z‖ - ‖w‖ ≤ ‖z - w‖ := norm_sub_norm_le z w
    rw [norm_sub_rev] at h1
    have : R / 4 ≤ ‖w‖ := by rw [hR]; linarith
    simp only [hc, hΨ, r26t8a_psiCut_one hchi hRpos this, one_mul, midPair, ContinuousLinearMap.mul_apply']
  rw [e1]
  have hL := r26t8a_nest_bilinear2 q p (ContinuousLinearMap.mul ℝ ℝ) c Ψ X z hcd hΨd
  have hmn : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  set r : ℝ := min 1 ‖z‖ with hr
  have hr0 : 0 < r := lt_min one_pos hzpos
  have hr1 : r ≤ 1 := min_le_left _ _
  set W : ℝ := pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) with hW
  have hW0 : 0 ≤ W := by
    simp only [hW, pairWeight]
    exact mul_nonneg (Real.rpow_nonneg (HRS.MS.Wad.s83_jb_pos _).le _) (Real.rpow_nonneg (HRS.MS.Wad.s83_jb_pos _).le _)
  set Lg : ℝ := (1 + |Real.log r|) ^ b with hLg
  have hLg0 : 0 ≤ Lg := by positivity
  set En : ℝ := 1 + r ^ (-(σ + (q : ℝ))) * Lg with hEn
  have hEn0 : 0 ≤ En := by positivity
  have hterm : ∀ i ∈ Finset.range (p + 1), ∀ j ∈ Finset.range (q + 1),
      ‖r26t8a_nest i j c X z‖ * ‖r26t8a_nest (p - i) (q - j) Ψ X z‖ ≤ B * (A * W * En) := by
    intro i hi j hj
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    have h1 : ‖r26t8a_nest i j c X z‖ ≤ B :=
      r26t8a_nest_shift_bound ha hab hB (by omega) X z
    have h2 : ‖r26t8a_nest (p - i) (q - j) Ψ X z‖ ≤ A * W * En := by
      rw [hΨ, r26t8a_nest_gtilde hchi hRpos (p - i) (q - j) X z (by rw [hR]; linarith)]
      refine (hG.2 (p - i) (q - j) (by omega) X z hz).trans ?_
      have hq : ((q - j : ℕ) : ℝ) = (q : ℝ) - j := by rw [Nat.cast_sub (by omega)]
      have hpow : r ^ (-(σ + ((q - j : ℕ) : ℝ))) ≤ r ^ (-(σ + (q : ℝ))) := by
        refine Real.rpow_le_rpow_of_exponent_ge hr0 hr1 ?_
        rw [hq]; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith
      have : 1 + r ^ (-(σ + ((q - j : ℕ) : ℝ))) * Lg ≤ En := by
        rw [hEn]; have := mul_le_mul_of_nonneg_right hpow hLg0; linarith
      exact mul_le_mul_of_nonneg_left this (mul_nonneg hA hW0)
    exact mul_le_mul h1 h2 (norm_nonneg _) hB
  have hsum : ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
      ‖r26t8a_nest i j c X z‖ * ‖r26t8a_nest (p - i) (q - j) Ψ X z‖ ≤
      ((p + 1 : ℝ) * (q + 1)) * (B * (A * W * En)) := by
    refine (Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj).trans (le_of_eq ?_)
    simp [Finset.sum_const, Finset.card_range]; ring
  have hp1 : ((p + 1 : ℝ) * (q + 1)) ≤ (k + 1 : ℝ) ^ 2 := by
    have hp : (p : ℝ) ≤ k := by exact_mod_cast (by omega : p ≤ k)
    have hq : (q : ℝ) ≤ k := by exact_mod_cast (by omega : q ≤ k)
    nlinarith [Nat.cast_nonneg (α := ℝ) p, Nat.cast_nonneg (α := ℝ) q]
  have hp2 : (2 : ℝ) ^ (p + q) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hpq
  have hBAWE : 0 ≤ B * (A * W * En) := by positivity
  have h3 : ‖ContinuousLinearMap.mul ℝ ℝ‖ * 2 ^ (p + q) * ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
      ‖r26t8a_nest i j c X z‖ * ‖r26t8a_nest (p - i) (q - j) Ψ X z‖ ≤
      1 * 2 ^ k * (((k + 1 : ℝ) ^ 2) * (B * (A * W * En))) := by
    refine mul_le_mul (mul_le_mul hmn hp2 (by positivity) zero_le_one) (hsum.trans ?_)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right hp1 hBAWE
  have h4 : 1 * 2 ^ k * (((k + 1 : ℝ) ^ 2) * (B * (A * W * En))) =
      2 ^ k * ((k + 1 : ℝ) ^ 2 * B * A) * W * En := by ring
  exact hL.trans (h3.trans (le_of_eq h4))

end HRS.MS.R26T8A
