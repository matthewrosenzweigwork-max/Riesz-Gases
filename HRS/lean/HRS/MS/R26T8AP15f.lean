import HRS.MS.R26T8AP15d

/-!
# S8.2 T8A P15f: product of a conormal pair function with a coefficient of centre/relative regularity
`r26t8a_conormal_mul_gen`: if `c : ℝ^d × ℝ^d → ℝ` is `C^k` with nested jets
`‖nest i j c (X,z)‖ ≤ B * pairWeight m (x,y) * (if j = 0 then (min 1 ‖z‖)^g else 1)` (`g ∈ {0,1}`; `g = 1` means that `c` vanishes on the
diagonal to first order) and `G` is `Conormal k b M σ A`, then `(x,y) ↦ c((x+y)/2, x-y) G(x,y)` is `Conormal k b (M+m) (σ-g) (2^k (k+1)^2 B A)`.
Generalises `r26t8a_conormal_mul_x`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

/-- The pair function `(x,y) ↦ c((x+y)/2, x-y)`. -/
def r26t8a_cpair (c : Euc d × Euc d → ℝ) (x y : Euc d) : ℝ := c ((1 / 2 : ℝ) • (x + y), x - y)

theorem r26t8a_midPair_cpair (c : Euc d × Euc d → ℝ) (Y w : Euc d) :
    midPair (r26t8a_cpair c) Y w = c (Y, w) := by
  show c ((1 / 2 : ℝ) • ((Y + (1 / 2 : ℝ) • w) + (Y - (1 / 2 : ℝ) • w)), (Y + (1 / 2 : ℝ) • w) - (Y - (1 / 2 : ℝ) • w)) = _
  rw [r26t8a_pdir_arg]

theorem r26t8a_pairWeight_add (m M : ℝ) (x y : Euc d) :
    HRS.MS.Phase2S82.pairWeight (M + m) x y =
      HRS.MS.Phase2S82.pairWeight M x y * HRS.MS.Phase2S82.pairWeight m x y := by
  simp only [HRS.MS.Phase2S82.pairWeight]
  rw [Real.rpow_add (s83_jb_pos x), Real.rpow_add (s83_jb_pos y)]
  ring

theorem r26t8a_mul_gen_key {r Lg σ : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hL : 0 ≤ Lg) (g q j : ℕ) (hg : g ≤ 1) (hj : j ≤ q) :
    (if j = 0 then r ^ g else 1) * (1 + r ^ (-(σ + ((q - j : ℕ) : ℝ))) * Lg) ≤
      1 + r ^ (-((σ - g) + (q : ℝ))) * Lg := by
  by_cases hj0 : j = 0
  · subst hj0
    simp only [ite_true, Nat.sub_zero]
    have e : r ^ g * r ^ (-(σ + (q : ℝ))) = r ^ (-((σ - g) + (q : ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr0]
      congr 1; ring
    have h1 : r ^ g ≤ 1 := pow_le_one₀ hr0.le hr1
    calc r ^ g * (1 + r ^ (-(σ + (q : ℝ))) * Lg) = r ^ g + (r ^ g * r ^ (-(σ + (q : ℝ)))) * Lg := by ring
      _ ≤ 1 + r ^ (-((σ - g) + (q : ℝ))) * Lg := by rw [e]; linarith
  · simp only [hj0, ite_false, one_mul]
    have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.2 hj0
    have hq : ((q - j : ℕ) : ℝ) = (q : ℝ) - j := by rw [Nat.cast_sub hj]
    have hp : r ^ (-(σ + ((q - j : ℕ) : ℝ))) ≤ r ^ (-((σ - g) + (q : ℝ))) := by
      refine Real.rpow_le_rpow_of_exponent_ge hr0 hr1 ?_
      rw [hq]
      have : (g : ℝ) ≤ 1 := by exact_mod_cast hg
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      linarith
    have := mul_le_mul_of_nonneg_right hp hL
    linarith

set_option maxHeartbeats 3200000 in
theorem r26t8a_conormal_mul_gen {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k b : ℕ} {M σ A B m : ℝ} (g : ℕ)
    (hg : g ≤ 1) (hA : 0 ≤ A) (hB : 0 ≤ B) {c : Euc d × Euc d → ℝ} (hc : ContDiff ℝ (k : WithTop ℕ∞) c)
    (hcb : ∀ i j : ℕ, i + j ≤ k → ∀ X z : Euc d, z ≠ 0 →
      ‖r26t8a_nest i j c X z‖ ≤ B * HRS.MS.Phase2S82.pairWeight m (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
        (if j = 0 then (min 1 ‖z‖) ^ g else 1))
    {G : Euc d → Euc d → ℝ} (hG : Conormal k b M σ A G) :
    Conormal k b (M + m) (σ - g) (2 ^ k * ((k + 1 : ℝ) ^ 2 * B * A)) (fun x y => r26t8a_cpair c x y * G x y) := by
  have hL : ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => ((1 / 2 : ℝ) • (p.1 + p.2), p.1 - p.2)) :=
    ((contDiff_fst.add contDiff_snd).const_smul (1 / 2 : ℝ)).prodMk (contDiff_fst.sub contDiff_snd)
  refine ⟨(hc.comp hL).contDiffOn.mul hG.1, fun p q hpq X z hz => ?_⟩
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  set R : ℝ := 2 * ‖z‖ with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  have hρ : 0 < ‖z‖ / 2 := by positivity
  set Ψ : Euc d × Euc d → ℝ := fun Yw => r26t8a_psiCut chi R Yw.2 * midPair G Yw.1 Yw.2 with hΨ
  have hcd : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) c := hc.of_le (by exact_mod_cast hpq)
  have hΨd : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Ψ :=
    (r26t8a_gtilde_contDiff hchi hRpos hG.1).of_le (by exact_mod_cast hpq)
  have e1 : mixedJet p q (fun x y => r26t8a_cpair c x y * G x y) X z =
      r26t8a_nest p q (fun Yw => (ContinuousLinearMap.mul ℝ ℝ) (c Yw) (Ψ Yw)) X z := by
    show r26t8a_nest p q (fun Yw : Euc d × Euc d =>
      midPair (fun x y => r26t8a_cpair c x y * G x y) Yw.1 Yw.2) X z = _
    refine r26t8a_nest_congr_ball p q _ _ hρ X z (fun Y w hw => ?_)
    have h1 : ‖z‖ - ‖w‖ ≤ ‖z - w‖ := norm_sub_norm_le z w
    rw [norm_sub_rev] at h1
    have : R / 4 ≤ ‖w‖ := by rw [hR]; linarith
    have hmc := r26t8a_midPair_cpair c Y w
    simp only [hΨ, r26t8a_psiCut_one hchi hRpos this, one_mul, ContinuousLinearMap.mul_apply']
    rw [← hmc]
    rfl
  rw [e1]
  have hL2 := r26t8a_nest_bilinear2 q p (ContinuousLinearMap.mul ℝ ℝ) c Ψ X z hcd hΨd
  have hmn : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  set r : ℝ := min 1 ‖z‖ with hr
  have hr0 : 0 < r := lt_min one_pos hzpos
  have hr1 : r ≤ 1 := min_le_left _ _
  set W : ℝ := HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) with hW
  set Wm : ℝ := HRS.MS.Phase2S82.pairWeight m (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) with hWm
  have hW0 : 0 ≤ W := r26t8a_pairWeight_nonneg _ _ _
  have hWm0 : 0 ≤ Wm := r26t8a_pairWeight_nonneg _ _ _
  set Lg : ℝ := (1 + |Real.log r|) ^ b with hLg
  have hLg0 : 0 ≤ Lg := by positivity
  set En : ℝ := 1 + r ^ (-((σ - g) + (q : ℝ))) * Lg with hEn
  have hEn0 : 0 ≤ En := by positivity
  have hterm : ∀ i ∈ Finset.range (p + 1), ∀ j ∈ Finset.range (q + 1),
      ‖r26t8a_nest i j c X z‖ * ‖r26t8a_nest (p - i) (q - j) Ψ X z‖ ≤ B * Wm * (A * W * En) := by
    intro i hi j hj
    have hi' := Finset.mem_range.1 hi
    have hj' := Finset.mem_range.1 hj
    have h1 := hcb i j (by omega) X z hz
    have h2 : ‖r26t8a_nest (p - i) (q - j) Ψ X z‖ ≤ A * W * (1 + r ^ (-(σ + ((q - j : ℕ) : ℝ))) * Lg) := by
      rw [hΨ, r26t8a_nest_gtilde hchi hRpos (p - i) (q - j) X z (by rw [hR]; linarith)]
      exact hG.2 (p - i) (q - j) (by omega) X z hz
    have hkey := r26t8a_mul_gen_key (σ := σ) (Lg := Lg) hr0 hr1 hLg0 g q j hg (by omega)
    have hnn : 0 ≤ B * Wm * (if j = 0 then r ^ g else 1) := by
      have : 0 ≤ (if j = 0 then r ^ g else 1 : ℝ) := by split_ifs <;> positivity
      positivity
    calc ‖r26t8a_nest i j c X z‖ * ‖r26t8a_nest (p - i) (q - j) Ψ X z‖
        ≤ (B * Wm * (if j = 0 then r ^ g else 1)) * (A * W * (1 + r ^ (-(σ + ((q - j : ℕ) : ℝ))) * Lg)) :=
          mul_le_mul h1 h2 (norm_nonneg _) hnn
      _ = B * Wm * (A * W) * ((if j = 0 then r ^ g else 1) * (1 + r ^ (-(σ + ((q - j : ℕ) : ℝ))) * Lg)) := by ring
      _ ≤ B * Wm * (A * W) * En := mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = B * Wm * (A * W * En) := by ring
  have hsum : ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
      ‖r26t8a_nest i j c X z‖ * ‖r26t8a_nest (p - i) (q - j) Ψ X z‖ ≤
      ((p + 1 : ℝ) * (q + 1)) * (B * Wm * (A * W * En)) := by
    refine (Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj).trans (le_of_eq ?_)
    simp [Finset.sum_const, Finset.card_range]; ring
  have hp1 : ((p + 1 : ℝ) * (q + 1)) ≤ (k + 1 : ℝ) ^ 2 := by
    have hp : (p : ℝ) ≤ k := by exact_mod_cast (by omega : p ≤ k)
    have hq : (q : ℝ) ≤ k := by exact_mod_cast (by omega : q ≤ k)
    nlinarith [Nat.cast_nonneg (α := ℝ) p, Nat.cast_nonneg (α := ℝ) q]
  have hp2 : (2 : ℝ) ^ (p + q) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hpq
  have hBAWE : 0 ≤ B * Wm * (A * W * En) := by positivity
  have h3 : ‖ContinuousLinearMap.mul ℝ ℝ‖ * 2 ^ (p + q) * ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
      ‖r26t8a_nest i j c X z‖ * ‖r26t8a_nest (p - i) (q - j) Ψ X z‖ ≤
      1 * 2 ^ k * (((k + 1 : ℝ) ^ 2) * (B * Wm * (A * W * En))) := by
    refine mul_le_mul (mul_le_mul hmn hp2 (by positivity) zero_le_one) (hsum.trans ?_)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right hp1 hBAWE
  have h4 : 1 * 2 ^ k * (((k + 1 : ℝ) ^ 2) * (B * Wm * (A * W * En))) =
      2 ^ k * ((k + 1 : ℝ) ^ 2 * B * A) * (HRS.MS.Phase2S82.pairWeight (M + m) (X + (1 / 2 : ℝ) • z)
        (X - (1 / 2 : ℝ) • z)) * En := by
    rw [r26t8a_pairWeight_add]; ring
  exact hL2.trans (h3.trans (le_of_eq h4))

end HRS.MS.R26T8A
