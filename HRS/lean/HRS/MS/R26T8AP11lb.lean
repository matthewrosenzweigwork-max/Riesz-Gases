import HRS.MS.R26T8AP11sn
import HRS.MS.R26T8AP11b4
import HRS.MS.R26T8AP01b

/-!
# S8.2 nonlocal layer: Leibniz in the relative variable for the outer cutoff (P11e, part 4)
`midPair localRiesz = chi(w) * Sfun`; `Sfun` is `C^k` off `w = 0` (`r26t8a_locInt_contDiffOn`), so after a cutoff
`theta(w) = 1 - chi(c w)` away from `0` the product bound `r26t8a_nest_product_bound` gives
`‖nest p q (midPair localRiesz) X z‖ <= Σ_i C(q,i) ‖D^i chi z‖ ‖nest p (q-i) Sfun X z‖` for every `z ≠ 0`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_nest_congr_ball {d : ℕ} (p q : ℕ) (Φ Φ' : Euc d × Euc d → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (X z : Euc d)
    (hΦ : ∀ Y w : Euc d, ‖w - z‖ < ρ → Φ (Y, w) = Φ' (Y, w)) :
    r26t8a_nest p q Φ X z = r26t8a_nest p q Φ' X z := by
  unfold r26t8a_nest
  have h : ∀ Y : Euc d, iteratedFDeriv ℝ q (fun w => Φ (Y, w)) z = iteratedFDeriv ℝ q (fun w => Φ' (Y, w)) z := by
    intro Y
    have hev : (fun w => Φ (Y, w)) =ᶠ[𝓝 z] fun w => Φ' (Y, w) := by
      filter_upwards [ball_mem_nhds z hρ] with w hw
      exact hΦ Y w (by simpa [dist_eq_norm] using hw)
    exact (hev.iteratedFDeriv ℝ q).self_of_nhds
  simp only [h]

theorem r26t8a_Sfun_eq_midPair {d : ℕ} (alpha : ℝ) (chi : Euc d → ℝ) (F : Euc d → Euc d → ℝ) (Y w : Euc d) :
    r26t8a_Sfun alpha chi F Y w = midPair (fun x y : Euc d => ∫ v : Euc d,
      ‖x - y - v‖ ^ (alpha - (d : ℝ)) * chi v * F (y + v) y) Y w := by
  unfold r26t8a_Sfun midPair
  beta_reduce
  have e1 : Y + (1 / 2 : ℝ) • w - (Y - (1 / 2 : ℝ) • w) = w := by module
  have e2 : Y - (1 / 2 : ℝ) • w = Y + (-(1 / 2 : ℝ)) • w := by module
  rw [e1, e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  ring

theorem r26t8a_Sfun_contDiffOn (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (A : ℝ) (hA : 0 ≤ A) (F : Euc d → Euc d → ℝ)
    (hF : Conormal k b M sigma A F) :
    ContDiffOn ℝ k (fun Yw : Euc d × Euc d => r26t8a_Sfun alpha chi F Yw.1 Yw.2) {Yw : Euc d × Euc d | Yw.2 ≠ 0} := by
  have h := r26t8a_midPair_contDiffOn (k := k)
    (F := fun x y : Euc d => ∫ v : Euc d, ‖x - y - v‖ ^ (alpha - (d : ℝ)) * chi v * F (y + v) y)
    (r26t8a_locInt_contDiffOn d hd k b alpha M sigma halpha had hM hsd chi hchi A hA F hF)
  exact h.congr (fun Yw _ => r26t8a_Sfun_eq_midPair alpha chi F Yw.1 Yw.2)

theorem r26t8a_Gtil_contDiff {d : ℕ} (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) {c : ℝ} (hc : 0 < c)
    (S : Euc d × Euc d → ℝ) {n : ℕ} (hS : ContDiffOn ℝ n S {Yw : Euc d × Euc d | Yw.2 ≠ 0}) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun Yw : Euc d × Euc d => (1 - chi (c • Yw.2)) * S Yw) := by
  have hchic : ContDiff ℝ (n : WithTop ℕ∞) chi := hchi.1.of_le (by exact_mod_cast le_top)
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hs : ‖x.2‖ < 1 / c
  · have hev : (fun Yw : Euc d × Euc d => (1 - chi (c • Yw.2)) * S Yw) =ᶠ[𝓝 x] fun _ => 0 := by
      have hopen : IsOpen {y : Euc d × Euc d | ‖y.2‖ < 1 / c} :=
        isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
      filter_upwards [hopen.mem_nhds hs] with y hy
      have hy' : ‖y.2‖ < 1 / c := hy
      have h1 : ‖c • y.2‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg hc.le]
        rw [lt_div_iff₀ hc] at hy'
        nlinarith
      rw [hchi.2.2.2.1 _ h1]
      ring
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · push Not at hs
    have hne : x.2 ≠ 0 := by
      intro h; rw [h, norm_zero] at hs
      have : (0 : ℝ) < 1 / c := by positivity
      linarith
    have hopen : IsOpen {Yw : Euc d × Euc d | Yw.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
    exact ((contDiff_const.sub (hchic.comp (contDiff_snd.const_smul c))).contDiffAt).mul
      (hS.contDiffAt (hopen.mem_nhds hne))

theorem r26t8a_mid_nest_leibniz (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (A : ℝ) (hA : 0 ≤ A) (F : Euc d → Euc d → ℝ)
    (hF : Conormal k b M sigma A F) (X z : Euc d) (hz : z ≠ 0) (p q : ℕ) (hpq : p + q ≤ k) :
    ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (r26t8a_localRiesz alpha chi F) Yw.1 Yw.2) X z‖ ≤
      ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i chi z‖ *
        ‖r26t8a_nest p (q - i) (fun Yw : Euc d × Euc d => r26t8a_Sfun alpha chi F Yw.1 Yw.2) X z‖ := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  set c : ℝ := 8 / ‖z‖ with hcd
  have hc : 0 < c := by positivity
  have hS := r26t8a_Sfun_contDiffOn d hd k b alpha M sigma halpha had hM hsd chi hchi A hA F hF
  have hG : ContDiff ℝ (k : WithTop ℕ∞) (fun Yw : Euc d × Euc d => (1 - chi (c • Yw.2)) *
      r26t8a_Sfun alpha chi F Yw.1 Yw.2) :=
    r26t8a_Gtil_contDiff chi hchi hc (fun Yw => r26t8a_Sfun alpha chi F Yw.1 Yw.2) hS
  have hG' : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d => (1 - chi (c • Yw.2)) *
      r26t8a_Sfun alpha chi F Yw.1 Yw.2) := hG.of_le (by exact_mod_cast hpq)
  have hchic : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) chi := hchi.1.of_le (by exact_mod_cast le_top)
  -- theta = 1 near z
  have hθ : ∀ w : Euc d, ‖w - z‖ < ‖z‖ / 2 → 1 - chi (c • w) = 1 := by
    intro w hw
    have h1 : ‖z‖ - ‖w‖ ≤ ‖z - w‖ := norm_sub_norm_le z w
    rw [norm_sub_rev] at h1
    have h2 : 2 ≤ ‖c • w‖ := by
      rw [norm_smul, Real.norm_of_nonneg hc.le, hcd, div_mul_eq_mul_div, le_div_iff₀ hzpos]
      nlinarith
    rw [hchi.2.2.2.2 _ h2]; ring
  have hρ : 0 < ‖z‖ / 2 := by positivity
  have e1 : r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (r26t8a_localRiesz alpha chi F) Yw.1 Yw.2) X z =
      r26t8a_nest p q (fun Yw : Euc d × Euc d => chi Yw.2 * ((1 - chi (c • Yw.2)) *
        r26t8a_Sfun alpha chi F Yw.1 Yw.2)) X z := by
    refine r26t8a_nest_congr_ball p q _ _ hρ X z (fun Y w hw => ?_)
    simp only
    rw [hθ w hw, one_mul, r26t8a_pu_midPair_localRiesz]
    rfl
  rw [e1]
  refine (r26t8a_nest_product_bound p q chi _ X z hchic hG').trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [r26t8a_nest_congr_ball p (q - i) (fun Yw : Euc d × Euc d => (1 - chi (c • Yw.2)) *
      r26t8a_Sfun alpha chi F Yw.1 Yw.2) (fun Yw : Euc d × Euc d => r26t8a_Sfun alpha chi F Yw.1 Yw.2) hρ X z
      (fun Y w hw => by simp only; rw [hθ w hw, one_mul])]

end HRS.MS.R26T8A
