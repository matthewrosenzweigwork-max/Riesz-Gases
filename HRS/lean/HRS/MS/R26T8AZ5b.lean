import HRS.MS.R26T8AZ5a3
import HRS.MS.R26T8AN5

/-!
# S8.2 T8A Z5b: the Newton potential of a conormal function that vanishes near the diagonal
`r26t8a_Z5b_smooth`: `Conormal k b M σ A P`, `P(x,y) = 0` for `|x-y| ≤ 1/4`: `P` is `C^k`, the Newton integrand is integrable and
`rawNewton P` is `Conormal k (b+1) M (σ-2) (C A)` (a smooth function with weighted bounded jets).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_Z5b_rpow_le {r : ℝ} (hr1 : 1 / 4 ≤ r) (hr2 : r ≤ 1) (e : ℝ) : r ^ e ≤ 4 ^ |e| := by
  have hr0 : 0 < r := by linarith
  rcases le_total 0 e with he | he
  · rw [abs_of_nonneg he]
    exact (Real.rpow_le_one hr0.le hr2 he).trans (Real.one_le_rpow (by norm_num) he)
  · rw [abs_of_nonpos he]
    have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 4) hr1 he
    refine h.trans (le_of_eq ?_)
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]

theorem r26t8a_Z5b_smooth (hd : 2 ≤ d) (k b : ℕ) (nu M σ : ℝ) (hnu : 0 < nu) (hM : 0 ≤ M)
    {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal k b M σ A P →
      (∀ x y : Euc d, ‖x - y‖ ≤ 1 / 4 → P x y = 0) →
      (∀ x y : Euc d, Integrable (fun z => newtonKernel d nu (x - y - z) * chi z *
        midPair P ((1 / 2 : ℝ) • (x + y)) z)) ∧
      Conormal k (b + 1) M (σ - 2) (C * A) (rawNewton nu chi P) := by
  obtain ⟨Cq, hCq0, hCq⟩ := r26t8a_rawNewton_smooth_jets hd k nu M hM hchi
  set Kc : ℝ := 1 + 4 ^ (|σ| + (k : ℝ)) * 4 ^ b with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  refine ⟨Cq * Kc, by positivity, fun P A hA hP hz0 => ?_⟩
  have hpw0 : ∀ X z : Euc d, 0 ≤ HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) :=
    fun X z => r26t8a_pairWeight_nonneg M _ _
  have hPcd : ContDiff ℝ (k : WithTop ℕ∞) (Function.uncurry P) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p.1 = p.2
    · have hev : Function.uncurry P =ᶠ[𝓝 p] fun _ => 0 := by
        have hopen : IsOpen {q : Euc d × Euc d | ‖q.1 - q.2‖ < 1 / 4} :=
          isOpen_lt (continuous_norm.comp (continuous_fst.sub continuous_snd)) continuous_const
        filter_upwards [hopen.mem_nhds (by simp [hp])] with q hq
        exact hz0 q.1 q.2 (le_of_lt hq)
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hopen : IsOpen {q : Euc d × Euc d | q.1 ≠ q.2} := isOpen_ne_fun continuous_fst continuous_snd
      exact hP.1.contDiffAt (hopen.mem_nhds hp)
  have hjets : ∀ p q : ℕ, p + q ≤ k → ∀ X z : Euc d,
      ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair P Yw.1 Yw.2) X z‖ ≤
        (Kc * A) * HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
    intro p q hpq X z
    have hnn : 0 ≤ (Kc * A) * HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) :=
      mul_nonneg (mul_nonneg hKc0 hA) (hpw0 X z)
    by_cases hz : ‖z‖ < 1 / 4
    · have h0 : r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair P Yw.1 Yw.2) X z =
          r26t8a_nest p q (fun _ : Euc d × Euc d => (0 : ℝ)) X z := by
        refine r26t8a_nest_congr_ball p q _ _ (ρ := 1 / 4 - ‖z‖) (by linarith) X z (fun Y w hw => ?_)
        have hwn : ‖w‖ < 1 / 4 := by
          have := norm_le_norm_add_norm_sub' w z
          linarith
        have e : (Y + (1 / 2 : ℝ) • w) - (Y - (1 / 2 : ℝ) • w) = w := by module
        exact hz0 _ _ (by rw [e]; exact hwn.le)
      have e0 : r26t8a_nest p q (fun _ : Euc d × Euc d => (0 : ℝ)) X z = 0 := by
        unfold r26t8a_nest; simp [iteratedFDeriv_fun_zero]
      rw [h0, e0, norm_zero]; exact hnn
    · push Not at hz
      have hz' : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith
      have hb := hP.2 p q hpq X z hz'
      have hr1 : 1 / 4 ≤ min 1 ‖z‖ := le_min (by norm_num) hz
      have hr2 : min 1 ‖z‖ ≤ 1 := min_le_left _ _
      have h1 := r26t8a_Z5b_rpow_le hr1 hr2 (-(σ + (q : ℝ)))
      have h2 : |-(σ + (q : ℝ))| ≤ |σ| + k := by
        rw [abs_neg]
        calc |σ + (q : ℝ)| ≤ |σ| + |(q : ℝ)| := abs_add_le _ _
          _ ≤ |σ| + k := by
            have hq0 : |(q : ℝ)| = q := abs_of_nonneg (Nat.cast_nonneg q)
            rw [hq0]
            have : (q : ℝ) ≤ k := by exact_mod_cast (by omega : q ≤ k)
            linarith
      have h3 : (4 : ℝ) ^ |-(σ + (q : ℝ))| ≤ 4 ^ (|σ| + (k : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
      have hL : (1 + |Real.log (min 1 ‖z‖)|) ^ b ≤ 4 ^ b := by
        refine pow_le_pow_left₀ (by positivity) ?_ b
        have hlog : |Real.log (min 1 ‖z‖)| ≤ Real.log 4 := by
          rw [abs_le]; constructor
          · have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) hr1
            rw [one_div, Real.log_inv] at this; linarith
          · have := Real.log_le_log (by linarith : (0 : ℝ) < min 1 ‖z‖) hr2
            rw [Real.log_one] at this
            linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
        have : Real.log 4 ≤ 3 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
        linarith
      have h4 : (min 1 ‖z‖) ^ (-(σ + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b ≤ 4 ^ (|σ| + (k : ℝ)) * 4 ^ b :=
        mul_le_mul (h1.trans h3) hL (by positivity) (by positivity)
      refine hb.trans ?_
      have hw := hpw0 X z
      calc A * HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
            (1 + (min 1 ‖z‖) ^ (-(σ + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b)
          ≤ A * HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) * Kc :=
            mul_le_mul_of_nonneg_left (by rw [hKc]; linarith) (mul_nonneg hA hw)
        _ = _ := by ring
  have hLPsm := r26t8a_N5_rawNewton_contDiff hd k nu hchi hPcd
  refine ⟨fun x y => ?_, ?_⟩
  · have hg : Continuous (fun z : Euc d => chi z * midPair P ((1 / 2 : ℝ) • (x + y)) z) := by
      refine hchi.1.continuous.mul ?_
      unfold midPair
      have hcz : Continuous (fun z : Euc d => ((1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • z,
          (1 / 2 : ℝ) • (x + y) - (1 / 2 : ℝ) • z)) := by fun_prop
      exact hPcd.continuous.comp hcz
    have hcs : HasCompactSupport (fun z : Euc d => chi z * midPair P ((1 / 2 : ℝ) • (x + y)) z) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) 2) (fun z hz => ?_)
      have : 2 < ‖z‖ := by simpa using hz
      simp [hchi.2.2.2.2 z this.le]
    have := r26t8a_N5_integrable hd nu hg hcs (x - y)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [mul_assoc]
  · refine And.intro hLPsm.contDiffOn fun p q hpq X z hz => ?_
    have h := hCq (Kc * A) (mul_nonneg hKc0 hA) P hPcd hjets p q hpq X z
    show ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (rawNewton nu chi P) Yw.1 Yw.2) X z‖ ≤ _
    refine h.trans ?_
    have h0 : 0 ≤ Cq * (Kc * A) * HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
      have := hpw0 X z; positivity
    have h1 : 0 ≤ (min 1 ‖z‖) ^ (-((σ - 2) + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ (b + 1) := by
      have : 0 ≤ min 1 ‖z‖ := le_min zero_le_one (norm_nonneg _)
      positivity
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + (min 1 ‖z‖) ^ (-((σ - 2) + (q : ℝ))) *
      (1 + |Real.log (min 1 ‖z‖)|) ^ (b + 1) by linarith) h0
    calc _ = Cq * (Kc * A) * HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) * 1 := by
          ring
      _ ≤ Cq * Kc * A * HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
          (1 + (min 1 ‖z‖) ^ (-((σ - 2) + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ (b + 1)) := by
          calc _ ≤ _ := this
            _ = _ := by ring

end HRS.MS.R26T8A
