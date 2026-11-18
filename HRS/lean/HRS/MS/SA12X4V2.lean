import HRS.MS.SA12X4V1
import HRS.MS.SA12X3C10E

/-!
# S.A.12 (SA12X4) V2: the continuous weighted jet energy versus `varpiNormE`

`sa12x4_varpi_le_J`: `‖u‖²_{H^m(ϖ)} ≤ K ∫ ϖ Z_m(u)` and `sa12x4_J_le_varpi`: `∫ ϖ Z_m(u) ≤ K ‖u‖²_{H^m(ϖ)}`
(both for smooth `u`; local Leibniz bound `sa12x3_stat_pt` and the equality `χ(· - c) u = u` on `B(c,1)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X4

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12
  HRS.MH.AdjointRd.Phase2SA12Near HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x4_varpi_sq (m : ℕ) (χ u : Euc d → ℝ) :
    varpiNormE m χ u ^ 2 = ∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
      sobolevNormE (m : ℝ) (fun x => χ (x - cellPt d z) * u x) ^ 2 := by
  unfold varpiNormE
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- The weighted ball count: `∑_y ω_y 1[‖x - y‖ ≤ R] ≤ K ϖ(x)`. -/
theorem sa12x4_ball_sum_le (hd : 1 ≤ d) (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Euc d, ∑' y, ENNReal.ofReal (jbracket (cellPt d y) ^ (-((d : ℝ) + 3))) *
      (closedBall (cellPt d y) R).indicator (fun _ => (1 : ℝ≥0∞)) x ≤
        ENNReal.ofReal K * ENNReal.ofReal (jbracket x ^ (-((d : ℝ) + 3))) := by
  classical
  obtain ⟨N, hN⟩ := sa12x4_lattice_count hd R
  set p : ℝ := (d : ℝ) + 3 with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  set Cw : ℝ := (Real.sqrt 2 * Real.sqrt (1 + R ^ 2)) ^ p with hCw
  have hCw0 : 0 ≤ Cw := Real.rpow_nonneg (by positivity) _
  refine ⟨N * Cw, by positivity, fun x => ?_⟩
  obtain ⟨S, hSc, hS⟩ := hN x
  have hzero : ∀ y ∉ S, ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) *
      (closedBall (cellPt d y) R).indicator (fun _ => (1 : ℝ≥0∞)) x = 0 := by
    intro y hy
    have hfar : x ∉ closedBall (cellPt d y) R := by
      intro h
      rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at h
      exact hy (hS y h)
    rw [indicator_of_notMem hfar]; simp
  rw [tsum_eq_sum hzero]
  have hterm : ∀ y ∈ S, ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) *
      (closedBall (cellPt d y) R).indicator (fun _ => (1 : ℝ≥0∞)) x ≤
      ENNReal.ofReal Cw * ENNReal.ofReal (jbracket x ^ (-p)) := by
    intro y _
    by_cases hx : x ∈ closedBall (cellPt d y) R
    · rw [indicator_of_mem hx, mul_one]
      have hnear : ‖x - cellPt d y‖ ≤ R := by
        rw [mem_closedBall, dist_eq_norm] at hx; exact hx
      have hc := sa12x4_varpi_comp p hp0 R x (cellPt d y) hnear
      calc ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) ≤ ENNReal.ofReal (Cw * jbracket x ^ (-p)) :=
            ENNReal.ofReal_le_ofReal hc
        _ = _ := ENNReal.ofReal_mul hCw0
    · rw [indicator_of_notMem hx]; simp
  calc ∑ y ∈ S, ENNReal.ofReal (jbracket (cellPt d y) ^ (-p)) *
        (closedBall (cellPt d y) R).indicator (fun _ => (1 : ℝ≥0∞)) x
      ≤ ∑ _y ∈ S, ENNReal.ofReal Cw * ENNReal.ofReal (jbracket x ^ (-p)) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ≥0∞) * (ENNReal.ofReal Cw * ENNReal.ofReal (jbracket x ^ (-p))) := by simp
    _ ≤ (N : ℝ≥0∞) * (ENNReal.ofReal Cw * ENNReal.ofReal (jbracket x ^ (-p))) := by gcongr
    _ = ENNReal.ofReal (N * Cw) * ENNReal.ofReal (jbracket x ^ (-p)) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]


theorem sa12x4_Y_le_Z (m : ℕ) (u : Euc d → ℝ) (x : Euc d) : sa12z3_Y m u x ≤ sa12x4_Z m u x := by
  unfold sa12z3_Y sa12x4_Z
  refine Finset.sum_le_sum fun n hn => ?_
  have hc : (1 : ℝ) ≤ (Nat.choose m n : ℝ) := by
    have : 1 ≤ Nat.choose m n := Nat.choose_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))
    exact_mod_cast this
  have h0 : 0 ≤ ∑ idx : Fin n → Fin d, (partialDeriv idx u x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

theorem sa12x4_Z_le_Y (m : ℕ) (u : Euc d → ℝ) (x : Euc d) : sa12x4_Z m u x ≤ 2 ^ m * sa12z3_Y m u x := by
  unfold sa12z3_Y sa12x4_Z
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hc : (Nat.choose m n : ℝ) ≤ 2 ^ m := by exact_mod_cast Nat.choose_le_two_pow m n
  have h0 : 0 ≤ ∑ idx : Fin n → Fin d, (partialDeriv idx u x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact mul_le_mul_of_nonneg_right hc h0

theorem sa12x4_varpi_le_J (hd : 1 ≤ d) (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {u : Euc d → ℝ}, ContDiff ℝ ∞ u → varpiNormE m χ u ^ 2 ≤ ENNReal.ofReal K * sa12x4_J m u := by
  classical
  obtain ⟨B1, hB10, hB1⟩ := sa12x3_stat_B m hχ.1 hχ.2.1
  obtain ⟨Kb, hKb0, hKb⟩ := sa12x4_ball_sum_le hd 2
  set Kp : ℝ := B1 ^ 2 * 4 ^ m * ((m : ℝ) + 1) ^ 2 * (d : ℝ) ^ m with hKp
  have hKp0 : 0 ≤ Kp := by positivity
  set M0 : ℝ := ∑ n ∈ Finset.range (m + 1), (d : ℝ) ^ n with hM0
  have hM00 : 0 ≤ M0 := Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨2 ^ m * (M0 * Kp) * Kb, by positivity, fun {u} hu => ?_⟩
  set f : (Fin d → ℤ) → Euc d → ℝ := fun c y => χ (y - cellPt d c) * u y with hf
  have hfC : ∀ c, ContDiff ℝ ∞ (f c) := fun c => (hχ.1.comp (contDiff_id.sub contDiff_const)).mul hu
  have hfc : ∀ c, HasCompactSupport (f c) := fun c => by
    have : HasCompactSupport (fun y => χ (y - cellPt d c)) := hχ.2.1.comp_homeomorph (Homeomorph.subRight _)
    exact this.mul_right
  have hYm : Measurable (sa12z3_Y m u) := by
    unfold sa12z3_Y
    refine Finset.measurable_sum _ fun r _ => Finset.measurable_sum _ fun γ _ => ?_
    exact ((sa12z3_pd_contDiff_inf hu γ).continuous.measurable).pow_const 2
  set I : (Fin d → ℤ) → ℝ≥0∞ := fun c => ∫⁻ x in closedBall (cellPt d c) 2, ENNReal.ofReal (sa12z3_Y m u x) with hI
  have hsqi : ∀ c, ∀ {n : ℕ} (idx : Fin n → Fin d), Integrable (fun x => (partialDeriv idx (f c) x) ^ 2) := fun c n idx =>
    Continuous.integrable_of_hasCompactSupport (f := fun x => (partialDeriv idx (f c) x) ^ 2)
      ((sa12z3_pd_contDiff_inf (hfC c) idx).continuous.pow 2)
      ((sa12z3_pd_compact (hfc c) idx).comp_left (g := fun t : ℝ => t ^ 2) (by simp))
  have hterm : ∀ c, ∀ n ∈ Finset.range (m + 1), ∀ idx : Fin n → Fin d,
      ENNReal.ofReal (∫ x, (partialDeriv idx (f c) x) ^ 2) ≤ ENNReal.ofReal Kp * I c := by
    intro c n hn idx
    have hnm : n ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    rw [ofReal_integral_eq_lintegral_ofReal (hsqi c idx) (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    calc ∫⁻ x, ENNReal.ofReal ((partialDeriv idx (f c) x) ^ 2)
        ≤ ∫⁻ x, ENNReal.ofReal Kp * (closedBall (cellPt d c) 2).indicator
            (fun x => ENNReal.ofReal (sa12z3_Y m u x)) x := by
          refine lintegral_mono fun x => ?_
          have h := sa12x3_stat_pt hd hχ.1 hχ.2.2.1 hB10 (cellPt d c) (fun i hi y => hB1 _ i hi y) hu hnm idx x
          by_cases hx : x ∈ closedBall (cellPt d c) 2
          · rw [indicator_of_mem hx]
            rw [if_pos hx] at h
            calc ENNReal.ofReal ((partialDeriv idx (f c) x) ^ 2) ≤ ENNReal.ofReal (Kp * sa12z3_Y m u x) :=
                  ENNReal.ofReal_le_ofReal (by simpa [hKp, mul_assoc] using h)
              _ = _ := ENNReal.ofReal_mul hKp0
          · rw [indicator_of_notMem hx]
            rw [if_neg hx] at h
            simp only [mul_zero] at h
            simp only [mul_zero]
            have : (partialDeriv idx (f c) x) ^ 2 ≤ 0 := by simpa [hKp] using h
            exact (ENNReal.ofReal_le_ofReal this).trans (by simp)
      _ = ENNReal.ofReal Kp * I c := by
          rw [lintegral_const_mul _ (hYm.ennreal_ofReal.indicator measurableSet_closedBall), lintegral_indicator measurableSet_closedBall]
  have hJraw : ∀ c, ENNReal.ofReal (sa12x3_Jraw m (f c)) ≤ ENNReal.ofReal (M0 * Kp) * I c := by
    intro c
    unfold sa12x3_Jraw
    rw [ENNReal.ofReal_sum_of_nonneg fun n _ => Finset.sum_nonneg fun idx _ => integral_nonneg fun x => sq_nonneg _]
    calc ∑ n ∈ Finset.range (m + 1), ENNReal.ofReal (∑ idx : Fin n → Fin d, ∫ x, (partialDeriv idx (f c) x) ^ 2)
        ≤ ∑ n ∈ Finset.range (m + 1), ((d : ℝ≥0∞) ^ n * (ENNReal.ofReal Kp * I c)) := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [ENNReal.ofReal_sum_of_nonneg fun idx _ => integral_nonneg fun x => sq_nonneg _]
          calc ∑ idx : Fin n → Fin d, ENNReal.ofReal (∫ x, (partialDeriv idx (f c) x) ^ 2)
              ≤ ∑ _idx : Fin n → Fin d, ENNReal.ofReal Kp * I c := Finset.sum_le_sum fun idx _ => hterm c n hn idx
            _ = (d : ℝ≥0∞) ^ n * (ENNReal.ofReal Kp * I c) := by simp
      _ = ENNReal.ofReal (M0 * Kp) * I c := by
          rw [ENNReal.ofReal_mul hM00, hM0, ENNReal.ofReal_sum_of_nonneg fun n _ => by positivity, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast, mul_assoc]
  have hsob : ∀ c, sobolevNormE (m : ℝ) (f c) ^ 2 ≤ ENNReal.ofReal (2 ^ m * (M0 * Kp)) * I c := by
    intro c
    refine (sa12x3_sob_jet m (sa12z3_cd_of_inf (hfC c) m) (hfc c)).1.trans ?_
    have e1 : ENNReal.ofReal (2 ^ m * sa12x3_Jraw m (f c)) =
        ENNReal.ofReal (2 ^ m) * ENNReal.ofReal (sa12x3_Jraw m (f c)) := ENNReal.ofReal_mul (by positivity)
    have e2 : ENNReal.ofReal (2 ^ m * (M0 * Kp)) = ENNReal.ofReal (2 ^ m) * ENNReal.ofReal (M0 * Kp) :=
      ENNReal.ofReal_mul (by positivity)
    rw [e1, e2, mul_assoc]
    gcongr
    exact hJraw c
  rw [sa12x4_varpi_sq]
  calc ∑' c, ENNReal.ofReal (jbracket (cellPt d c) ^ (-((d : ℝ) + 3))) * sobolevNormE (m : ℝ) (f c) ^ 2
      ≤ ∑' c, ENNReal.ofReal (jbracket (cellPt d c) ^ (-((d : ℝ) + 3))) *
          (ENNReal.ofReal (2 ^ m * (M0 * Kp)) * I c) := ENNReal.tsum_le_tsum fun c => by gcongr; exact hsob c
    _ = ENNReal.ofReal (2 ^ m * (M0 * Kp)) * ∑' c, ENNReal.ofReal (jbracket (cellPt d c) ^ (-((d : ℝ) + 3))) * I c := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun c => ?_
        ring
    _ ≤ ENNReal.ofReal (2 ^ m * (M0 * Kp)) * (ENNReal.ofReal Kb * sa12x4_J m u) := by
        gcongr
        have hsw : ∑' c, ENNReal.ofReal (jbracket (cellPt d c) ^ (-((d : ℝ) + 3))) * I c =
            ∫⁻ x, ENNReal.ofReal (sa12z3_Y m u x) * ∑' c, ENNReal.ofReal (jbracket (cellPt d c) ^ (-((d : ℝ) + 3))) *
              (closedBall (cellPt d c) 2).indicator (fun _ => (1 : ℝ≥0∞)) x := by
          have hm1 : ∀ c, Measurable (fun x => ENNReal.ofReal (jbracket (cellPt d c) ^ (-((d : ℝ) + 3))) *
              (closedBall (cellPt d c) 2).indicator (fun x => ENNReal.ofReal (sa12z3_Y m u x)) x) := fun c =>
            (hYm.ennreal_ofReal.indicator measurableSet_closedBall).const_mul _
          have e1 : ∀ c, ENNReal.ofReal (jbracket (cellPt d c) ^ (-((d : ℝ) + 3))) * I c =
              ∫⁻ x, ENNReal.ofReal (jbracket (cellPt d c) ^ (-((d : ℝ) + 3))) *
                (closedBall (cellPt d c) 2).indicator (fun x => ENNReal.ofReal (sa12z3_Y m u x)) x := by
            intro c
            rw [lintegral_const_mul _ (hYm.ennreal_ofReal.indicator measurableSet_closedBall),
              lintegral_indicator measurableSet_closedBall]
          simp_rw [e1]
          rw [← lintegral_tsum fun c => (hm1 c).aemeasurable]
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun c => ?_
          by_cases hx : x ∈ closedBall (cellPt d c) 2
          · simp only [indicator_of_mem hx]; ring
          · simp only [indicator_of_notMem hx]; simp
        rw [hsw, sa12x4_J, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono fun x => ?_
        calc ENNReal.ofReal (sa12z3_Y m u x) * ∑' c, ENNReal.ofReal (jbracket (cellPt d c) ^ (-((d : ℝ) + 3))) *
              (closedBall (cellPt d c) 2).indicator (fun _ => (1 : ℝ≥0∞)) x
            ≤ ENNReal.ofReal (sa12z3_Y m u x) * (ENNReal.ofReal Kb * ENNReal.ofReal (jbracket x ^ (-((d : ℝ) + 3)))) := by
              gcongr; exact hKb x
          _ ≤ ENNReal.ofReal (sa12x4_Z m u x) * (ENNReal.ofReal Kb * ENNReal.ofReal (jbracket x ^ (-((d : ℝ) + 3)))) := by
              gcongr; exact sa12x4_Y_le_Z m u x
          _ = ENNReal.ofReal Kb * (ENNReal.ofReal (jbracket x ^ (-((d : ℝ) + 3))) * ENNReal.ofReal (sa12x4_Z m u x)) := by ring
    _ = ENNReal.ofReal (2 ^ m * (M0 * Kp) * Kb) * sa12x4_J m u := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]

end HRS.MH.AdjointRd.Phase2SA12X4
