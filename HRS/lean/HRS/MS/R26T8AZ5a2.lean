import HRS.MS.R26T8AZ5a1
import HRS.MS.R26T8AP15g
import HRS.MS.R26T8AP11a3

/-!
# S8.2 T8A Z5a2: the near-diagonal cutoff `ζ(x-y) F(x,y)`, `ζ = chi(4 .)`
`r26t8a_Z5a2_Fz chi F x y = chi(4(x-y)) F(x,y)` vanishes for `|x-y| ≥ 1/2`; `F - Fz` vanishes for `|x-y| ≤ 1/4`;
`Fz` is conormal with the same `k b M σ` (constant `c A`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

def r26t8a_Z5a2_Fz (chi : Euc d → ℝ) (F : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ :=
  chi ((4 : ℝ) • (x - y)) * F x y

theorem r26t8a_Z5a2_midPair (chi : Euc d → ℝ) (F : Euc d → Euc d → ℝ) (Y w : Euc d) :
    midPair (r26t8a_Z5a2_Fz chi F) Y w = chi ((4 : ℝ) • w) * midPair F Y w := by
  unfold midPair r26t8a_Z5a2_Fz
  have e : (Y + (1 / 2 : ℝ) • w) - (Y - (1 / 2 : ℝ) • w) = w := by module
  rw [e]

theorem r26t8a_Z5a2_supp {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (F : Euc d → Euc d → ℝ) (x y : Euc d)
    (h : 1 / 2 ≤ ‖x - y‖) : r26t8a_Z5a2_Fz chi F x y = 0 := by
  unfold r26t8a_Z5a2_Fz
  have : 2 ≤ ‖(4 : ℝ) • (x - y)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]; linarith
  rw [hchi.2.2.2.2 _ this, zero_mul]

theorem r26t8a_Z5a2_one {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (F : Euc d → Euc d → ℝ) (x y : Euc d)
    (h : ‖x - y‖ ≤ 1 / 4) : r26t8a_Z5a2_Fz chi F x y = F x y := by
  unfold r26t8a_Z5a2_Fz
  have : ‖(4 : ℝ) • (x - y)‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]; linarith
  rw [hchi.2.2.2.1 _ this, one_mul]

theorem r26t8a_Z5a2_nest_one (p q : ℕ) (X z : Euc d) :
    ‖r26t8a_nest p q (fun _ : Euc d × Euc d => (1 : ℝ)) X z‖ ≤ 1 := by
  unfold r26t8a_nest
  have h : (fun Y : Euc d => iteratedFDeriv ℝ q (fun w : Euc d => (1 : ℝ)) z) =
      fun _ => iteratedFDeriv ℝ q (fun w : Euc d => (1 : ℝ)) z := rfl
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [norm_iteratedFDeriv_zero]
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · rw [norm_iteratedFDeriv_zero]; simp
    · rw [iteratedFDeriv_const_of_ne hq.ne']; simp
  · have : iteratedFDeriv ℝ p (fun _ : Euc d => iteratedFDeriv ℝ q (fun w : Euc d => (1 : ℝ)) z) X = 0 :=
      congrFun (iteratedFDeriv_const_of_ne hp.ne' _) X
    rw [this]; simp

theorem r26t8a_Z5a2_conormal {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k b : ℕ) (M σ : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (F : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal k b M σ A F →
      Conormal k b M σ (c * A) (r26t8a_Z5a2_Fz chi F) := by
  have hζ : ContDiff ℝ ∞ (fun w : Euc d => chi ((4 : ℝ) • w)) := hchi.1.comp (contDiff_const_smul _)
  have hcs : HasCompactSupport (fun w : Euc d => chi ((4 : ℝ) • w)) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) 1) fun w hw => ?_
    have : 1 < ‖w‖ := by simpa [mem_closedBall_zero_iff] using hw
    have h2 : 2 ≤ ‖(4 : ℝ) • w‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]; linarith
    exact hchi.2.2.2.2 _ h2
  have hJ : ∀ i : ℕ, ∃ C : ℝ, ∀ w, ‖iteratedFDeriv ℝ i (fun w : Euc d => chi ((4 : ℝ) • w)) w‖ ≤ C := fun i =>
    (hζ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support (hcs.iteratedFDeriv i)
  choose Cz hCz using hJ
  set Bz : ℝ := ∑ i ∈ Finset.range (k + 1), max (Cz i) 0 with hBz
  have hBz0 : 0 ≤ Bz := Finset.sum_nonneg fun i _ => le_max_right _ _
  have hBzi : ∀ i ≤ k, ∀ w, ‖iteratedFDeriv ℝ i (fun w : Euc d => chi ((4 : ℝ) • w)) w‖ ≤ Bz := by
    intro i hi w
    refine (hCz i w).trans (le_trans (le_max_left (Cz i) 0) ?_)
    exact Finset.single_le_sum (f := fun i => max (Cz i) 0) (fun i _ => le_max_right _ _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  refine ⟨2 ^ k * (((k : ℝ) + 1) ^ 2 * Bz), by positivity, fun F A hA hF => ?_⟩
  have hc : ContDiff ℝ (k : WithTop ℕ∞) (fun Yw : Euc d × Euc d => chi ((4 : ℝ) • Yw.2)) :=
    (hζ.of_le (by exact_mod_cast le_top)).comp contDiff_snd
  have h := r26t8a_conormal_mul_gen hchi (m := 0) 0 (by norm_num) hA hBz0 hc (fun i j hij X z _ => by
    have hpw : HRS.MS.Phase2S82.pairWeight (0 : ℝ) (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) = 1 := by
      simp [HRS.MS.Phase2S82.pairWeight]
    rw [hpw]
    simp only [pow_zero, ite_self, mul_one]
    unfold r26t8a_nest
    have hconst : (fun Y : Euc d => iteratedFDeriv ℝ j (fun w : Euc d => (fun Yw : Euc d × Euc d => chi ((4 : ℝ) • Yw.2)) (Y, w)) z) =
        fun _ => iteratedFDeriv ℝ j (fun w : Euc d => chi ((4 : ℝ) • w)) z := rfl
    rw [hconst]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [norm_iteratedFDeriv_zero]
      exact hBzi j (by omega) z
    · rw [congrFun (iteratedFDeriv_const_of_ne hi.ne' _) X]
      simpa using hBz0) hF
  simp only [add_zero, Nat.cast_zero, sub_zero] at h
  exact r26t8a_conormal_mono_sA (by positivity) (le_of_eq (by ring)) le_rfl h

end HRS.MS.R26T8A
