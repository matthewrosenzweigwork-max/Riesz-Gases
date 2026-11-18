import HRS.MD.EQLZCap5

/-!
# EQ-LZ packet CAP, helper 6: capacity estimate on `𝕋^d`, `d ≥ 2`

`vol{sT ≤ τ} ≤ τ/2` (`0 ≤ τ ≤ 2`, `d ≥ 2`) and the dyadic-shell bound
`∫ Psi m (sT u) du ≤ 2 (m + 1)`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped Classical

namespace HRS.MD.EQLZ.Cap

variable {d : ℕ}

theorem jordan_circle (x : UnitAddCircle) : 8 * ‖x‖ ^ 2 ≤ 1 - Real.cos (2 * Real.pi * ‖x‖) := by
  have h0 : 0 ≤ ‖x‖ := norm_nonneg x
  have h1 : ‖x‖ ≤ 1 / 2 := by
    have := AddCircle.norm_le_half_period (1 : ℝ) one_ne_zero (x := x)
    simpa using this
  set t := ‖x‖ with ht
  have hs : 2 * t ≤ Real.sin (Real.pi * t) := by
    have := Real.mul_le_sin (x := Real.pi * t) (by positivity) (by nlinarith [Real.pi_pos])
    have e : 2 / Real.pi * (Real.pi * t) = 2 * t := by field_simp
    rwa [e] at this
  have hc : Real.cos (2 * Real.pi * t) = 1 - 2 * Real.sin (Real.pi * t) ^ 2 := by
    have := Real.cos_two_mul (Real.pi * t)
    have h2 := Real.sin_sq_add_cos_sq (Real.pi * t)
    rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring, this]
    nlinarith
  rw [hc]
  nlinarith [sq_nonneg (Real.sin (Real.pi * t) - 2 * t)]

theorem sT_ge_coord (u : Torus d) (k : Fin d) : 8 * ‖u k‖ ^ 2 ≤ sT u := by
  unfold sT
  refine (jordan_circle (u k)).trans ?_
  exact Finset.single_le_sum (f := fun k => 1 - Real.cos (2 * Real.pi * ‖u k‖))
    (fun j _ => by linarith [Real.cos_le_one (2 * Real.pi * ‖u j‖)]) (Finset.mem_univ k)

theorem vol_sT_le (hd : 2 ≤ d) {τ : ℝ} (h0 : 0 ≤ τ) (h2 : τ ≤ 2) :
    (volume : Measure (Torus d)) {u | sT u ≤ τ} ≤ ENNReal.ofReal (τ / 2) := by
  set ρ : ℝ := Real.sqrt (τ / 8) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ2 : ρ ^ 2 = τ / 8 := Real.sq_sqrt (by positivity)
  have hρ1 : 2 * ρ ≤ 1 := by nlinarith
  have hsub : {u : Torus d | sT u ≤ τ} ⊆ Set.univ.pi (fun _ : Fin d => Metric.closedBall (0 : UnitAddCircle) ρ) := by
    intro u hu k _
    simp only [Metric.mem_closedBall, dist_zero_right]
    have := sT_ge_coord u k
    have : ‖u k‖ ^ 2 ≤ ρ ^ 2 := by rw [hρ2]; linarith [show sT u ≤ τ from hu]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hρ0 two_ne_zero).1 this
  calc (volume : Measure (Torus d)) {u | sT u ≤ τ}
      ≤ (volume : Measure (Torus d)) (Set.univ.pi (fun _ : Fin d => Metric.closedBall (0 : UnitAddCircle) ρ)) :=
        measure_mono hsub
    _ = ∏ _k : Fin d, ENNReal.ofReal (min 1 (2 * ρ)) := by
        rw [volume_pi_pi]
        refine Finset.prod_congr rfl fun k _ => ?_
        simpa using AddCircle.volume_closedBall (1 : ℝ) (x := (0 : UnitAddCircle)) ρ
    _ = ENNReal.ofReal (2 * ρ) ^ d := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, min_eq_right hρ1]
    _ = ENNReal.ofReal ((2 * ρ) ^ d) := (ENNReal.ofReal_pow (by positivity) d).symm
    _ ≤ ENNReal.ofReal ((2 * ρ) ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        exact pow_le_pow_of_le_one (by positivity) hρ1 hd
    _ = ENNReal.ofReal (τ / 2) := by
        congr 1; nlinarith

theorem Psi_nonneg (m : ℕ) (τ : ℝ) : 0 ≤ Psi m τ := by
  unfold Psi
  split_ifs with h
  · exact inv_nonneg.2 (le_trans (Real.exp_pos _).le h.1)
  · exact le_rfl

theorem Psi_le_sum (m : ℕ) (hm : 1 ≤ m) (τ : ℝ) :
    Psi m τ ≤ ∑ j ∈ Finset.range (m + 1),
      Real.exp (2 * (m : ℝ) - j) * (if τ ≤ Real.exp (-2 * (m : ℝ) + j + 1) then 1 else 0) := by
  have hnn : ∀ j ∈ Finset.range (m + 1), 0 ≤ Real.exp (2 * (m : ℝ) - j) *
      (if τ ≤ Real.exp (-2 * (m : ℝ) + j + 1) then (1 : ℝ) else 0) := fun j _ =>
    mul_nonneg (Real.exp_pos _).le (by split_ifs <;> norm_num)
  by_cases hs : Real.exp (-2 * m) ≤ τ ∧ τ ≤ Real.exp (-(m : ℝ))
  · have hτ : 0 < τ := lt_of_lt_of_le (Real.exp_pos _) hs.1
    have hl1 : -2 * (m : ℝ) ≤ Real.log τ := (Real.le_log_iff_exp_le hτ).2 hs.1
    have hl2 : Real.log τ ≤ -(m : ℝ) := (Real.log_le_iff_le_exp hτ).2 hs.2
    set a : ℝ := Real.log τ + 2 * m with ha
    have ha0 : 0 ≤ a := by rw [ha]; linarith
    set j : ℕ := ⌊a⌋₊ with hj
    have hj1 : (j : ℝ) ≤ a := Nat.floor_le ha0
    have hj2 : a < j + 1 := Nat.lt_floor_add_one a
    have hjm : j ≤ m := Nat.floor_le_of_le (by rw [ha]; linarith)
    have hjmem : j ∈ Finset.range (m + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hjm)
    refine le_trans ?_ (Finset.single_le_sum hnn hjmem)
    have h3 : τ ≤ Real.exp (-2 * (m : ℝ) + j + 1) := by
      have : Real.log τ < -2 * (m : ℝ) + j + 1 := by rw [ha] at hj2; linarith
      exact ((Real.log_lt_iff_lt_exp hτ).1 this).le
    have h4 : Real.exp ((j : ℝ) - 2 * m) ≤ τ := by
      have : (j : ℝ) - 2 * m ≤ Real.log τ := by rw [ha] at hj1; linarith
      exact (Real.le_log_iff_exp_le hτ).1 this
    simp only [Psi, if_pos hs, if_pos h3, mul_one]
    calc τ⁻¹ ≤ (Real.exp ((j : ℝ) - 2 * m))⁻¹ := inv_anti₀ (Real.exp_pos _) h4
      _ = Real.exp (2 * (m : ℝ) - j) := by rw [← Real.exp_neg]; congr 1; ring
  · simp only [Psi, if_neg hs]
    exact Finset.sum_nonneg hnn

theorem integral_Psi_sT (hd : 2 ≤ d) {m : ℕ} (hm : 1 ≤ m) :
    ∫ u : Torus d, Psi m (sT u) ≤ 2 * ((m : ℝ) + 1) := by
  set A : ℕ → Set (Torus d) := fun j => {u | sT u ≤ Real.exp (-2 * (m : ℝ) + j + 1)} with hA
  have hAm : ∀ j, MeasurableSet (A j) := fun j =>
    (isClosed_le continuous_sT continuous_const).measurableSet
  set g : Torus d → ℝ := fun u => ∑ j ∈ Finset.range (m + 1),
    Real.exp (2 * (m : ℝ) - j) * (A j).indicator (fun _ => (1 : ℝ)) u with hg
  have hgI : Integrable g (volume : Measure (Torus d)) := by
    refine integrable_finsetSum _ fun j _ => ?_
    exact ((integrable_const (1 : ℝ)).indicator (hAm j)).const_mul _
  have h1 : ∫ u : Torus d, Psi m (sT u) ≤ ∫ u, g u := by
    refine integral_mono_of_nonneg (ae_of_all _ fun u => Psi_nonneg _ _) hgI (ae_of_all _ fun u => ?_)
    refine (Psi_le_sum m hm (sT u)).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hA, Set.indicator, Set.mem_setOf_eq]
  have h2 : ∫ u, g u = ∑ j ∈ Finset.range (m + 1), Real.exp (2 * (m : ℝ) - j) *
      (volume : Measure (Torus d)).real (A j) := by
    simp only [hg]
    rw [integral_finsetSum _ (fun j _ => ((integrable_const (1 : ℝ)).indicator (hAm j)).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_indicator_const _ (hAm j)]
    simp
  have h3 : ∀ j ∈ Finset.range (m + 1), Real.exp (2 * (m : ℝ) - j) *
      (volume : Measure (Torus d)).real (A j) ≤ 2 := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hτ0 : 0 ≤ Real.exp (-2 * (m : ℝ) + j + 1) := (Real.exp_pos _).le
    have hτ2 : Real.exp (-2 * (m : ℝ) + j + 1) ≤ 2 := by
      have h0 : Real.exp (-2 * (m : ℝ) + j + 1) ≤ Real.exp 0 := by
        apply Real.exp_le_exp.2
        have : (j : ℝ) ≤ m := by exact_mod_cast hjm
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm
        linarith
      rw [Real.exp_zero] at h0
      linarith
    have hv := vol_sT_le hd hτ0 hτ2
    have hvr : (volume : Measure (Torus d)).real (A j) ≤ Real.exp (-2 * (m : ℝ) + j + 1) / 2 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    calc Real.exp (2 * (m : ℝ) - j) * (volume : Measure (Torus d)).real (A j)
        ≤ Real.exp (2 * (m : ℝ) - j) * (Real.exp (-2 * (m : ℝ) + j + 1) / 2) :=
          mul_le_mul_of_nonneg_left hvr (Real.exp_pos _).le
      _ = Real.exp 1 / 2 := by
          rw [← mul_div_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ 2 := by have := (Real.exp_one_lt_d9).le; linarith
  calc ∫ u : Torus d, Psi m (sT u) ≤ ∫ u, g u := h1
    _ = _ := h2
    _ ≤ ∑ _j ∈ Finset.range (m + 1), (2 : ℝ) := Finset.sum_le_sum h3
    _ = 2 * ((m : ℝ) + 1) := by simp; ring

end HRS.MD.EQLZ.Cap
