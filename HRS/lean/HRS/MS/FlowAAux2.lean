import HRS.MS.FlowAAux1

/-!
# MS-FLOW-A, global existence by truncation

The drift is composed with the radial retraction onto a large ball; the truncated field is globally
Lipschitz and bounded, so the local Picard-Lindelof theorem on `[0,T]` applies, and the a-priori
Gronwall bound shows the solution never leaves the ball.
-/

open Set Metric
open scoped NNReal Topology

set_option linter.unusedSectionVars false

namespace HRS.MS.FlowA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial retraction onto the closed ball of radius `R`. -/
noncomputable def ret (R : ℝ) (y : E) : E := (R / max R ‖y‖) • y

theorem ret_of_le {R : ℝ} (hR : 0 < R) {y : E} (hy : ‖y‖ ≤ R) : ret R y = y := by
  simp [ret, max_eq_left hy, div_self hR.ne']

theorem norm_ret_le {R : ℝ} (hR : 0 < R) (y : E) : ‖ret R y‖ ≤ ‖y‖ ∧ ‖ret R y‖ ≤ R := by
  have hm : 0 < max R ‖y‖ := lt_max_of_lt_left hR
  have hc : 0 ≤ R / max R ‖y‖ := by positivity
  have e : ‖ret R y‖ = R / max R ‖y‖ * ‖y‖ := by
    rw [ret, norm_smul, Real.norm_of_nonneg hc]
  rw [e]
  constructor
  · have : R / max R ‖y‖ ≤ 1 := (div_le_one hm).2 (le_max_left _ _)
    nlinarith [norm_nonneg y]
  · rw [div_mul_eq_mul_div, div_le_iff₀ hm]
    nlinarith [le_max_right R ‖y‖]

theorem ret_lip {R : ℝ} (hR : 0 < R) (y z : E) : ‖ret R y - ret R z‖ ≤ 2 * ‖y - z‖ := by
  set my := max R ‖y‖ with hmy_def
  set mz := max R ‖z‖ with hmz_def
  have hmy : 0 < my := lt_max_of_lt_left hR
  have hmz : 0 < mz := lt_max_of_lt_left hR
  have hcy : R / my ≤ 1 := (div_le_one hmy).2 (le_max_left _ _)
  have hcy0 : 0 ≤ R / my := by positivity
  have hsplit : ret R y - ret R z = (R / my) • (y - z) + (R / my - R / mz) • z := by
    simp only [ret, smul_sub, sub_smul]; abel
  have h1 : |R / my - R / mz| * ‖z‖ ≤ ‖y - z‖ := by
    have e : R / my - R / mz = R * (mz - my) / (my * mz) := by field_simp
    have a : |mz - my| ≤ ‖y - z‖ := by
      have := abs_max_sub_max_le_abs ‖z‖ ‖y‖ R
      rw [max_comm ‖z‖ R, max_comm ‖y‖ R] at this
      refine this.trans ?_
      calc |‖z‖ - ‖y‖| ≤ ‖z - y‖ := abs_norm_sub_norm_le _ _
        _ = ‖y - z‖ := norm_sub_rev _ _
    rw [e, abs_div, abs_mul, abs_of_pos hR, abs_of_pos (mul_pos hmy hmz), div_mul_eq_mul_div,
      div_le_iff₀ (mul_pos hmy hmz)]
    have hz : ‖z‖ ≤ mz := le_max_right _ _
    have hRm : R ≤ my := le_max_left _ _
    calc R * |mz - my| * ‖z‖ ≤ my * ‖y - z‖ * mz := by gcongr
      _ = ‖y - z‖ * (my * mz) := by ring
  rw [hsplit]
  calc ‖(R / my) • (y - z) + (R / my - R / mz) • z‖
      ≤ ‖(R / my) • (y - z)‖ + ‖(R / my - R / mz) • z‖ := norm_add_le _ _
    _ = R / my * ‖y - z‖ + |R / my - R / mz| * ‖z‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hcy0, Real.norm_eq_abs]
    _ ≤ 1 * ‖y - z‖ + ‖y - z‖ := by gcongr
    _ = 2 * ‖y - z‖ := by ring

variable [CompleteSpace E]

/-- Global existence on `[0,T]` for `f' = -b(τ,f)`, `f 0 = x`. -/
theorem exists_sol {T Λ : ℝ} {b : ℝ → E → E} (h : Hyp T Λ b) (hT : 0 ≤ T) (x : E) :
    ∃ f : ℝ → E, f 0 = x ∧ Sol T b f := by
  have hΛ := h.Λ_nonneg
  set K' : ℝ := Λ + 1 with hK'def
  have hK' : 0 < K' := by positivity
  set R : ℝ := (‖x‖ + 1) * Real.exp (K' * T) with hRdef
  have hR1 : 1 ≤ R := by
    have h1 : 1 ≤ ‖x‖ + 1 := by linarith [norm_nonneg x]
    have h2 : 1 ≤ Real.exp (K' * T) := Real.one_le_exp (by positivity)
    nlinarith
  have hR : 0 < R := by linarith
  set v : ℝ → E → E := fun t y => -(b t (ret R y)) with hv
  have hvlip : ∀ t ∈ Icc (0 : ℝ) T, ∀ y z, ‖v t y - v t z‖ ≤ (2 * Λ) * ‖y - z‖ := by
    intro t ht y z
    simp only [hv]
    rw [show -b t (ret R y) - -b t (ret R z) = -(b t (ret R y) - b t (ret R z)) by abel, norm_neg]
    calc ‖b t (ret R y) - b t (ret R z)‖ ≤ Λ * ‖ret R y - ret R z‖ := h.lip t ht _ _
      _ ≤ Λ * (2 * ‖y - z‖) := by gcongr; exact ret_lip hR y z
      _ = 2 * Λ * ‖y - z‖ := by ring
  have hvbd : ∀ t ∈ Icc (0 : ℝ) T, ∀ y, ‖v t y‖ ≤ Λ * (1 + R) := by
    intro t ht y
    simp only [hv, norm_neg]
    calc ‖b t (ret R y)‖ ≤ Λ * (1 + ‖ret R y‖) := h.growth t ht _
      _ ≤ Λ * (1 + R) := by gcongr; exact (norm_ret_le hR y).2
  have hvc : ∀ y, ContinuousOn (fun t => v t y) (Icc (0 : ℝ) T) := by
    intro y
    have := h.cont.comp (f := fun t : ℝ => (t, ret R y)) (by fun_prop)
      (s := Icc (0 : ℝ) T) (t := Icc (0 : ℝ) T ×ˢ univ) (fun t ht => ⟨ht, trivial⟩)
    exact this.neg
  set L : ℝ≥0 := (Λ * (1 + R)).toNNReal with hL
  set K : ℝ≥0 := (2 * Λ).toNNReal with hK
  have hLc : (L : ℝ) = Λ * (1 + R) := Real.coe_toNNReal _ (by positivity)
  have hKc : (K : ℝ) = 2 * Λ := Real.coe_toNNReal _ (by positivity)
  have hPL : IsPicardLindelof v (tmin := 0) (tmax := T) (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T) x
      (L * T.toNNReal) 0 L K :=
    ⟨fun t ht => LipschitzOnWith.of_dist_le_mul fun y _ z _ => by
      rw [dist_eq_norm, dist_eq_norm, hKc]; exact hvlip t ht y z,
     fun y _ => hvc y,
     fun t ht y _ => by rw [hLc]; exact hvbd t ht y,
     by
      simp only [sub_zero, NNReal.coe_mul, Real.coe_toNNReal T hT]
      rw [max_eq_left hT]
      simp⟩
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hα0' : α 0 = x := hα0
  have hcont : ContinuousOn α (Icc (0 : ℝ) T) := fun t ht => (hα t ht).continuousWithinAt
  have hmem : ∀ t ∈ Ico (0 : ℝ) T, Icc (0 : ℝ) T ∈ 𝓝[≥] t := fun t ht =>
    Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := α)
    (f' := fun t => v t (α t)) (δ := ‖x‖) (K := K') (ε := K') (a := 0) (b := T) hcont
    (fun t ht => (hα t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (hmem t ht))
    (by simp [hα0']) (by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
      simp only [hv, norm_neg]
      calc ‖b t (ret R (α t))‖ ≤ Λ * (1 + ‖ret R (α t)‖) := h.growth t ht' _
        _ ≤ Λ * (1 + ‖α t‖) := by gcongr; exact (norm_ret_le hR _).1
        _ ≤ K' * ‖α t‖ + K' := by rw [hK'def]; nlinarith [norm_nonneg (α t)])
  have hbd : ∀ t ∈ Icc (0 : ℝ) T, ‖α t‖ ≤ R := by
    intro t ht
    refine (hgr t ht).trans ?_
    rw [gronwallBound_of_K_ne_0 hK'.ne']
    simp only [sub_zero, div_self hK'.ne', one_mul]
    have hE : Real.exp (K' * t) ≤ Real.exp (K' * T) :=
      Real.exp_le_exp.2 (by nlinarith [ht.2])
    have hE1 : 0 < Real.exp (K' * t) := Real.exp_pos _
    rw [hRdef]
    nlinarith [norm_nonneg x]
  refine ⟨α, hα0', fun t ht => ?_⟩
  have e : ret R (α t) = α t := ret_of_le hR (hbd t ht)
  have := hα t ht
  simpa [hv, e] using this

end HRS.MS.FlowA
