import HRS.MS.R2ChaosAux15

/-!
# HRS.MS.R2ChaosAux16 -- continuity of the quadratic path maps `C([0,T])^n → L²([0,T])`

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

section PathEval

variable {T : ℝ}

theorem s94_pathEval_measurable (w : C(Set.Icc (0 : ℝ) T, ℝ)) : Measurable (r2PathEval T w) := by
  by_cases hT : 0 ≤ T
  · have : r2PathEval T w = Set.indicator (Set.Icc 0 T) (fun t => w (Set.projIcc 0 T hT t)) := by
      funext t
      by_cases ht : t ∈ Set.Icc (0 : ℝ) T
      · rw [Set.indicator_of_mem ht, s94_pathEval_eq ht]
        simp [Set.projIcc_of_mem hT ht]
      · rw [Set.indicator_of_notMem ht]
        unfold r2PathEval; simp [ht]
    rw [this]
    exact (w.continuous.comp continuous_projIcc).measurable.indicator measurableSet_Icc
  · have : r2PathEval T w = fun _ => 0 := by
      funext t
      have ht : t ∉ Set.Icc (0 : ℝ) T := fun h => hT (h.1.trans h.2)
      unfold r2PathEval; simp [ht]
    rw [this]
    exact measurable_const

theorem s94_pathEval_abs_le (w : C(Set.Icc (0 : ℝ) T, ℝ)) (t : ℝ) : |r2PathEval T w t| ≤ ‖w‖ := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) T
  · rw [s94_pathEval_eq ht]
    simpa using w.norm_coe_le_norm ⟨t, ht⟩
  · have : r2PathEval T w t = 0 := by unfold r2PathEval; simp [ht]
    rw [this]; simp

theorem s94_pathEval_sub (w w' : C(Set.Icc (0 : ℝ) T, ℝ)) (t : ℝ) :
    r2PathEval T (w - w') t = r2PathEval T w t - r2PathEval T w' t := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) T
  · simp [s94_pathEval_eq ht]
  · unfold r2PathEval; simp [ht]

theorem s94_dist_r2L2Path_le {f f' : ℝ → ℝ} (hT : 0 ≤ T) (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hf' : MemLp f' 2 (volume.restrict (Set.Icc (0 : ℝ) T))) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, |f t - f' t| ≤ δ) :
    dist (r2L2Path T f) (r2L2Path T f') ≤ Real.sqrt T * δ := by
  set μT : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  rw [s94_r2L2Path_eq hf, s94_r2L2Path_eq hf']
  have hd : dist (hf.toLp f : Lp ℝ 2 μT) (hf'.toLp f') = ‖(hf.sub hf').toLp (f - f')‖ := by
    rw [dist_eq_norm, ← MemLp.toLp_sub]
  show dist (hf.toLp f : Lp ℝ 2 μT) (hf'.toLp f') ≤ _
  rw [hd, Lp.norm_toLp]
  have hae : ∀ᵐ t ∂μT, ‖(f - f') t‖ ≤ δ := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun t ht => ?_)
    simpa using h t ht
  have h1 := eLpNorm_le_of_ae_bound (p := 2) (hf.sub hf').aestronglyMeasurable hae
  have hμ : μT Set.univ = ENNReal.ofReal T := by simp [hμT]
  rw [hμ] at h1
  have h2 : (ENNReal.ofReal T) ^ ((2 : ℝ≥0∞).toReal⁻¹) = ENNReal.ofReal (Real.sqrt T) := by
    rw [ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg hT (by norm_num), Real.sqrt_eq_rpow]
    norm_num
  rw [h2, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h1
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h1).trans_eq (ENNReal.toReal_ofReal (by positivity))

end PathEval

section Psi

variable {T : ℝ} {n : ℕ} {S : Type*} [Fintype S]

/-- The quadratic integrand `t ↦ ∑_s coef_s(t) w_{i s}(t) w_{j s}(t)`. -/
def s94Intg (coef : S → ℝ → ℝ) (i j : S → Fin n) (w : Fin n → C(Set.Icc (0 : ℝ) T, ℝ)) (t : ℝ) : ℝ :=
  ∑ s, coef s t * (r2PathEval T (w (i s)) t * r2PathEval T (w (j s)) t)

theorem s94Intg_measurable {coef : S → ℝ → ℝ} (hm : ∀ s, Measurable (coef s)) (i j : S → Fin n)
    (w : Fin n → C(Set.Icc (0 : ℝ) T, ℝ)) : Measurable (s94Intg coef i j w) := by
  unfold s94Intg
  exact Finset.measurable_sum _ fun s _ => (hm s).mul
    ((s94_pathEval_measurable _).mul (s94_pathEval_measurable _))

theorem s94Intg_abs_le {coef : S → ℝ → ℝ} {K0 : ℝ} (hb : ∀ s t, |coef s t| ≤ K0) (i j : S → Fin n)
    (w : Fin n → C(Set.Icc (0 : ℝ) T, ℝ)) (t : ℝ) :
    |s94Intg coef i j w t| ≤ (Fintype.card S : ℝ) * K0 * ‖w‖ ^ 2 := by
  unfold s94Intg
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ s ∈ (Finset.univ : Finset S), |coef s t * (r2PathEval T (w (i s)) t * r2PathEval T (w (j s)) t)| ≤
      K0 * ‖w‖ ^ 2 := by
    intro s _
    rw [abs_mul, abs_mul]
    have h1 := s94_pathEval_abs_le (w (i s)) t
    have h2 := s94_pathEval_abs_le (w (j s)) t
    have h3 : ‖w (i s)‖ ≤ ‖w‖ := norm_le_pi_norm w (i s)
    have h4 : ‖w (j s)‖ ≤ ‖w‖ := norm_le_pi_norm w (j s)
    have hK : 0 ≤ K0 := (abs_nonneg _).trans (hb s t)
    calc |coef s t| * (|r2PathEval T (w (i s)) t| * |r2PathEval T (w (j s)) t|)
        ≤ K0 * (‖w‖ * ‖w‖) := by
          gcongr
          · exact hb s t
          · exact h1.trans h3
          · exact h2.trans h4
      _ = K0 * ‖w‖ ^ 2 := by ring
  calc _ ≤ ∑ s : S, K0 * ‖w‖ ^ 2 := Finset.sum_le_sum this
    _ = _ := by simp [Finset.sum_const]; ring

theorem s94Intg_memLp (hT : 0 ≤ T) {coef : S → ℝ → ℝ} (hm : ∀ s, Measurable (coef s)) {K0 : ℝ}
    (hb : ∀ s t, |coef s t| ≤ K0) (i j : S → Fin n) (w : Fin n → C(Set.Icc (0 : ℝ) T, ℝ)) :
    MemLp (s94Intg coef i j w) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  have hfin : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) := by constructor; simp
  exact MemLp.of_bound (s94Intg_measurable hm i j w).aestronglyMeasurable _
    (ae_of_all _ fun t => by simpa using s94Intg_abs_le hb i j w t)

theorem s94_Psi_continuous (hT : 0 ≤ T) {coef : S → ℝ → ℝ} (hm : ∀ s, Measurable (coef s)) {K0 : ℝ}
    (hK : 0 ≤ K0) (hb : ∀ s t, |coef s t| ≤ K0) (i j : S → Fin n) :
    Continuous fun w : Fin n → C(Set.Icc (0 : ℝ) T, ℝ) => r2L2Path T (s94Intg coef i j w) := by
  refine continuous_iff_continuousAt.2 fun w0 => ?_
  set L : ℝ := Real.sqrt T * ((Fintype.card S : ℝ) * K0 * (2 * ‖w0‖ + 1)) with hL
  have hbound : ∀ w : Fin n → C(Set.Icc (0 : ℝ) T, ℝ), ‖w - w0‖ ≤ 1 →
      dist (r2L2Path T (s94Intg coef i j w)) (r2L2Path T (s94Intg coef i j w0)) ≤ L * ‖w - w0‖ := by
    intro w hw
    have hpt : ∀ t ∈ Set.Icc (0 : ℝ) T, |s94Intg coef i j w t - s94Intg coef i j w0 t| ≤
        (Fintype.card S : ℝ) * K0 * (2 * ‖w0‖ + 1) * ‖w - w0‖ := by
      intro t _
      unfold s94Intg
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hs : ∀ s ∈ (Finset.univ : Finset S), |coef s t * (r2PathEval T (w (i s)) t * r2PathEval T (w (j s)) t) -
          coef s t * (r2PathEval T (w0 (i s)) t * r2PathEval T (w0 (j s)) t)| ≤
          K0 * ((2 * ‖w0‖ + 1) * ‖w - w0‖) := by
        intro s _
        rw [← mul_sub, abs_mul]
        set D := ‖w - w0‖ with hD
        have hD0 : 0 ≤ D := norm_nonneg _
        have e1 : |r2PathEval T (w (i s)) t| ≤ ‖w0‖ + 1 := by
          have h1 := s94_pathEval_abs_le (w (i s)) t
          have h2 : ‖w (i s)‖ ≤ ‖w‖ := norm_le_pi_norm w (i s)
          have h3 : ‖w‖ ≤ ‖w0‖ + ‖w - w0‖ := by
            calc ‖w‖ = ‖(w - w0) + w0‖ := by rw [sub_add_cancel]
              _ ≤ ‖w - w0‖ + ‖w0‖ := norm_add_le _ _
              _ = _ := add_comm _ _
          linarith
        have e2 : |r2PathEval T (w0 (j s)) t| ≤ ‖w0‖ := (s94_pathEval_abs_le _ t).trans (norm_le_pi_norm w0 (j s))
        have e3 : |r2PathEval T (w (j s)) t - r2PathEval T (w0 (j s)) t| ≤ D := by
          rw [← s94_pathEval_sub]
          exact (s94_pathEval_abs_le _ t).trans (by simpa using norm_le_pi_norm (w - w0) (j s))
        have e4 : |r2PathEval T (w (i s)) t - r2PathEval T (w0 (i s)) t| ≤ D := by
          rw [← s94_pathEval_sub]
          exact (s94_pathEval_abs_le _ t).trans (by simpa using norm_le_pi_norm (w - w0) (i s))
        have key : |r2PathEval T (w (i s)) t * r2PathEval T (w (j s)) t -
            r2PathEval T (w0 (i s)) t * r2PathEval T (w0 (j s)) t| ≤ (2 * ‖w0‖ + 1) * D := by
          have : r2PathEval T (w (i s)) t * r2PathEval T (w (j s)) t -
              r2PathEval T (w0 (i s)) t * r2PathEval T (w0 (j s)) t =
              r2PathEval T (w (i s)) t * (r2PathEval T (w (j s)) t - r2PathEval T (w0 (j s)) t) +
              (r2PathEval T (w (i s)) t - r2PathEval T (w0 (i s)) t) * r2PathEval T (w0 (j s)) t := by ring
          rw [this]
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
          have hn : 0 ≤ ‖w0‖ := norm_nonneg _
          calc _ ≤ (‖w0‖ + 1) * D + D * ‖w0‖ := by
                gcongr
            _ ≤ (2 * ‖w0‖ + 1) * D := by nlinarith
        exact mul_le_mul (hb s t) key (abs_nonneg _) hK
      refine (Finset.sum_le_sum hs).trans ?_
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      refine le_of_eq ?_
      ring
    have := s94_dist_r2L2Path_le hT (s94Intg_memLp hT hm hb i j w) (s94Intg_memLp hT hm hb i j w0)
      (δ := (Fintype.card S : ℝ) * K0 * (2 * ‖w0‖ + 1) * ‖w - w0‖) (by positivity) hpt
    calc _ ≤ _ := this
      _ = L * ‖w - w0‖ := by rw [hL]; ring
  have hn0 : Tendsto (fun w : Fin n → C(Set.Icc (0 : ℝ) T, ℝ) => ‖w - w0‖) (𝓝 w0) (𝓝 0) := by
    have hc : Continuous fun w : Fin n → C(Set.Icc (0 : ℝ) T, ℝ) => ‖w - w0‖ :=
      (continuous_id.sub continuous_const).norm
    have := hc.tendsto w0
    simpa using this
  have hevent : ∀ᶠ w in 𝓝 w0, ‖w - w0‖ ≤ 1 := hn0.eventually (ge_mem_nhds one_pos)
  refine (tendsto_iff_dist_tendsto_zero).2 ?_
  refine squeeze_zero' (Eventually.of_forall fun w => dist_nonneg) ?_ (by simpa using hn0.const_mul L)
  filter_upwards [hevent] with w hw using hbound w hw

end Psi

end HRS.MS.R2Chaos
