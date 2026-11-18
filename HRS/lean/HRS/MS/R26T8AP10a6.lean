import HRS.MS.R26T8AP10a5

/-!
# S8.2 T8A P10a (part 6): per-direction integration by parts for the regularised kernel
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

/-- Hypotheses on the vector field `h` (to be `ρ ∇ Q(·,y)`): `C^1` off `y`, Gaussian-pole bounds. -/
structure R26P10Hyp (d : ℕ) (y : Euc d) (τ : ℝ) (h : Euc d → Euc d) : Prop where
  hd : 2 ≤ d
  τ0 : 0 < τ
  τd : τ + 1 < d
  C1 : ContDiffOn ℝ 1 h {y}ᶜ
  hb : R26P10GP y τ (fun u => ‖h u‖)
  hdb : R26P10GP y (τ + 1) (fun u => ‖fderiv ℝ h u‖)

theorem R26P10Hyp.hb1 {y : Euc d} {τ : ℝ} {h : Euc d → Euc d} (H : R26P10Hyp d y τ h) :
    R26P10GP y (τ + 1) (fun u => ‖h u‖) :=
  r26t8a_p10a_gp_mono H.hb H.τ0.le (by linarith)

theorem r26t8a_Gamma_hasFDerivAt (s : ℝ) {ε : ℝ} (hε : 0 < ε) (x u : Euc d) :
    HasFDerivAt (fun v : Euc d => r26t8a_keps s ε (x - v))
      (((-s / 2 * (‖x - u‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) * 2) • innerSL ℝ (x - u)).comp
        (-(ContinuousLinearMap.id ℝ (Euc d)))) u := by
  have h1 : HasFDerivAt (fun v : Euc d => x - v) (-(ContinuousLinearMap.id ℝ (Euc d))) u :=
    (hasFDerivAt_id u).const_sub x
  exact (r26t8a_keps_hasFDerivAt s hε (x - u)).comp u h1

theorem r26t8a_fderiv_Gamma (s : ℝ) {ε : ℝ} (hε : 0 < ε) (x u : Euc d) (j : Fin d) :
    fderiv ℝ (fun v : Euc d => r26t8a_keps s ε (x - v)) u (EuclideanSpace.single j 1) =
      - r26t8a_dkeps s ε (x - u) j := by
  rw [(r26t8a_Gamma_hasFDerivAt s hε x u).fderiv]
  simp [r26t8a_dkeps, EuclideanSpace.inner_single_right]
  ring

theorem r26t8a_p10a_ibp_j {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {y : Euc d} {τ : ℝ}
    {h : Euc d → Euc d} (H : R26P10Hyp d y τ h) {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) (x : Euc d)
    {δ : ℝ} (hδ : 0 < δ) {Cχ : ℝ} (hCχ : ∀ u : Euc d, ‖fderiv ℝ (r26t8a_cut chi y δ) u‖ ≤ Cχ / δ)
    (j : Fin d) :
    Integrable (fun u => r26t8a_keps s ε (x - u) * r26t8a_Dj chi y δ h j u) ∧
    Integrable (fun u => r26t8a_dkeps s ε (x - u) j * r26t8a_Hj chi y δ h j u) ∧
    ∫ u, r26t8a_keps s ε (x - u) * r26t8a_Dj chi y δ h j u =
      ∫ u, r26t8a_dkeps s ε (x - u) j * r26t8a_Hj chi y δ h j u := by
  have hd := H.hd
  have hτd : τ + 1 < d := H.τd
  have hθd : τ + 1 < (d : ℝ) := hτd
  have hτ0 := H.τ0
  have hHc := r26t8a_Hj_continuous hchi hδ H.C1 j
  have hGc : Continuous fun u : Euc d => r26t8a_keps s ε (x - u) :=
    (r26t8a_keps_continuous s ε hε).comp (continuous_const.sub continuous_id)
  have hdc : Continuous fun u : Euc d => r26t8a_dkeps s ε (x - u) j :=
    (r26t8a_dkeps_continuous s ε hε j).comp (continuous_const.sub continuous_id)
  have hB : ∀ w : Euc d, r26t8a_keps s ε w ≤ (ε ^ 2) ^ (-s / 2) :=
    fun w => r26t8a_keps_le_const hs hε w
  have hD : ∀ (w : Euc d) (j : Fin d), |r26t8a_dkeps s ε w j| ≤ s * (ε ^ 2) ^ (-s / 2 - 1 / 2) :=
    fun w j => r26t8a_dkeps_le_const hs hε w j
  have hB0 : 0 ≤ (ε ^ 2) ^ (-s / 2) := Real.rpow_nonneg (by positivity) _
  have hCχ0 : 0 ≤ Cχ / δ := (norm_nonneg _).trans (hCχ 0)
  have gH : R26P10GP y τ (fun u => r26t8a_Hj chi y δ h j u) :=
    r26t8a_p10a_gp_of_bound H.hb zero_le_one (fun u _ => by
      rw [one_mul, abs_of_nonneg (norm_nonneg _)]; exact r26t8a_Hj_bound hchi y δ j u)
  have gDj : R26P10GP y (τ + 1) (fun u => r26t8a_Dj chi y δ h j u) := by
    have g1 := r26t8a_p10a_gp_add H.hdb
      (r26t8a_p10a_gp_of_bound H.hb1 hCχ0 (φ := fun u => ‖h u‖) (ψ := fun u => Cχ / δ * ‖h u‖)
        (fun u _ => by rw [abs_of_nonneg (by positivity), abs_of_nonneg (norm_nonneg _)]))
    exact r26t8a_p10a_gp_of_bound g1 zero_le_one (fun u _ => by
      have := r26t8a_Dj_bound hchi y hδ hCχ (h := h) j u
      rw [one_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg hCχ0 (norm_nonneg _)))]
      exact this)
  have hIdc := r26t8a_Dj_continuousOn hchi y δ H.C1 j
  have I1 : Integrable (fun u => -r26t8a_dkeps s ε (x - u) j * r26t8a_Hj chi y δ h j u) := by
    refine r26t8a_p10a_gp_integrable (y := y) (τ := τ) hd hτ0 (by linarith) ?_ ?_
    · exact r26t8a_p10a_gp_of_bound gH (B := s * (ε ^ 2) ^ (-s / 2 - 1 / 2)) (by positivity)
        (fun u _ => by
          rw [abs_mul, abs_neg]
          exact mul_le_mul_of_nonneg_right (hD (x - u) j) (abs_nonneg _))
    · exact (hdc.neg.mul hHc).aestronglyMeasurable
  have I2 : Integrable (fun u => r26t8a_keps s ε (x - u) * r26t8a_Dj chi y δ h j u) := by
    refine r26t8a_p10a_gp_integrable (y := y) (τ := τ + 1) hd (by linarith) (by linarith) ?_ ?_
    · exact r26t8a_p10a_gp_of_bound gDj (B := (ε ^ 2) ^ (-s / 2)) hB0 (fun u _ => by
        rw [abs_mul, abs_of_nonneg (r26t8a_keps_nonneg s ε _)]
        exact mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _))
    · refine r26t8a_p10a_aesm hd y ?_
      exact (hGc.continuousOn).mul hIdc
  have I3 : Integrable (fun u => r26t8a_keps s ε (x - u) * r26t8a_Hj chi y δ h j u) := by
    refine r26t8a_p10a_gp_integrable (y := y) (τ := τ) hd hτ0 (by linarith) ?_ ?_
    · exact r26t8a_p10a_gp_of_bound gH (B := (ε ^ 2) ^ (-s / 2)) hB0 (fun u _ => by
        rw [abs_mul, abs_of_nonneg (r26t8a_keps_nonneg s ε _)]
        exact mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _))
    · exact (hGc.mul hHc).aestronglyMeasurable
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := EuclideanSpace.single j 1)
    (f := fun u => r26t8a_keps s ε (x - u)) (g := r26t8a_Hj chi y δ h j)
    (by simpa only [r26t8a_fderiv_Gamma s hε] using I1)
    (by simpa only [r26t8a_fderiv_Hj hchi hδ H.C1 j] using I2) I3
    (fun u _ => (r26t8a_Gamma_hasFDerivAt s hε x u).differentiableAt)
    (fun u _ => (r26t8a_hasFDerivAt_Hj hchi hδ H.C1 j u).differentiableAt)
  simp only [r26t8a_fderiv_Hj hchi hδ H.C1 j, r26t8a_fderiv_Gamma s hε] at key
  refine ⟨I2, by simpa using I1.neg, ?_⟩
  rw [key, ← integral_neg]
  congr 1
  funext u
  ring

end HRS.MS.R26T8A
