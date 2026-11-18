import HRS.Commutator.Whole.LocalAuxSAMP12

/-!
# `v_{>1} = K̃ * |∇|^α v` and `vhi_cube_sampling` (packet CMX-SAMP, helper file 13)
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ} {s : ℝ}

theorem vhi_identity (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {K : Euc d → ℝ}
    (hK : Integrable K)
    (hKF : ∀ ξ : Euc d, 𝓕 (fun x : Euc d => ((K x : ℝ) : ℂ)) ξ =
      (((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-alphaE d s) : ℝ) : ℂ))
    (hKq : MemLp (fun x : Euc d => K (-x)) (ENNReal.ofReal (p1E d s).conjExponent) volume)
    {v : Euc d → Euc d} {L : ℝ≥0} {w : Euc d → Euc d} {F : ℝ} (hLip : LipschitzWith L v)
    (hrep : ∀ i, IsFracDerivRep (alphaE d s) (fun x => v x i) (fun x => w x i))
    (hnorm : eLpNorm (fun x => ‖w x‖) (ENNReal.ofReal (p1E d s)) volume ≤ ENNReal.ofReal F) :
    ∃ w' : Euc d → Euc d, Measurable w' ∧
      eLpNorm (fun x => ‖w' x‖) (ENNReal.ofReal (p1E d s)) volume ≤ ENNReal.ofReal F ∧
      (∀ i, IsFracDerivRep (alphaE d s) (fun x => v x i) (fun x => w' x i)) ∧
      ∀ x, Pgt 1 v x = ∫ y, K (-(x - y)) • w' y := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hα1, hαd, hα0, hp1, hαp⟩ := exponents hd hs0 hsd
  have hp0 : 0 < p1E d s := by linarith
  obtain ⟨w', hw'm, hrep', hw'⟩ := exists_meas_rep hrep hnorm
  obtain ⟨C, hC, hb⟩ := vhi_bounded_core d
  have hPc : Continuous (Pgt 1 v) := (hb v L hLip).1
  have hw'L : MemLp (fun x => ‖w' x‖) (ENNReal.ofReal (p1E d s)) volume := by
    rw [memLp_iff]; exact lt_of_le_of_lt hw' ENNReal.ofReal_lt_top
  refine ⟨w', hw'm, hw', hrep', fun x => ?_⟩
  have hw'P : MemLp w' (ENNReal.ofReal (p1E d s)) volume :=
    (memLp_norm_iff hw'm.aestronglyMeasurable).1 hw'L
  have hint := conv_integrable hp1 hKq hw'P x
  ext i
  have hPg : ∀ x' : Euc d, (Pgt 1 v x') i = v x' i - ∫ y, psiL 1 y * v (x' - y) i := by
    intro x'
    show (v x' - Pleq 1 v x') i = _
    rw [PiLp.sub_apply, Pleq_apply_comp v x' (psi_smul_integrable hLip x') i]
  have hR : (∫ y, K (-(x - y)) • w' y) i = ∫ y, K (-(x - y)) * w' y i := by
    have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm hint
    simpa using this.symm
  rw [hR, hPg x]
  have hvc : Continuous (fun x => v x i) :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hLip.continuous
  refine scalar_identity hd1 hα1 hK hKF hp1 hKq hvc (cmxHLS_lip_bound hLip i) ?_
    ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).measurable.comp hw'm)
    (lintegral_comp_ne_top hw'm hp0 hw' i) (hrep' i) x
  have : (fun x => v x i - ∫ y, psiL 1 y * v (x - y) i) = fun x => (Pgt 1 v x) i :=
    funext fun x => (hPg x).symm
  rw [this]
  exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hPc

theorem vhi_cube_core (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (L : ℝ≥0) (w : Euc d → Euc d) (F : ℝ),
      LipschitzWith L v →
      (∀ i, IsFracDerivRep (alphaE d s) (fun x => v x i) (fun x => w x i)) →
      eLpNorm (fun x => ‖w x‖) (ENNReal.ofReal (p1E d s)) volume ≤ ENNReal.ofReal F →
        cubeSupNorm (p1E d s) (Pgt 1 v) ≤ ENNReal.ofReal (C * F) := by
  obtain ⟨hα1, hαd, hα0, hp1, hαp⟩ := exponents hd hs0 hsd
  have hp0 : 0 < p1E d s := by linarith
  obtain ⟨K, hK, hKF, hKq, c, hc, hcs⟩ := kernel_data hd hs0 hsd
  refine ⟨c.toReal + 1, by positivity, fun v L w F hLip hrep hnorm => ?_⟩
  obtain ⟨w', hw'm, hw', -, hid⟩ := vhi_identity hd hs0 hsd hK hKF hKq hLip hrep hnorm
  have hW : Measurable fun y => ‖w' y‖ₑ := hw'm.enorm
  have hu : ∀ x, ‖Pgt 1 v x‖ₑ ≤ ∫⁻ y, ‖K (-(x - y))‖ₑ * ‖w' y‖ₑ := by
    intro x
    rw [hid x]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    rw [enorm_smul]
  have h1 := hcs (fun y => ‖w' y‖ₑ) hW (fun x => ‖Pgt 1 v x‖ₑ) hu
  have hpne : ENNReal.ofReal (p1E d s) ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  have h2 : eLpNorm (fun x => ‖w' x‖) (ENNReal.ofReal (p1E d s)) volume =
      (∫⁻ y, ‖w' y‖ₑ ^ (p1E d s)) ^ (1 / p1E d s) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top
      hw'm.norm.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
    simp only [enorm_norm]
  unfold cubeSupNorm
  refine h1.trans ?_
  rw [← h2]
  calc c * eLpNorm (fun x => ‖w' x‖) (ENNReal.ofReal (p1E d s)) volume
      ≤ ENNReal.ofReal (c.toReal + 1) * ENNReal.ofReal F := by
        gcongr
        calc c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hc).symm
          _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal ((c.toReal + 1) * F) := (ENNReal.ofReal_mul (by positivity)).symm

end HRS.Commutator.Whole.SAMP1
