import HRS.MS.R26T8AA01j

/-!
# S8.2 T8A A01 (part k): `ρ ‖∇Q‖` is integrable
For a `PairCorrector` `Q`, `z ↦ ρ z ‖pairGradX Q z w‖` and `z ↦ ρ z ‖pairGradX Q w z‖` are Lebesgue integrable.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_a01_grad_int (hd : 2 ≤ d) (a beta M A : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hA : 0 ≤ A) {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (w : Euc d) :
    Integrable (fun z => rho z * ‖pairGradX Q z w‖) ∧ Integrable (fun z => rho z * ‖pairGradX Q w z‖) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hs1 : (1 : ℝ) ≤ criticalS d := by unfold criticalS; linarith
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd hs0.le (by unfold criticalS; linarith) ha hbeta hrho).1
  have hρc : Continuous rho := hρs.continuous
  have hrho0 : ∀ x, 0 ≤ rho x := hprob.nonneg
  have hI : Integrable (fun z => rho z * (jbracket z ^ M * pole w z)) :=
    (r26t8a_f25_wd_integrable hprob _).1 (r26t8a_a01_pole_int hd hM ha hbeta hrho w)
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.smooth.of_le (by norm_num)
  have hjw : 0 ≤ jbracket w ^ M := Real.rpow_nonneg (s83_jb_pos w).le _
  have key : ∀ (u v : Euc d), u ≠ v → ‖pairGradX Q u v‖ ≤ A * (jbracket u ^ M * jbracket v ^ M) * pole u v := by
    intro u v huv
    have h1 := (le_add_of_nonneg_right (norm_nonneg (pairGradY Q u v))).trans (hQ.gradient u v huv)
    refine h1.trans ?_
    have hp := r26t8a_a01_grad_pole huv hs1
    have h0 : 0 ≤ A * HRS.MS.Phase2S82.pairWeight M u v :=
      mul_nonneg hA (mul_nonneg (Real.rpow_nonneg (s83_jb_pos u).le _) (Real.rpow_nonneg (s83_jb_pos v).le _))
    exact mul_le_mul_of_nonneg_left hp h0
  have hae : ∀ᵐ z : Euc d ∂volume, z ≠ w := compl_mem_ae_iff.mpr (measure_singleton w)
  have hdom : Integrable (fun z => A * jbracket w ^ M * (rho z * (jbracket z ^ M * pole w z))) := hI.const_mul _
  have hbd : ∀ z : Euc d, ∀ B : ℝ, B ≤ A * (jbracket z ^ M * jbracket w ^ M) * pole w z →
      rho z * B ≤ A * jbracket w ^ M * (rho z * (jbracket z ^ M * pole w z)) := by
    intro z B hB
    calc rho z * B ≤ rho z * (A * (jbracket z ^ M * jbracket w ^ M) * pole w z) :=
          mul_le_mul_of_nonneg_left hB (hrho0 z)
      _ = _ := by ring
  constructor
  · refine Integrable.mono' hdom ?_ ?_
    · exact r26t8a_p10a_aesm hd w (hρc.continuousOn.mul (r26t8a_a01_gradX_cont_fst hQ2 w).norm)
    · filter_upwards [hae] with z hz
      rw [Real.norm_of_nonneg (mul_nonneg (hrho0 z) (norm_nonneg _))]
      refine hbd z _ ?_
      have := key z w hz
      rwa [r26t8a_a01_pole_comm z w] at this
  · refine Integrable.mono' hdom ?_ ?_
    · exact r26t8a_p10a_aesm hd w (hρc.continuousOn.mul (r26t8a_a01_gradX_cont_snd hQ2 w).norm)
    · filter_upwards [hae] with z hz
      rw [Real.norm_of_nonneg (mul_nonneg (hrho0 z) (norm_nonneg _))]
      refine hbd z _ ?_
      have := key w z hz.symm
      calc ‖pairGradX Q w z‖ ≤ A * (jbracket w ^ M * jbracket z ^ M) * pole w z := this
        _ = _ := by ring

end HRS.MS.R26T8A
