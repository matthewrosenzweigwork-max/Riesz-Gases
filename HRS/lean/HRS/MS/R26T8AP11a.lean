import HRS.MS.R26T8AP00b
import HRS.Whole.Q34Aux1
import HRS.Kernel.SymbolClass

/-!
# S8.2 nonlocal layer, packet T8A.P11a: finite jets and local mass of the general Riesz potential kernel
Jets of `|z|^(alpha-d)` from `HRS.norm_iteratedFDeriv_rpow_norm_le`; local mass from `HRS.Whole.Q34.lintegral_ball_rpow`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_p11a_mass (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ) (halpha : 0 < alpha) (had : alpha < d)
    (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun z : Euc d => ‖z‖ ^ (alpha - (d : ℝ))) (ball (0 : Euc d) R) ∧
      ∫ z in ball (0 : Euc d) R, ‖z‖ ^ (alpha - (d : ℝ)) = sphereArea d * (R ^ alpha / alpha) := by
  have hd1 : 1 ≤ d := by omega
  have hl := HRS.Whole.Q34.lintegral_ball_rpow (d := d) hd1 hR (a := (d : ℝ) - alpha) (by linarith)
  have hexp : -((d : ℝ) - alpha) = alpha - (d : ℝ) := by ring
  rw [hexp, show (d : ℝ) - ((d : ℝ) - alpha) = alpha by ring] at hl
  have hmeas : AEStronglyMeasurable (fun z : Euc d => ‖z‖ ^ (alpha - (d : ℝ)))
      (volume.restrict (ball (0 : Euc d) R)) :=
    (measurable_norm.pow_const _).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume.restrict (ball (0 : Euc d) R)] fun z : Euc d => ‖z‖ ^ (alpha - (d : ℝ)) :=
    Filter.Eventually.of_forall fun z => Real.rpow_nonneg (norm_nonneg _) _
  have hint : IntegrableOn (fun z : Euc d => ‖z‖ ^ (alpha - (d : ℝ))) (ball (0 : Euc d) R) := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn, hl]
    exact ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  have hsA : 0 ≤ sphereArea d := by
    unfold sphereArea
    have : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by
      have : (0 : ℝ) < d := by exact_mod_cast hd1
      positivity)
    positivity
  have h2 := ofReal_integral_eq_lintegral_ofReal hint hnn
  rw [hl] at h2
  have hnn2 : 0 ≤ sphereArea d * (R ^ alpha / alpha) := by positivity
  have h3 : 0 ≤ ∫ z in ball (0 : Euc d) R, ‖z‖ ^ (alpha - (d : ℝ)) :=
    setIntegral_nonneg measurableSet_ball fun z _ => Real.rpow_nonneg (norm_nonneg _) _
  have := (ENNReal.ofReal_eq_ofReal_iff h3 hnn2).1 h2
  exact this

theorem r26t8a_riesz_potential_jets (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ContDiffOn ℝ ∞ (fun z : Euc d => ‖z‖ ^ (alpha - (d : ℝ))) {z | z ≠ 0} ∧
      (∀ j ≤ k, ∀ z : Euc d, z ≠ 0 →
        ‖iteratedFDeriv ℝ j (fun v : Euc d => ‖v‖ ^ (alpha - (d : ℝ))) z‖ ≤
          C * ‖z‖ ^ (alpha - (d : ℝ) - j)) ∧
      ∀ R : ℝ, 0 < R → IntegrableOn (fun z : Euc d => ‖z‖ ^ (alpha - (d : ℝ))) (ball (0 : Euc d) R) ∧
        ∫ z in ball (0 : Euc d) R, ‖z‖ ^ (alpha - (d : ℝ)) ≤ C * R ^ alpha := by
  choose Cj hCj0 hCj using fun j => HRS.norm_iteratedFDeriv_rpow_norm_le (V := Euc d) (alpha - (d : ℝ)) j
  set Cm : ℝ := sphereArea d / alpha with hCm
  have hsA : 0 ≤ sphereArea d := by
    unfold sphereArea
    have : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by
      have : (0 : ℝ) < d := by exact_mod_cast (show 1 ≤ d by omega)
      positivity)
    positivity
  have hCm0 : 0 ≤ Cm := div_nonneg hsA halpha.le
  refine ⟨Cm + ∑ j ∈ Finset.range (k + 1), Cj j,
    add_nonneg hCm0 (Finset.sum_nonneg fun j _ => hCj0 j), ?_, ?_, ?_⟩
  · exact fun z hz => (HRS.contDiffAt_rpow_norm (V := Euc d) (alpha - (d : ℝ)) hz).contDiffWithinAt
  · intro j hj z hz
    have h1 : Cj j ≤ ∑ j ∈ Finset.range (k + 1), Cj j :=
      Finset.single_le_sum (f := Cj) (fun j _ => hCj0 j) (Finset.mem_range.2 (by omega))
    refine (hCj j z hz).trans ?_
    have hfac : 0 ≤ ‖z‖ ^ (alpha - (d : ℝ) - j) := Real.rpow_nonneg (norm_nonneg _) _
    nlinarith
  · intro R hR
    obtain ⟨hi, hv⟩ := r26t8a_p11a_mass d hd alpha halpha had R hR
    refine ⟨hi, ?_⟩
    rw [hv]
    have hs : 0 ≤ ∑ j ∈ Finset.range (k + 1), Cj j := Finset.sum_nonneg fun j _ => hCj0 j
    have hRa : 0 ≤ R ^ alpha := Real.rpow_nonneg hR.le _
    have : sphereArea d * (R ^ alpha / alpha) = Cm * R ^ alpha := by
      rw [hCm]; ring
    rw [this]
    nlinarith

end HRS.MS.R26T8A
