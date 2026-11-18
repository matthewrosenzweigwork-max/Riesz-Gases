import HRS.MS.R26T8AA02c

/-!
# S8.2 T8A A02 (part d): a jointly measurable representative of `pairJ` off the diagonal
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_a02_pairJ_meas (d : ℕ) (hd : 2 ≤ d) (a beta M A : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hA : 0 ≤ A) {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) :
    ∃ Pm : Euc d → Euc d → ℝ, Measurable (fun p : Euc d × Euc d => Pm p.1 p.2) ∧
      ∀ x y, x ≠ y → pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x y = Pm x y := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : criticalS d < d := by unfold criticalS; linarith
  have hQt : Conormal (4 + 2) 1 M (criticalS d - 2) A Q := hQ.tangential
  obtain ⟨Jm, hJm, hJmeq⟩ := r26t8a_a02_oneJ_meas d hd a beta M A ha hbeta hM hA hrho hQ
  have hmc : Continuous (fun z => ∫ x, oneJ (critCoeff d a beta rho) (fun u => Q u z) x
      ∂(HRS.Whole.withDensityReal rho)) :=
    (r26t8a_g14_row_smooth d hd 4 1 a beta M (criticalS d) ha hbeta hM hsd hrho Q A hA hQt).continuous
  refine ⟨fun x y => (Jm x y - ∫ t, oneJ (critCoeff d a beta rho) (fun u => Q u y) t ∂(HRS.Whole.withDensityReal rho)) +
      (Jm y x - ∫ t, oneJ (critCoeff d a beta rho) (fun u => Q u x) t ∂(HRS.Whole.withDensityReal rho)), ?_, ?_⟩
  · have h1 : Measurable (fun p : Euc d × Euc d => Jm p.1 p.2) := hJm
    have h2 : Measurable (fun p : Euc d × Euc d => Jm p.2 p.1) := hJm.comp (measurable_snd.prodMk measurable_fst)
    have h3 : Measurable (fun p : Euc d × Euc d => ∫ t, oneJ (critCoeff d a beta rho) (fun u => Q u p.2) t
        ∂(HRS.Whole.withDensityReal rho)) := hmc.measurable.comp measurable_snd
    have h4 : Measurable (fun p : Euc d × Euc d => ∫ t, oneJ (critCoeff d a beta rho) (fun u => Q u p.1) t
        ∂(HRS.Whole.withDensityReal rho)) := hmc.measurable.comp measurable_fst
    exact (h1.sub h3).add (h2.sub h4)
  · intro x y hxy
    rw [r26t8a_a01_pairJ_decomp _ _ hQ.symmetric x y, hJmeq x y hxy, hJmeq y x hxy.symm]

end HRS.MS.R26T8A
