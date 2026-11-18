import HRS.MS.Fp81S21GaussG4U3
import HRS.MS.ProClosureS111WeightedJets

/-! Continuity of the G4 cost on finite weighted Sobolev tests. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal ContDiff
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111

/-- The exact squared G4 cost is continuous under convergence in its own
weighted Sobolev norm, provided the functions have finite cost. -/
theorem fp81s21_g4_cost_continuous {d : ℕ} (f : Euc d → ℝ)
    (F : ℕ → Euc d → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hF : ∀ n, ContDiff ℝ 2 (F n))
    (hff : weightedSobolevE 2 (2 * (d : ℝ) + 4) f < ⊤)
    (hFf : ∀ n, weightedSobolevE 2 (2 * (d : ℝ) + 4) (F n) < ⊤)
    (hconv : Tendsto (fun n => fp81s21_g4_J d (F n - f)) atTop (𝓝 0)) :
    Tendsto (fun n => fp81s21_g4_J d (F n)) atTop (𝓝 (fp81s21_g4_J d f)) := by
  let P : ℝ := 2 * (d : ℝ) + 4
  have hmF : ∀ n, MemLp (weightedJets 2 P (F n)) 2 volume :=
    fun n => (weightedJets_memLp_iff (hF n)).2 (hFf n)
  have hmf : MemLp (weightedJets 2 P f) 2 volume :=
    (weightedJets_memLp_iff hf).2 hff
  have hsub (n : ℕ) : weightedJets 2 P (F n - f) =
      weightedJets 2 P (F n) - weightedJets 2 P f := by
    have hn : weightedJets 2 P (-f) = -weightedJets 2 P f := by
      simpa using (weightedJets_smul (r := 2) (Pw := P) (-1 : ℝ) hf)
    have ha := weightedJets_add (Pw := P) (hF n) hf.neg
    change weightedJets 2 P (F n + -f) =
      weightedJets 2 P (F n) + weightedJets 2 P (-f) at ha
    rw [hn] at ha
    simpa only [sub_eq_add_neg] using ha
  have hme : ∀ n, weightedSobolevE 2 P (F n - f) < ⊤ := by
    intro n
    apply (weightedJets_memLp_iff ((hF n).sub hf)).1
    change MemLp (weightedJets 2 P (F n - f)) 2 volume
    rw [hsub]
    exact (hmF n).sub hmf
  have hsqrt : Tendsto (fun n => (weightedSobolevE 2 P (F n - f)).toReal)
      atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hconv
    simpa only [Function.comp_def, fp81s21_g4_J, Real.sqrt_sq ENNReal.toReal_nonneg, Real.sqrt_zero, P] using h
  have he : Tendsto (fun n => eLpNorm (weightedJets 2 P (F n) - weightedJets 2 P f) 2 volume)
      atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hsqrt
    have heq (n : ℕ) : eLpNorm (weightedJets 2 P (F n) - weightedJets 2 P f) 2 volume =
        weightedSobolevE 2 P (F n - f) := by
      rw [← hsub n]
      exact weightedJets_eLpNorm ((hF n).sub hf)
    simpa only [heq, ENNReal.ofReal_toReal (hme _).ne, ENNReal.ofReal_zero] using h
  have hlp := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => weightedJets 2 P (F n)) hmF (weightedJets 2 P f) hmf).2 he
  have hn := hlp.norm
  have hr : Tendsto (fun n => (weightedSobolevE 2 P (F n)).toReal) atTop
      (𝓝 (weightedSobolevE 2 P f).toReal) := by
    simpa only [Lp.norm_toLp, weightedJets_eLpNorm (hF _), weightedJets_eLpNorm hf] using hn
  simpa only [fp81s21_g4_J] using hr.pow 2

#print axioms fp81s21_g4_cost_continuous
end HRS.Fp81.S21
