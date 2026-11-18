import HRS.MC.E213U13c

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Fp81.S21

/-- The first Gaussian chaos is closed under convergence in the prescribed L^q. -/
theorem fp81s21_firstChaos_closed
    {B Ω : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → ℝ) (hξ : HRS.IsStdGaussianSeq P ξ)
    (hm : ∀ i, Measurable (ξ i)) (q : ℝ) (hq : 2 ≤ q)
    (Wn : ℕ → Ω → B) (W : Ω → B) (hW : AEStronglyMeasurable W P)
    (hlim : Tendsto (fun n => eLpNorm (fun ω => Wn n ω - W ω)
      (ENNReal.ofReal q) P) atTop (𝓝 0))
    (hn : ∀ n, HRS.InFirstChaos P ξ q (Wn n)) : HRS.InFirstChaos P ξ q W := by
  classical
  have hq0 : 0 < q := by linarith
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := ENNReal.one_le_ofReal.2 (by linarith)
  choose k c hc using fun n => (hn n).2
  let g : ℕ → ℕ → Ω → B := fun n m ω =>
    ∑ i ∈ Finset.range (k n m), ξ i ω • c n m i
  have hgm : ∀ n m, AEStronglyMeasurable (g n m) P := by
    intro n m
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (hm i).aestronglyMeasurable.smul_const _
  have ht : ∀ n, Tendsto (fun m => eLpNorm (g n m - Wn n)
      (ENNReal.ofReal q) P) atTop (𝓝 0) := by
    intro n
    apply (HRS.MC.E213U13.tendsto_lintegral_iff_eLpNorm
      (fun m => (hgm n m).sub (hn n).1) hq0).1
    exact hc n
  obtain ⟨mm, hmm⟩ := HRS.MC.E213U13.exists_diag hp g Wn W ht hlim
  refine ⟨hW, fun n => k n (mm n), fun n => c n (mm n), ?_⟩
  apply (HRS.MC.E213U13.tendsto_lintegral_iff_eLpNorm
    (fun n => (hgm n (mm n)).sub hW) hq0).2
  exact hmm

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_firstChaos_closed
