import HRS.MS.R26T8AG0
import HRS.MS.S82WK6

/-!
# S8.2 observed-time layer, packet T8A.G02 (native adapter): cutoff convergence in value, gradient and generator

Merged `w_cutoff_seq` (S82WK6) with the conjuncts reordered; `r26t8a_configPoleEnvelope M = u4Env M M` definitionally.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_graph_cutoff_convergence (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (F : EucConfig d N → ℝ)
    (hF : ContDiffOn ℝ 2 F (eucCollisionSet d N)ᶜ)
    (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hb : ∀ X, X ∉ eucCollisionSet d N → |F X| + ‖fderiv ℝ F X‖ + ‖iteratedFDeriv ℝ 2 F X‖ ≤
      A * r26t8a_configPoleEnvelope M X) :
    ∃ Fn : ℕ → EucConfig d N → ℝ,
      (∀ n, ContDiff ℝ 2 (Fn n) ∧ HasCompactSupport (Fn n) ∧ tsupport (Fn n) ⊆ (eucCollisionSet d N)ᶜ) ∧
      Tendsto (fun n => eLpNorm (Fn n - F) 2 (canonicalP d N a beta)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun X => particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (Fn n) X -
        particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F X) 2 (canonicalP d N a beta))
        atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun n => eLpNorm (fun X => HRS.MS.Phase2S82.configGrad (Fn n) X i -
        HRS.MS.Phase2S82.configGrad F X i) 2 (canonicalP d N a beta)) atTop (𝓝 0) := by
  obtain ⟨f, h1, h2, h3, h4⟩ := HRS.MS.S82W.w_cutoff_seq hd (by omega) ha hbeta hF hM hA hb
  exact ⟨f, h1, h2, h4, h3⟩

end HRS.MS.R26T8A
