import HRS.MS.R26T8AG0
import HRS.MS.S82WA04

/-!
# S8.2 observed-time layer, packet T8A.G04 (native adapter): actual Gibbs generator graph closure

The merged `Phase2S82.gibbs_graph_closure` (S82WA04) is exactly the statement of the packet (the pole envelope
`r26t8a_configPoleEnvelope` is the merged `Phase2S82.configPoleEnvelope`).  G02/G03 are not needed: the merged proof carries
its own cut-off (`w_cutoff_seq`) and mollification (`w_smooth_approx`) steps.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_gibbs_graph_closure (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (F : EucConfig d N → ℝ)
    (hF : ContDiffOn ℝ 2 F (eucCollisionSet d N)ᶜ)
    (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hb : ∀ X, X ∉ eucCollisionSet d N →
      |F X| + ‖fderiv ℝ F X‖ + ‖iteratedFDeriv ℝ 2 F X‖ ≤
        A * r26t8a_configPoleEnvelope M X) :
    GeneratorClosure a beta F
      (particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F) ∧
      ∫ X, particleGenerator (quadraticGradientDyn d (criticalS d) a beta) F X
        ∂canonicalP d N a beta = 0 :=
  Phase2S82.gibbs_graph_closure d N hd hN a beta ha hbeta F hF M A hM hA hb

end HRS.MS.R26T8A
