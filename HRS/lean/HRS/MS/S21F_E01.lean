import HRS.MS.S81G_Sing
import HRS.MS.S21F_E00

/-!
# S21F, packet R26-T3.E01: canonical and double-sum Hamiltonians agree

Wrapper of `s81g_Hs_eq` (S81G, merged) for `D = quadraticGradientDyn d s a β` (`D.V = confinement a`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem r26t3_hamiltonian (d N : ℕ) (s a β : ℝ) (k : Euc d → ℝ)
    (hk : ∀ x, k (-x) = k x) (X : EucConfig d N) :
    HRS.MS.MfeConf.sb1Hs (quadraticGradientDyn d s a β) k N X =
      HRS.Whole.canonicalHamiltonian k (confinement a) X :=
  HRS.MS.S81G.s81g_Hs_eq (D := quadraticGradientDyn d s a β) hk X

end HRS.MS.R26T3
