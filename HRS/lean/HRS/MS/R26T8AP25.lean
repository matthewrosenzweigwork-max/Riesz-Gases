import HRS.MS.S82P2Local
import HRS.MS.WadAux188

/-!
# S8.2 local Newton layer, packet T8A.P25: mean preservation for the weighted semigroup
Reduces to the merged S8.3 uniqueness `s85_semigroup_unique` (`U t f = Ulim t f`) and `s8d_mean_U`;
integrability from the weighted bound `|U t f| <= C <x>^M` and the Gaussian moment of `rho`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_weighted_mean (d : ℕ) (hd : 2 ≤ d) (a beta M : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 < M) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (U : ℝ → (Euc d → ℝ) → Euc d → ℝ)
    (hU : IsWeightedSemigroup (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) M U) :
    ∀ f : Euc d → ℝ, MemCM M f → ∀ t : ℝ, 0 ≤ t →
      Integrable (U t f) (HRS.Whole.withDensityReal rho) ∧
      ∫ x, U t f x ∂HRS.Whole.withDensityReal rho = ∫ x, f x ∂HRS.Whole.withDensityReal rho := by
  intro f hf t ht
  have hrho' : IsThermalEquilibrium d ((d : ℝ) / 2) a beta rho := hrho
  have hP : HRS.Whole.IsProbDensity rho := hrho'.1.1
  have hg := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho'
  have hjint := HRS.MS.Wad.s85_jb_integrable hP hg hM.le
  constructor
  · have hm := hU.maps t ht f hf
    have hw := HRS.MS.Wad.s83_wt_of_memCM hm
    exact Integrable.mono' (hjint.const_mul _) hm.1.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa using hw x)
  · have H : HRS.MS.Wad.S85Hyp d a beta (t + 1) M rho := ⟨hd, ha, hbeta, by linarith, hM.le, hrho'⟩
    rw [HRS.MS.Wad.s85_semigroup_unique hd ha hbeta hrho' hM hU ht hf]
    exact HRS.MS.Wad.s8d_mean_U H ht (by linarith) hf

end HRS.MS.R26T8A
