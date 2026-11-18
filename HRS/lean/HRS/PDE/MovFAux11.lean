import HRS.PDE.MovFAux10
import HRS.Stochastic.Duality

/-!
# MOVF Aux11: `IsC12Test` from a weak solution with `C^{m_*+2}` bounds (bridge `movT_isC12Test_of_weak`)

Route: the junk-free weak form of `HRS.Duality` (`MFWeak.of_regular`) makes `r ↦ ∫ψρ^r` Lipschitz (`pair_lipschitz_time`),
so the Fourier coefficients are continuous; bounded in `H^{m_*+2}` they are therefore norm-continuous in `H^{m_*+1}`
(`continuousInHs_of_bdd`), hence in `C²` (Sobolev embedding); the core `movf_isC12_core` finishes.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movf_coeffOf_eq_pair {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hc : Continuous ρ) (k : Lattice d) :
    PDE.coeffOf ρ k = ((pair (withDensityReal ρ) (Torus.cosMode (-k)) : ℝ) : ℂ) +
      ((pair (withDensityReal ρ) (Torus.sinMode (-k)) : ℝ) : ℂ) * Complex.I := by
  unfold PDE.coeffOf
  rw [PDE.funFourierCoeff_eq_int]
  have hmc : Continuous fun x : Torus d => UnitAddTorus.mFourier (-k) x := (UnitAddTorus.mFourier (-k)).continuous
  have hint : Integrable fun x : Torus d => UnitAddTorus.mFourier (-k) x * ((ρ x : ℝ) : ℂ) :=
    (hmc.mul (Complex.continuous_ofReal.comp hc)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hre : ∫ x : Torus d, RCLike.re (UnitAddTorus.mFourier (-k) x * ((ρ x : ℝ) : ℂ)) =
      ∫ x, ρ x * Torus.cosMode (-k) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Torus.cosMode, Torus.mode]
    ring
  have him : ∫ x : Torus d, RCLike.im (UnitAddTorus.mFourier (-k) x * ((ρ x : ℝ) : ℂ)) =
      ∫ x, ρ x * Torus.sinMode (-k) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [RCLike.im_to_complex, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero,
      Torus.sinMode, Torus.mode]
    ring
  rw [← integral_re_add_im hint, hre, him]
  unfold pair
  rw [PDE.MFPairing.integral_withDensityReal hρ.measurable hρ.nonneg,
    PDE.MFPairing.integral_withDensityReal hρ.measurable hρ.nonneg]
  rfl

end HRS

end
