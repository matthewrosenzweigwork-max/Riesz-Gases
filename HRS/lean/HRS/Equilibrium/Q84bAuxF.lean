/-
# HRS.Equilibrium.Q84bAuxF — packet Q84b: measurability and integrability of the envelope `w`
-/
import HRS.Equilibrium.Q84bAuxE

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84b

variable {d : ℕ} {s : ℝ}

theorem q84b_measurable_grad (φ : Torus d → ℝ) : Measurable (Torus.grad φ) := by
  unfold Torus.grad gradient
  exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ (Torus.lift φ))).comp (q84b_measurable_rep d)

theorem q84b_measurable_gradFst (ψ : Torus d → Torus d → ℝ) (y : Torus d) :
    Measurable (fun x => gradFst ψ x y) :=
  q84b_measurable_grad (fun z => ψ z y)

theorem q84b_measurable_forceField (ρ : Torus d → ℝ) : Measurable (forceField d s ρ) :=
  q84b_measurable_grad _

/-- `w(x, ·)` is integrable (critical exponent `s = d/2`). -/
theorem q84b_w_integrable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (x : Torus d) :
    Integrable (fun z => wEnv s x z) := by
  refine ⟨(PairCorrAux.measurable_wEnv s x).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => by
    have := PairCorrAux.one_le_wEnv s x z; simp only [Pi.zero_apply]; linarith)]
  exact lt_of_le_of_lt (PairCorrAux.radial_B0 hd hcrit x) ENNReal.ofReal_lt_top

theorem q84b_w_integral_le (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ x : Torus d, ∫ z, wEnv s x z ≤ W := by
  refine ⟨(PairCorrAux.cdR d * ((1 / d + 1 / s) * 1 ^ s) + 2), ?_, fun x => ?_⟩
  · have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hs0 : 0 < s := by rw [hcrit]; linarith
    have := PairCorrAux.cdR_nonneg d
    positivity
  · have h := PairCorrAux.radial_B0 hd hcrit x
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => by
      have := PairCorrAux.one_le_wEnv s x z; simp only [Pi.zero_apply]; linarith)
      (PairCorrAux.measurable_wEnv s x).aestronglyMeasurable]
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hs0 : 0 < s := by rw [hcrit]; linarith
    have := PairCorrAux.cdR_nonneg d
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

theorem q84b_wEnv_sub (x u : Torus d) : wEnv s x (x - u) = wEnv s u 0 := by
  unfold wEnv rTrunc
  rw [PairCorrAux.eucDist_sub_zero x (x - u), sub_sub_cancel]

end HRS.Q84b
