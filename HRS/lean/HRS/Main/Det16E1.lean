import HRS.Main.Det16C5
import HRS.Main.Det16D1
import HRS.Main.Det16D2
import HRS.Main.Det16B1

/-!
# det16e: assembly pieces for Example A.16

* `det16e_path_data`: for `N ≥ 1` the deterministic path `x_N`, the Dirac form of `law (flucPath ..)` and a pointwise
  description of the Dirac point in terms of `x_N`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.Det16

open HRS

variable {d : ℕ}

/-- For `N ≥ 1`: `law (flucPath)` is a Dirac mass at a path `ξ` with `ξ^t = σ_N ofMeasureDiff_{γ'}(emp x(t), ρ_N t)`,
where `x` is a deterministic path with `X^t = x(t)` a.s. -/
theorem det16e_path_data {S : MainData d} (hβ : ∀ N, S.invβ N = 0) {R : ∀ N, Realization d N}
    (hflow : SelectedFlows S R) {r : ℕ} {Λ : ℝ} (hr : d + 1 ≤ r) (hmf : MeanFieldRegularity S r Λ)
    (hV1 : Torus.IsCk 1 S.V) {N : ℕ} (hN : 1 ≤ N) (Y : Config d N)
    (hdet : ∀ᵐ ω ∂(R N).P, (R N).X₀ ω = Y) {γ' : ℝ} (hγ' : (d : ℝ) < 2 * γ') :
    ∃ x : ℝ≥0 → Config d N, (∀ᵐ ω ∂(R N).P, ∀ t : ℝ≥0, (t : ℝ) ≤ S.T → (R N).X t ω = x t) ∧
      ∃ ξ : PathSpace d γ' S.T,
        law (R N).P (flucPath γ' S.T (S.sigma N) (R N).X (S.ρ N)) = Measure.dirac ξ ∧
        ∀ t : Set.Icc (0 : ℝ) S.T, PathSpace.at' ξ t =
          S.sigma N • NegSobolev.ofMeasureDiff γ' (empirical (x (Real.toNNReal t)))
            (withDensityReal (S.ρ N t)) := by
  have hsol := det16c_strong hβ hflow hN
  have hU := det16c_pathwiseUnique hβ hflow hN
  obtain ⟨x, hxc, -, hx⟩ := det16d_det_path (R N).P (S.dyn N) (hβ N) S.T (R N).X₀ Y hdet
    (R N).W hU (R N).X hsol
  have hcont := det16d_path_cont S hr hmf hV1 hN hγ' (S.sigma N) x hxc
  exact ⟨x, hx, det16d_xPath γ' S.T (S.sigma N) (S.ρ N) x hcont,
    det16d_law_flucPath_dirac (R N).P γ' S.T (S.sigma N) (R N).X (S.ρ N) x hx hcont, fun t => rfl⟩

end HRS.Main.Det16
