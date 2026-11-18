import HRS.MC.IID5
import HRS.MC.E718A
import HRS.MC.S7ChaosIID

/-!
# iid transfer, part 2: Proposition 7.18 in the independent-Gaussian form from the bridge

`HRS.MC.S7ChaosIID` is imported for the TYPE of `HRS.chaos_iid_representation` only; the two theorems below take
that statement as an explicit first hypothesis `bridge` and never use the (sorried) theorem itself.  Given `bridge`
they follow from the correlated statements `E718.chaos_laws_not_tight_proof` and `E718.chaos_no_L2_limit_proof`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.IID

open HRS HRS.Sec7 HRS.MC.Sec7

/-- The correlated representation of the iid chaos limits, obtained from the bridge. -/
theorem iid_to_correlated (bridge : type_of% @HRS.chaos_iid_representation) {d : ℕ} (hd : 2 ≤ d) {s : ℝ}
    (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ)
    (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) (S : ℕ → ℕ → ℝ) (hS : s7_IsCovFactor d s β ρ e S)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (g : ℕ → Ω → ℝ)
    (hg : IsStdGaussianSeq P g) (Q : ℝ → Ω → ℝ)
    (hQ : ∀ ε, 0 < ε → TendstoL2 P
      (chaosSection (s7_conjCoeff S (s7_kernelCoeff ρ e (hCut d s φ ε))) g) (Q ε)) :
    ∃ G : ℕ → Ω → ℝ, s7_GaussData d s β ρ e P G ∧
      ∀ ε, 0 < ε → AEMeasurable (Q ε) P ∧ s7_IsChaosLimit d s β ρ e P G (hCut d s φ ε) (Q ε) := by
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  obtain ⟨G, hG, -, hT⟩ := bridge hd hs0 hsd hβ ρ hρ e he S hS P g hg
  refine ⟨G, hG, fun ε hε => ⟨(hQ ε hε).1.aemeasurable, ?_⟩⟩
  exact (hT (hCut d s φ ε) (kernelCoeff_cut_isSymHS hd hs0 hsd hρ hφ he hε)).2 (Q ε) (hQ ε hε)

theorem chaos_laws_not_tight_iid_proof (bridge : type_of% @HRS.chaos_iid_representation) {d : ℕ}
    (hd : 2 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) (hnc : ∃ x y, φ x ≠ φ y) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) (S : ℕ → ℕ → ℝ) (hS : s7_IsCovFactor d s β ρ e S)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (g : ℕ → Ω → ℝ)
    (hg : IsStdGaussianSeq P g) (Q : ℝ → Ω → ℝ)
    (hQ : ∀ ε, 0 < ε → TendstoL2 P
      (chaosSection (s7_conjCoeff S (s7_kernelCoeff ρ e (hCut d s φ ε))) g) (Q ε))
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    ¬ IsTightMeasureSet (Set.range fun n : ℕ => P.map (Q (ε n))) := by
  obtain ⟨G, hG, hQ'⟩ := iid_to_correlated bridge hd hs hsd hβ ρ hρ φ hφ e he S hS P g hg Q hQ
  exact E718.chaos_laws_not_tight_proof hd hs hsd hβ ρ hρ φ hφ hnc e he P G hG Q hQ' ε hε0 hε

theorem chaos_no_L2_limit_iid_proof (bridge : type_of% @HRS.chaos_iid_representation) {d : ℕ}
    (hd : 2 ≤ d) {s : ℝ} (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) (hnc : ∃ x y, φ x ≠ φ y) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) (S : ℕ → ℕ → ℝ) (hS : s7_IsCovFactor d s β ρ e S)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (g : ℕ → Ω → ℝ)
    (hg : IsStdGaussianSeq P g) (Q : ℝ → Ω → ℝ)
    (hQ : ∀ ε, 0 < ε → TendstoL2 P
      (chaosSection (s7_conjCoeff S (s7_kernelCoeff ρ e (hCut d s φ ε))) g) (Q ε))
    (ε : ℕ → ℝ) (hε0 : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    ¬ ∃ Q₀ : Ω → ℝ, AEMeasurable Q₀ P ∧
      Tendsto (fun n : ℕ => ∫⁻ ω, ‖Q (ε n) ω - Q₀ ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
  obtain ⟨G, hG, hQ'⟩ := iid_to_correlated bridge hd hs hsd hβ ρ hρ φ hφ e he S hS P g hg Q hQ
  exact E718.chaos_no_L2_limit_proof hd hs hsd hβ ρ hρ φ hφ hnc e he P G hG Q hQ' ε hε0 hε

end HRS.MC.IID
