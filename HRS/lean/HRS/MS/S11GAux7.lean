import HRS.MS.S11GAux6
import HRS.MS.S111BDAux4
import HRS.MS.S11GAux8
import HRS.MS.R2S11Aux20

/-!
# S11G: `S11GaussCompare`

The Gaussian covariance interpolation on the window space `C([0,T]; B_m)` for the shifted window of the preparation
evolution and the unshifted window of the stationary evolution: both are centered Gaussian laws on the Banach space
(`s111_shifted_window_gaussian`), and `s11g_gaussian_comparison` applies.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S11G

open HRS.Whole
open HRS (Euc)

/-- the comparison once both windows are a.e. measurable with centered Gaussian laws -/
theorem s11g_compare_core (d : ℕ) (T : ℝ) {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (W₁ : Ω₁ → R2X d T) (W₂ : Ω₂ → R2X d T) (hm1 : AEMeasurable W₁ P₁) (hm2 : AEMeasurable W₂ P₂)
    (hg1 : HRS.IsCenteredGaussian (P₁.map W₁)) (hg2 : HRS.IsCenteredGaussian (P₂.map W₂))
    {F : R2X d T → ℝ} (hF : ContDiff ℝ 2 F) {Mbd δ : ℝ} (h2 : ∀ x, ‖iteratedFDeriv ℝ 2 F x‖ ≤ Mbd)
    (hcov : ∀ M : (R2X d T) [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 →
      |∫ ζ, M ![W₁ ζ, W₁ ζ] ∂P₁ - ∫ ζ, M ![W₂ ζ, W₂ ζ] ∂P₂| ≤ δ) :
    |∫ ζ, F (W₁ ζ) ∂P₁ - ∫ ζ, F (W₂ ζ) ∂P₂| ≤ 1 / 2 * Mbd * δ := by
  have hint : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : Ω → R2X d T) (G : R2X d T → ℝ),
      AEMeasurable W P → Continuous G → ∫ ζ, G (W ζ) ∂P = ∫ x, G x ∂(P.map W) := by
    intro Ω _ P W G hW hG
    exact (integral_map hW hG.aestronglyMeasurable).symm
  have key := HRS.MS.S11G.s11g_gaussian_comparison (P₁.map W₁) (P₂.map W₂) hg1 hg2 hF
    (Mb := Mbd) (δ := δ) h2
    (fun M hM => by
      have c : Continuous fun x : R2X d T => M ![x, x] := by fun_prop
      rw [← hint P₁ _ _ hm1 c, ← hint P₂ _ _ hm2 c]
      exact hcov M hM)
  rw [hint P₁ _ _ hm1 hF.continuous, hint P₂ _ _ hm2 hF.continuous]
  exact key.2.2

theorem s11g_gaussCompare (d : ℕ) (s a β γ T lam : ℝ) :
    HRS.MS.R2S11.S11GaussCompare d s a β γ T lam := by
  intro ρβ _ _ F hF Mbd δ h2 Ω₁ Ω₂ _ _ P₁ P₂ _ _ Z₁ Z₂ hZ₁ hZ₂ u hu hcov
  rcases lt_trichotomy T 0 with hT | hT | hT
  · -- empty window: the path space is a point
    have hsub : Subsingleton (R2X d T) := ⟨fun a b => ContinuousMap.ext fun x =>
      absurd (x.2.1.trans x.2.2) (not_le.2 hT)⟩
    have hconst : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (W : Ω → R2X d T), ∫ ζ, F (W ζ) ∂P = F 0 := by
      intro Ω _ P _ W
      simp only [Subsingleton.elim (W _) (0 : R2X d T)]
      simp
    rw [hconst P₁, hconst P₂, sub_self, abs_zero]
    have hMb : 0 ≤ Mbd := (norm_nonneg (iteratedFDeriv ℝ 2 F 0)).trans (h2 0)
    have hδ : 0 ≤ δ := by
      have := hcov 0 (by simp)
      simpa using this
    positivity
  · subst hT
    obtain ⟨hm1, hg1⟩ := HRS.MS.S11G.s11g_window_gaussian_zero d P₁ _ _ _ u _ Z₁ (hZ₁ (u + 1)) hu
    obtain ⟨hm2, hg2⟩ := HRS.MS.S11G.s11g_window_gaussian_zero d P₂ _ _ _ 0 _ Z₂ (hZ₂ (0 + 1)) le_rfl
    exact s11g_compare_core d 0 P₁ P₂ _ _ hm1 hm2 hg1 hg2 hF h2 hcov
  · obtain ⟨hm1, hg1, -⟩ := HRS.MS.S111BD.s111_shifted_window_gaussian d P₁ _ _ _ T u (u + T) _ Z₁
      (hZ₁ (u + T)) hT hu le_rfl
    obtain ⟨hm2, hg2, -⟩ := HRS.MS.S111BD.s111_shifted_window_gaussian d P₂ _ _ _ T 0 (0 + T) _ Z₂
      (hZ₂ (0 + T)) hT le_rfl le_rfl
    exact s11g_compare_core d T P₁ P₂ _ _ hm1 hm2 hg1 hg2 hF h2 hcov

end HRS.MS.S11G
