import HRS.Uniform.Q45Win2
import HRS.Uniform.Q45Sep3
import HRS.Uniform.Q45Cov9
import HRS.Uniform.Q45Max
import HRS.Uniform.Q45Gauss

/-!
# Q45 (Lemma 3.20): the Bochner tensor `E[W ⊗ W]` of a path-valued random variable
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS.LindebergAux

section Meas

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma continuous_tmul : Continuous (fun p : Y × Y => tmul p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun q : Y × Y => ‖q.1 - p.1‖) (𝓝 p) (𝓝 0) := by
    have := (continuous_fst.tendsto p).sub_const p.1
    simpa using this.norm
  have h2 : Tendsto (fun q : Y × Y => ‖q.2 - p.2‖) (𝓝 p) (𝓝 0) := by
    have := (continuous_snd.tendsto p).sub_const p.2
    simpa using this.norm
  have h3 : Tendsto (fun q : Y × Y => ‖q.2‖) (𝓝 p) (𝓝 ‖p.2‖) :=
    (continuous_snd.tendsto p).norm
  have h4 : Tendsto (fun q : Y × Y => ‖q.1 - p.1‖ * ‖q.2‖ + ‖p.1‖ * ‖q.2 - p.2‖) (𝓝 p)
      (𝓝 (0 * ‖p.2‖ + ‖p.1‖ * 0)) := (h1.mul h3).add (h2.const_mul _)
  rw [zero_mul, mul_zero, add_zero] at h4
  exact squeeze_zero (fun q => norm_nonneg _) (fun q => norm_tmul_sub_le _ _ _ _) h4

end Meas

section Win

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

lemma aemeasurable_windowPath' (P : Measure Ω) {T : ℝ} (hT : 0 < T) (Y : ℝ → Ω → E)
    (hY : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Y t) P)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) :
    AEMeasurable (windowPath 0 T Y) P := by
  have hF : ∀ g : ℕ, AEMeasurable (fun ω => hatPath T (g + 1) (fun i => Y (HRS.unifPart T (g + 1) i) ω)) P := by
    intro g
    have : AEMeasurable (fun ω => (fun i : Fin (g + 1 + 1) => Y (HRS.unifPart T (g + 1) i) ω)) P :=
      aemeasurable_pi_iff.2 fun i => hY _ ⟨HRS.LindebergAux.unifPart_nonneg hT.le _ _, gridT_le hT (Nat.le_add_left 1 g) i⟩
    exact (continuous_hatPath hT (Nat.le_add_left 1 g)).measurable.comp_aemeasurable this
  refine aemeasurable_of_tendsto_metrizable_ae atTop (fun g => hF g) ?_
  filter_upwards [hc] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g0, hg0⟩ := hatPath_sample_close hT (windowPath 0 T Y ω) (show 0 < ε / 2 by positivity)
  refine ⟨g0, fun g hg => ?_⟩
  have := hg0 (g + 1) (by omega) (Nat.le_add_left 1 g)
  have e : (fun i : Fin (g + 1 + 1) => Y (HRS.unifPart T (g + 1) i) ω) =
      samplePath hT.le (g + 1) (windowPath 0 T Y ω) := by
    funext i
    rw [samplePath_windowPath hT Y hω (g + 1) (Nat.le_add_left 1 g) i]
  rw [dist_eq_norm, e]
  linarith

/-- The path norm is the supremum of the pointwise norms. -/
lemma enorm_windowPath_le {T : ℝ} (Y : ℝ → Ω → E) {ω : Ω}
    (hω : ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) :
    ‖windowPath 0 T Y ω‖ₑ ≤ ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Y t ω‖ₑ := by
  by_cases htop : (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Y t ω‖ₑ) = ⊤
  · rw [htop]; exact le_top
  set s := ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Y t ω‖ₑ with hs
  have hne : s ≠ ⊤ := htop
  have hle : ∀ t : Set.Icc (0 : ℝ) T, ‖Y (t : ℝ) ω‖ ≤ s.toReal := by
    intro t
    have : ‖Y (t : ℝ) ω‖ₑ ≤ s := le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => ‖Y t ω‖ₑ) (t : ℝ) t.2
    rw [← ofReal_norm] at this
    exact (ENNReal.ofReal_le_iff_le_toReal hne).1 this
  have hn : ‖windowPath 0 T Y ω‖ ≤ s.toReal := by
    refine norm_pcm_le _ ENNReal.toReal_nonneg fun t => ?_
    rw [pcm_windowPath Y hω]
    exact hle t
  rw [← ofReal_norm]
  calc ENNReal.ofReal ‖windowPath 0 T Y ω‖ ≤ ENNReal.ofReal s.toReal := ENNReal.ofReal_le_ofReal hn
    _ = s := ENNReal.ofReal_toReal hne

instance pathSp_secondCountable {T : ℝ} : SecondCountableTopology (PathSp T E) :=
  inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, E))

end Win

end HRS.Uniform.Q45
