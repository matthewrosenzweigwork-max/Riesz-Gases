import HRS.Uniform.Q45Win

/-!
# Q45: `windowPath` is a measurable path-valued random variable
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

lemma windowPath_cont_aux {T : ℝ} (Y : ℝ → Ω → E) {ω : Ω}
    (hω : ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) :
    Continuous fun t : Set.Icc (0 : ℝ) T => Y (0 + (t : ℝ)) ω := by
  have := continuousOn_iff_continuous_restrict.1 hω
  have e : (fun t : Set.Icc (0 : ℝ) T => Y (0 + (t : ℝ)) ω) =
      (Set.Icc 0 T).restrict (fun t => Y t ω) := by
    funext t; simp [Set.restrict]
  rw [e]; exact this

lemma pcm_windowPath {T : ℝ} (Y : ℝ → Ω → E) {ω : Ω}
    (hω : ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) (t : Set.Icc (0 : ℝ) T) :
    pcm (windowPath 0 T Y ω) t = Y (t : ℝ) ω := by
  have h : windowPath 0 T Y ω =
      (⟨fun t => Y (0 + (t : ℝ)) ω, windowPath_cont_aux Y hω⟩ : C(Set.Icc (0 : ℝ) T, E)) := by
    unfold windowPath
    exact dif_pos (windowPath_cont_aux Y hω)
  rw [h]
  simp [pcm]

lemma samplePath_windowPath {T : ℝ} (hT : 0 < T) (Y : ℝ → Ω → E) {ω : Ω}
    (hω : ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) (g : ℕ) (hg : 1 ≤ g) (i : Fin (g + 1)) :
    samplePath hT.le g (windowPath 0 T Y ω) i = Y (unifPart T g i) ω := by
  unfold samplePath
  have hi : (i : ℝ) * T / g ∈ Set.Icc 0 T := ⟨by positivity, gridT_le hT hg i⟩
  rw [pcm_windowPath Y hω, Set.projIcc_of_mem hT.le hi]
  rfl

lemma aemeasurable_windowPath (P : Measure Ω) {T : ℝ} (hT : 0 < T) (Y : ℝ → Ω → E)
    (hY : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (Y t))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) :
    AEMeasurable (windowPath 0 T Y) P := by
  have hF : ∀ g : ℕ, Measurable fun ω => hatPath T (g + 1) (fun i => Y (unifPart T (g + 1) i) ω) := by
    intro g
    have : Measurable fun ω => (fun i : Fin (g + 1 + 1) => Y (unifPart T (g + 1) i) ω) :=
      measurable_pi_iff.2 fun i => hY _ ⟨unifPart_nonneg hT.le _ _, gridT_le hT (Nat.le_add_left 1 g) i⟩
    exact (continuous_hatPath hT (Nat.le_add_left 1 g)).measurable.comp this
  refine aemeasurable_of_tendsto_metrizable_ae atTop (fun g => (hF g).aemeasurable) ?_
  filter_upwards [hc] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g0, hg0⟩ := hatPath_sample_close hT (windowPath 0 T Y ω) (show 0 < ε / 2 by positivity)
  refine ⟨g0, fun g hg => ?_⟩
  have := hg0 (g + 1) (by omega) (Nat.le_add_left 1 g)
  have e : (fun i : Fin (g + 1 + 1) => Y (unifPart T (g + 1) i) ω) =
      samplePath hT.le (g + 1) (windowPath 0 T Y ω) := by
    funext i
    rw [samplePath_windowPath hT Y hω (g + 1) (Nat.le_add_left 1 g) i]
  rw [dist_eq_norm, e]
  linarith

end HRS.Uniform.Q45
