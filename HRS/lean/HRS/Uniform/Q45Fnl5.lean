import HRS.Uniform.Q45Fnl4

/-!
# Q45: Proposition 3.21 in the degenerate case `T = 0`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The constant path on `[0,0]`. -/
def constPath (x : E) : PathSp 0 E := (⟨fun _ => x, continuous_const⟩ : C(Set.Icc (0 : ℝ) 0, E))

lemma pcm_constPath (x : E) (t : Set.Icc (0 : ℝ) 0) : pcm (constPath x) t = x := rfl

lemma norm_constPath_sub_le (x y : E) : ‖constPath x - constPath y‖ ≤ ‖x - y‖ :=
  norm_pcm_le _ (norm_nonneg _) fun t => by rw [pcm_sub, pcm_constPath, pcm_constPath]

lemma norm_constPath (x : E) : ‖constPath x‖ = ‖x‖ := by
  refine le_antisymm (norm_pcm_le _ (norm_nonneg _) fun t => by rw [pcm_constPath]) ?_
  have := norm_pcm_apply_le (constPath x) ⟨0, le_rfl, le_rfl⟩
  rwa [pcm_constPath] at this

lemma continuous_constPath : Continuous (constPath : E → PathSp 0 E) :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun x y => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact norm_constPath_sub_le x y).continuous

lemma windowPath_zero {Ω : Type*} (Y : ℝ → Ω → E) (ω : Ω) : windowPath 0 0 Y ω = constPath (Y 0 ω) := by
  have hc : Continuous fun t : Set.Icc (0 : ℝ) 0 => Y (0 + (t : ℝ)) ω := by
    have : (fun t : Set.Icc (0 : ℝ) 0 => Y (0 + (t : ℝ)) ω) = fun _ => Y 0 ω := by
      funext t
      have : (t : ℝ) = 0 := le_antisymm t.2.2 t.2.1
      simp [this]
    rw [this]; exact continuous_const
  rw [windowPath_eq_mk Y hc]
  refine ContinuousMap.ext fun t => ?_
  have : (t : ℝ) = 0 := le_antisymm t.2.2 t.2.1
  simp [constPath, this]

lemma aemeasurable_windowPath_zero {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (Y : ℝ → Ω → E) (hY : Measurable (Y 0)) : AEMeasurable (windowPath 0 0 Y) P := by
  have : windowPath 0 0 Y = fun ω => constPath (Y 0 ω) := funext (windowPath_zero Y)
  rw [this]
  exact (continuous_constPath.measurable.comp hY).aemeasurable


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

/-- At `t = 0` the stochastic convolution vanishes almost surely. -/
lemma stochConv_zero_ae (S : EvolData H E) (M : ℝ → Ω → H) (Z : Ω → E) (hZm : Measurable Z)
    (hZ : IsStochConv P S.VE S.j M 0 0 Z) : ∀ᵐ ω ∂P, Z ω = 0 := by
  have hle : ∫⁻ ω, ‖Z ω‖ₑ ^ 2 ∂P ≤ 0 := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨δ, hδ, h⟩ := hZ (ε : ℝ) (by exact_mod_cast hε)
    have := h 0 (fun _ => 0) rfl rfl (fun _ _ _ => le_rfl) (fun i => i.elim0)
    simp only [riemannSum, Finset.univ_eq_empty, Finset.sum_empty, sub_zero] at this
    rw [zero_add]
    exact (this.trans_eq (by simp)).le
  have h0 : ∫⁻ ω, ‖Z ω‖ₑ ^ 2 ∂P = 0 := le_antisymm hle bot_le
  rw [lintegral_eq_zero_iff' (hZm.enorm.pow_const 2).aemeasurable] at h0
  filter_upwards [h0] with ω hω
  have : ‖Z ω‖ₑ = 0 := by
    simpa using hω
  simpa using this

end HRS.Uniform.Q45
