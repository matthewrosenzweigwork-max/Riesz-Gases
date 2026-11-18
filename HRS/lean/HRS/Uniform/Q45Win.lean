import HRS.Uniform.Q45Lim3

/-!
# Q45: the initial path `t ↦ V(t,0) j x` and measurability of `windowPath`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The transported initial path `t ↦ V(t,0) j x` as an element of `C([0,T];E)`. -/
def vpath (S : EvolData H E) {T : ℝ} (hev : S.IsEvolution T) (x : H) : PathSp T E :=
  (⟨fun t => S.VE (t : ℝ) 0 (S.j x), by
    have hc := hev.cont_E (S.j x)
    have := hc.comp_continuous (show Continuous (fun t : Set.Icc (0 : ℝ) T => ((t : ℝ), (0 : ℝ))) by
      fun_prop) (fun t => ⟨le_rfl, t.2.1, t.2.2⟩)
    exact this⟩ : C(Set.Icc (0 : ℝ) T, E))

lemma pcm_vpath (S : EvolData H E) {T : ℝ} (hev : S.IsEvolution T) (x : H) (t : Set.Icc (0 : ℝ) T) :
    pcm (vpath S hev x) t = S.VE (t : ℝ) 0 (S.j x) := rfl

lemma norm_vpath_sub_le {T K : ℝ} (hT : 0 ≤ T) (S : EvolData H E) (hS : S.MaxHyp T K) (x x' : H) :
    ‖vpath S hS.1 x - vpath S hS.1 x'‖ ≤ detConst T K * ‖x - x'‖ := by
  refine norm_pcm_le _ (mul_nonneg (detConst_pos T K).le (norm_nonneg _)) fun t => ?_
  rw [pcm_sub, pcm_vpath, pcm_vpath, ← map_sub, ← map_sub]
  exact hS.norm_le hT le_rfl t.2.1 t.2.2 (x - x')

lemma continuous_vpath {T K : ℝ} (hT : 0 ≤ T) (S : EvolData H E) (hS : S.MaxHyp T K) :
    Continuous (vpath S hS.1 : H → PathSp T E) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hC := detConst_pos T K
  have : ∀ᶠ x' in 𝓝 x, ‖x' - x‖ < ε / detConst T K := by
    have := Metric.ball_mem_nhds x (show 0 < ε / detConst T K by positivity)
    filter_upwards [this] with x' hx'
    simpa [dist_eq_norm] using hx'
  filter_upwards [this] with x' hx'
  rw [dist_eq_norm]
  calc ‖vpath S hS.1 x' - vpath S hS.1 x‖ ≤ detConst T K * ‖x' - x‖ := norm_vpath_sub_le hT S hS x' x
    _ < detConst T K * (ε / detConst T K) := by gcongr
    _ = ε := by field_simp

end HRS.Uniform.Q45
