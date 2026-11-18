import HRS.MC.S7PIL5
import HRS.MC.S7PIJB3

/-!
# Packet piG3 (PI-G3): convergence and equicontinuity of the projected derivatives

`s7_PIG_conv_equicont_proof`.  Route: spatial Lipschitz bound of `projHeatD` (constant `cbNorm 5 Φ`, uniform in `L`),
time Lipschitz bound (`s7_PIB_lip_proj_proof`, `s7_PIB_lip_proof`), pointwise convergence (`s7_PIB_proj_limit_proof`),
and an abstract compactness lemma turning pointwise convergence plus equicontinuity into uniform convergence.
Namespace `HRS.MC.Sec7.S7PIG3`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIG3

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- second countability of the path space (local instance, as in `S7PIA.lean`) -/
local instance s7pig3_pathSpace_sc {m T : ℝ} : SecondCountableTopology (PathSpace d m T) :=
  inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, NegSobolev d m))

/-- Lipschitz dependence of `projHeatD` on the base point, uniformly in the projection of norm `≤ 1`. -/
theorem S7PIG3_proj_lip_space {m T : ℝ} (γ : ℝ → Measure (PathSpace d m T))
    (hγp : ∀ u, IsProbabilityMeasure (γ u)) (P : PathSpace d m T →L[ℝ] PathSpace d m T) (hP : ‖P‖ ≤ 1)
    {Φ : PathSpace d m T → ℝ} (hΦ : MemCb 5 Φ) (j : ℕ) (hj : j ≤ 4) (u : ℝ) (y y' : PathSpace d m T) :
    ‖projHeatD γ Φ P j u y - projHeatD γ Φ P j u y'‖ ≤ cbNorm 5 Φ * ‖y - y'‖ := by
  have := hγp u
  have hj5 : j ≤ 5 := by omega
  have hcont : Continuous (iteratedFDeriv ℝ j Φ) :=
    hΦ.1.continuous_iteratedFDeriv (m := j) (by exact_mod_cast hj5)
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ j Φ) :=
    hΦ.1.differentiable_iteratedFDeriv (m := j) (by
      have : ((j : ℕ) : WithTop ℕ∞) < ((5 : ℕ) : WithTop ℕ∞) := by exact_mod_cast (by omega : j < 5)
      exact_mod_cast this)
  have hK0 : 0 ≤ cbNorm 5 Φ := HRS.MC.Sec7.S7PIL.S7PIL_cbNorm_nonneg hΦ 0
  have hK : ∀ x, ‖fderiv ℝ (iteratedFDeriv ℝ j Φ) x‖ ≤ cbNorm 5 Φ := fun x => by
    rw [norm_fderiv_iteratedFDeriv]
    exact HRS.MC.Sec7.S7PIL.S7PIL_le_cbNorm hΦ (by omega) x
  have hlip : ∀ a b, ‖iteratedFDeriv ℝ j Φ a - iteratedFDeriv ℝ j Φ b‖ ≤ cbNorm 5 Φ * ‖a - b‖ := fun a b =>
    (convex_univ (𝕜 := ℝ) (E := PathSpace d m T)).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hdiff x) (fun x _ => hK x) (Set.mem_univ b) (Set.mem_univ a)
  have hint : ∀ y : PathSpace d m T, Integrable (fun z => iteratedFDeriv ℝ j Φ (P (y + z))) (γ u) := fun y =>
    Integrable.of_bound (C := ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖)
      (hcont.comp (by fun_prop : Continuous fun z : PathSpace d m T => P (y + z))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => HRS.MC.Sec7.PIA.pia_le_sup hΦ hj5 (P (y + z)))
  unfold projHeatD
  rw [← integral_sub (hint y) (hint y')]
  have hb := norm_integral_le_of_norm_le_const (μ := γ u)
    (f := fun z => iteratedFDeriv ℝ j Φ (P (y + z)) - iteratedFDeriv ℝ j Φ (P (y' + z)))
    (C := cbNorm 5 Φ * ‖y - y'‖) (Filter.Eventually.of_forall fun z => by
      refine (hlip _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hK0
      rw [← map_sub, show y + z - (y' + z) = y - y' by abel]
      exact (P.le_opNorm _).trans (by nlinarith [norm_nonneg (y - y')]))
  simpa [Measure.real] using hb

/-- Continuity from a joint modulus. -/
theorem S7PIG3_contOn {B E : Type*} [NormedAddCommGroup B] [NormedAddCommGroup E] {s : Set ℝ}
    (F : ℝ → E) (Y : ℝ → B) (hY : ContinuousOn Y s) (a b : ℝ)
    (h : ∀ τ ∈ s, ∀ σ ∈ s, ‖F τ - F σ‖ ≤ a * |τ - σ| + b * ‖Y τ - Y σ‖) : ContinuousOn F s := by
  intro σ hσ
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun τ => a * |τ - σ| + b * ‖Y τ - Y σ‖) (𝓝[s] σ) (𝓝 0) := by
    have e1 : Tendsto (fun τ : ℝ => |τ - σ|) (𝓝[s] σ) (𝓝 0) := by
      have : Tendsto (fun τ : ℝ => |τ - σ|) (𝓝 σ) (𝓝 0) := by
        simpa using ((continuous_id.sub continuous_const).abs (f := fun τ : ℝ => τ - σ)).tendsto σ
      exact this.mono_left nhdsWithin_le_nhds
    have e2 : Tendsto (fun τ => ‖Y τ - Y σ‖) (𝓝[s] σ) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (hY σ hσ)
    simpa using (e1.const_mul a).add (e2.const_mul b)
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall fun τ hτ => h τ hτ σ hσ) h1

/-- Pointwise convergence plus equicontinuity on a compact set gives uniform convergence. -/
theorem S7PIG3_unif {E : Type*} [NormedAddCommGroup E] {s : Set ℝ} (hs : IsCompact s)
    (F : ℕ → ℝ → E) (F0 : ℝ → E)
    (heq : ∀ σ ∈ s, ∀ ε : ℝ, 0 < ε → ∀ᶠ τ in 𝓝[s] σ, (∀ L, ‖F L τ - F L σ‖ ≤ ε) ∧ ‖F0 τ - F0 σ‖ ≤ ε)
    (hpt : ∀ σ ∈ s, Tendsto (fun L => F L σ) atTop (𝓝 (F0 σ))) (ε : ℝ) (hε : 0 < ε) :
    ∃ L0 : ℕ, ∀ L ≥ L0, ∀ τ ∈ s, ‖F L τ - F0 τ‖ ≤ ε := by
  refine hs.induction_on (p := fun t => ∃ L0 : ℕ, ∀ L ≥ L0, ∀ τ ∈ t, ‖F L τ - F0 τ‖ ≤ ε)
    ⟨0, by simp⟩ ?_ ?_ ?_
  · rintro t t' htt' ⟨L0, h⟩
    exact ⟨L0, fun L hL τ hτ => h L hL τ (htt' hτ)⟩
  · rintro t t' ⟨L0, h⟩ ⟨L1, h'⟩
    refine ⟨max L0 L1, fun L hL τ hτ => ?_⟩
    rcases hτ with hτ | hτ
    · exact h L (le_trans (le_max_left _ _) hL) τ hτ
    · exact h' L (le_trans (le_max_right _ _) hL) τ hτ
  · intro σ hσ
    have h1 := (heq σ hσ (ε / 3) (by positivity)).and (self_mem_nhdsWithin : s ∈ 𝓝[s] σ)
    have h2 : ∀ᶠ L in atTop, ‖F L σ - F0 σ‖ ≤ ε / 3 := by
      have := tendsto_iff_norm_sub_tendsto_zero.1 (hpt σ hσ)
      exact this.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < ε / 3))
    obtain ⟨L0, hL0⟩ := eventually_atTop.1 h2
    refine ⟨{τ | ((∀ L, ‖F L τ - F L σ‖ ≤ ε / 3) ∧ ‖F0 τ - F0 σ‖ ≤ ε / 3) ∧ τ ∈ s}, h1, L0, ?_⟩
    rintro L hL τ ⟨⟨hq1, hq2⟩, -⟩
    have := hq1 L
    have h3 := hL0 L hL
    have h4 : ‖F L τ - F0 τ‖ ≤ ‖F L τ - F L σ‖ + ‖F L σ - F0 σ‖ + ‖F0 σ - F0 τ‖ := by
      calc ‖F L τ - F0 τ‖ = ‖(F L τ - F L σ) + (F L σ - F0 σ) + (F0 σ - F0 τ)‖ := by congr 1; abel
        _ ≤ _ := (norm_add₃_le)
    rw [norm_sub_rev (F0 σ)] at h4
    linarith

/-- **G3** (convergence and equicontinuity of the projected derivatives), proof. -/
theorem s7_PIG_conv_equicont_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (γ : ℝ → Measure (PathSpace d m T)) (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
    (hγp : ∀ u, IsProbabilityMeasure (γ u)) (Pj : ℕ → (PathSpace d m T →L[ℝ] PathSpace d m T))
    (hPj : ∀ L w, Pj L w = projPoly m T hT.le L w) (hP1 : ∀ L, ‖Pj L‖ ≤ 1)
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w))
    {Φ : PathSpace d m T → ℝ} (hΦ : MemCb 5 Φ) (Y : ℝ → PathSpace d m T) (hY : ContinuousOn Y (Set.Icc 0 T))
    (j : ℕ) (hj : j ≤ 2) :
    ContinuousOn (fun τ => iteratedFDeriv ℝ j (heatFn γ Φ τ) (Y τ)) (Set.Icc 0 T) ∧
    (∀ L, ContinuousOn (fun τ => projHeatD γ Φ (Pj L) j τ (Y τ)) (Set.Icc 0 T)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ‖projHeatD γ Φ (Pj L) j τ (Y τ) - iteratedFDeriv ℝ j (heatFn γ Φ τ) (Y τ)‖ ≤ ε := by
  obtain ⟨C1, hC1⟩ := HRS.MC.Sec7.S7PIL.s7_PIB_lip_proj_proof R m hm T hT γ hγ
  obtain ⟨C2, hC2⟩ := HRS.MC.Sec7.S7PIL.s7_PIB_lip_proof R m hm T hT γ hγ hγp
  have hK0 : 0 ≤ cbNorm 5 Φ := HRS.MC.Sec7.S7PIL.S7PIL_cbNorm_nonneg hΦ 0
  set K := cbNorm 5 Φ with hKdef
  set A : ℝ := |C1| + |C2| with hAdef
  have hj3 : j ≤ 3 := by omega
  have hj4 : j ≤ 4 := by omega
  have hA1 : C1 ≤ A := (le_abs_self C1).trans (by linarith [abs_nonneg C2])
  have hA2 : C2 ≤ A := (le_abs_self C2).trans (by linarith [abs_nonneg C1])
  have hlim : ∀ τ y, Tendsto (fun L => projHeatD γ Φ (Pj L) j τ y) atTop
      (𝓝 (iteratedFDeriv ℝ j (heatFn γ Φ τ) y)) := fun τ y =>
    HRS.MC.Sec7.S7PIJ.s7_PIB_proj_limit_proof γ hγp Pj hconv hΦ j hj4 τ y
  -- spatial Lipschitz bounds
  have hsp : ∀ L τ y y', ‖projHeatD γ Φ (Pj L) j τ y - projHeatD γ Φ (Pj L) j τ y'‖ ≤ K * ‖y - y'‖ :=
    fun L τ y y' => S7PIG3_proj_lip_space γ hγp (Pj L) (hP1 L) hΦ j hj4 τ y y'
  have hsp0 : ∀ τ y y', ‖iteratedFDeriv ℝ j (heatFn γ Φ τ) y - iteratedFDeriv ℝ j (heatFn γ Φ τ) y'‖ ≤
      K * ‖y - y'‖ := fun τ y y' =>
    le_of_tendsto ((hlim τ y).sub (hlim τ y')).norm (Filter.Eventually.of_forall fun L => hsp L τ y y')
  -- time Lipschitz bounds
  have htm : ∀ L, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ y,
      ‖projHeatD γ Φ (Pj L) j τ y - projHeatD γ Φ (Pj L) j σ y‖ ≤ A * K * |τ - σ| := by
    intro L τ hτ σ hσ y
    refine (hC1 Pj hPj L Φ hΦ τ hτ σ hσ j hj3 y).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA1 hK0) (abs_nonneg _)
  have htm0 : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ y,
      ‖iteratedFDeriv ℝ j (heatFn γ Φ τ) y - iteratedFDeriv ℝ j (heatFn γ Φ σ) y‖ ≤ A * K * |τ - σ| := by
    intro τ hτ σ hσ y
    refine (hC2 Φ hΦ τ hτ σ hσ j hj3 y).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA2 hK0) (abs_nonneg _)
  -- joint modulus along the curve
  have hmodL : ∀ L, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ‖projHeatD γ Φ (Pj L) j τ (Y τ) - projHeatD γ Φ (Pj L) j σ (Y σ)‖ ≤ (A * K) * |τ - σ| + K * ‖Y τ - Y σ‖ := by
    intro L τ hτ σ hσ
    calc _ = ‖(projHeatD γ Φ (Pj L) j τ (Y τ) - projHeatD γ Φ (Pj L) j σ (Y τ)) +
            (projHeatD γ Φ (Pj L) j σ (Y τ) - projHeatD γ Φ (Pj L) j σ (Y σ))‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (htm L τ hτ σ hσ _) (hsp L σ _ _))
  have hmod0 : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ‖iteratedFDeriv ℝ j (heatFn γ Φ τ) (Y τ) - iteratedFDeriv ℝ j (heatFn γ Φ σ) (Y σ)‖ ≤
        (A * K) * |τ - σ| + K * ‖Y τ - Y σ‖ := by
    intro τ hτ σ hσ
    calc _ = ‖(iteratedFDeriv ℝ j (heatFn γ Φ τ) (Y τ) - iteratedFDeriv ℝ j (heatFn γ Φ σ) (Y τ)) +
            (iteratedFDeriv ℝ j (heatFn γ Φ σ) (Y τ) - iteratedFDeriv ℝ j (heatFn γ Φ σ) (Y σ))‖ := by
              congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (htm0 τ hτ σ hσ _) (hsp0 σ _ _))
  refine ⟨S7PIG3_contOn _ Y hY _ _ hmod0, fun L => S7PIG3_contOn _ Y hY _ _ (hmodL L), ?_⟩
  intro ε hε
  have hmod : ∀ σ ∈ Set.Icc (0 : ℝ) T, Tendsto (fun τ => (A * K) * |τ - σ| + K * ‖Y τ - Y σ‖)
      (𝓝[Set.Icc 0 T] σ) (𝓝 0) := by
    intro σ hσ
    have e1 : Tendsto (fun τ : ℝ => |τ - σ|) (𝓝[Set.Icc 0 T] σ) (𝓝 0) := by
      have : Tendsto (fun τ : ℝ => |τ - σ|) (𝓝 σ) (𝓝 0) := by
        simpa using ((continuous_id.sub continuous_const).abs (f := fun τ : ℝ => τ - σ)).tendsto σ
      exact this.mono_left nhdsWithin_le_nhds
    have e2 : Tendsto (fun τ => ‖Y τ - Y σ‖) (𝓝[Set.Icc 0 T] σ) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 (hY σ hσ)
    simpa using (e1.const_mul (A * K)).add (e2.const_mul K)
  obtain ⟨L0, hL0⟩ := S7PIG3_unif (isCompact_Icc (a := (0 : ℝ)) (b := T))
    (fun L τ => projHeatD γ Φ (Pj L) j τ (Y τ)) (fun τ => iteratedFDeriv ℝ j (heatFn γ Φ τ) (Y τ))
    (fun σ hσ e he => by
      have h1 := ((hmod σ hσ).eventually (ge_mem_nhds he)).and (self_mem_nhdsWithin : Set.Icc 0 T ∈ 𝓝[Set.Icc 0 T] σ)
      filter_upwards [h1] with τ hτ
      exact ⟨fun L => (hmodL L τ hτ.2 σ hσ).trans hτ.1, (hmod0 τ hτ.2 σ hσ).trans hτ.1⟩)
    (fun σ _ => hlim σ (Y σ)) ε hε
  exact ⟨L0, hL0⟩

end HRS.MC.Sec7.S7PIG3

end
