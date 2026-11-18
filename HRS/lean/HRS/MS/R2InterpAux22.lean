import HRS.MS.R2InterpAux21
import HRS.MC.S7PIG3

/-!
# S10.2 (worker S102), part 22 (packet G3): convergence and equicontinuity of the projected derivatives

Whole-space port of `s7_PIG_conv_equicont_proof`, with the time-Lipschitz bound of the projected heat derivatives (torus packet B2,
`s7_PIB_lip_proj`) as the explicit hypothesis `S102LipProj` (to be proved in the B-block; it is the only analytic input beyond the spatial
Lipschitz bound and pointwise convergence).  Its consequence for the unprojected heat derivatives (torus B4) follows by the limit `L → ∞`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ} {m T : ℝ}

/-- The time-Lipschitz bound of the projected heat derivatives, uniform in the projection (torus packet B2). -/
def S102LipProj (γ : ℝ → Measure (OscPath d m T)) (Pj : ℕ → (OscPath d m T →L[ℝ] OscPath d m T)) : Prop :=
  ∃ C : ℝ, ∀ (L : ℕ) (Φ : OscPath d m T → ℝ), MemCb 5 Φ → ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ v ∈ Set.Icc (0 : ℝ) T,
    ∀ j ≤ 3, ∀ y, ‖s102_projHeatD γ Φ (Pj L) j u y - s102_projHeatD γ Φ (Pj L) j v y‖ ≤
      C * cbNorm 5 Φ * |u - v|

/-- Lipschitz dependence of `s102_projHeatD` on the base point. -/
theorem s102_proj_lip_space (γ : ℝ → Measure (OscPath d m T)) (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (P : OscPath d m T →L[ℝ] OscPath d m T) (hP : ‖P‖ ≤ 1) {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ)
    (j : ℕ) (hj : j ≤ 4) (u : ℝ) (y y' : OscPath d m T) :
    ‖s102_projHeatD γ Φ P j u y - s102_projHeatD γ Φ P j u y'‖ ≤ cbNorm 5 Φ * ‖y - y'‖ := by
  haveI := hγp u
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
    (convex_univ (𝕜 := ℝ) (E := OscPath d m T)).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hdiff x) (fun x _ => hK x) (Set.mem_univ b) (Set.mem_univ a)
  have hint : ∀ y : OscPath d m T, Integrable (fun z => iteratedFDeriv ℝ j Φ (P (y + z))) (γ u) := fun y =>
    Integrable.of_bound (C := ⨆ z, ‖iteratedFDeriv ℝ j Φ z‖)
      (hcont.comp (by fun_prop : Continuous fun z : OscPath d m T => P (y + z))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => s102_le_sup hΦ hj5 (P (y + z)))
  unfold s102_projHeatD
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
theorem s102_contOn {B E : Type*} [NormedAddCommGroup B] [NormedAddCommGroup E] {s : Set ℝ}
    (F : ℝ → E) (Y : ℝ → B) (hY : ContinuousOn Y s) (a b : ℝ)
    (h : ∀ τ ∈ s, ∀ σ ∈ s, ‖F τ - F σ‖ ≤ a * |τ - σ| + b * ‖Y τ - Y σ‖) : ContinuousOn F s :=
  HRS.MC.Sec7.S7PIG3.S7PIG3_contOn F Y hY a b h

/-- **G3**: convergence and equicontinuity of the projected derivatives. -/
theorem s102_conv_equicont (γ : ℝ → Measure (OscPath d m T)) (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (Pj : ℕ → (OscPath d m T →L[ℝ] OscPath d m T)) (hP1 : ∀ L, ‖Pj L‖ ≤ 1)
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w)) (hLP : S102LipProj γ Pj)
    {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ) (Y : ℝ → OscPath d m T) (hY : ContinuousOn Y (Set.Icc 0 T))
    (j : ℕ) (hj : j ≤ 2) :
    ContinuousOn (fun τ => iteratedFDeriv ℝ j (r2HeatFn γ Φ τ) (Y τ)) (Set.Icc 0 T) ∧
    (∀ L, ContinuousOn (fun τ => s102_projHeatD γ Φ (Pj L) j τ (Y τ)) (Set.Icc 0 T)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ‖s102_projHeatD γ Φ (Pj L) j τ (Y τ) - iteratedFDeriv ℝ j (r2HeatFn γ Φ τ) (Y τ)‖ ≤ ε := by
  obtain ⟨C1, hC1⟩ := hLP
  have hK0 : 0 ≤ cbNorm 5 Φ := HRS.MC.Sec7.S7PIL.S7PIL_cbNorm_nonneg hΦ 0
  set K := cbNorm 5 Φ with hKdef
  set A : ℝ := |C1| with hAdef
  have hj3 : j ≤ 3 := by omega
  have hj4 : j ≤ 4 := by omega
  have hj5 : j ≤ 5 := by omega
  have hA1 : C1 ≤ A := le_abs_self C1
  have hlim : ∀ τ y, Tendsto (fun L => s102_projHeatD γ Φ (Pj L) j τ y) atTop
      (𝓝 (iteratedFDeriv ℝ j (r2HeatFn γ Φ τ) y)) := fun τ y =>
    s102_proj_limit γ hγp Pj hconv hΦ j hj5 τ y
  -- spatial Lipschitz bounds
  have hsp : ∀ L τ y y', ‖s102_projHeatD γ Φ (Pj L) j τ y - s102_projHeatD γ Φ (Pj L) j τ y'‖ ≤ K * ‖y - y'‖ :=
    fun L τ y y' => s102_proj_lip_space γ hγp (Pj L) (hP1 L) hΦ j hj4 τ y y'
  have hsp0 : ∀ τ y y', ‖iteratedFDeriv ℝ j (r2HeatFn γ Φ τ) y - iteratedFDeriv ℝ j (r2HeatFn γ Φ τ) y'‖ ≤
      K * ‖y - y'‖ := fun τ y y' =>
    le_of_tendsto ((hlim τ y).sub (hlim τ y')).norm (Filter.Eventually.of_forall fun L => hsp L τ y y')
  -- time Lipschitz bounds
  have htm : ∀ L, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ y,
      ‖s102_projHeatD γ Φ (Pj L) j τ y - s102_projHeatD γ Φ (Pj L) j σ y‖ ≤ A * K * |τ - σ| := by
    intro L τ hτ σ hσ y
    refine (hC1 L Φ hΦ τ hτ σ hσ j hj3 y).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA1 hK0) (abs_nonneg _)
  have htm0 : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ σ ∈ Set.Icc (0 : ℝ) T, ∀ y,
      ‖iteratedFDeriv ℝ j (r2HeatFn γ Φ τ) y - iteratedFDeriv ℝ j (r2HeatFn γ Φ σ) y‖ ≤ A * K * |τ - σ| := by
    intro τ hτ σ hσ y
    exact le_of_tendsto ((hlim τ y).sub (hlim σ y)).norm (Filter.Eventually.of_forall fun L => htm L τ hτ σ hσ y)
  -- joint modulus along the curve
  have hmodL : ∀ L, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ‖s102_projHeatD γ Φ (Pj L) j τ (Y τ) - s102_projHeatD γ Φ (Pj L) j σ (Y σ)‖ ≤
        (A * K) * |τ - σ| + K * ‖Y τ - Y σ‖ := by
    intro L τ hτ σ hσ
    calc _ = ‖(s102_projHeatD γ Φ (Pj L) j τ (Y τ) - s102_projHeatD γ Φ (Pj L) j σ (Y τ)) +
            (s102_projHeatD γ Φ (Pj L) j σ (Y τ) - s102_projHeatD γ Φ (Pj L) j σ (Y σ))‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (htm L τ hτ σ hσ _) (hsp L σ _ _))
  have hmod0 : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ‖iteratedFDeriv ℝ j (r2HeatFn γ Φ τ) (Y τ) - iteratedFDeriv ℝ j (r2HeatFn γ Φ σ) (Y σ)‖ ≤
        (A * K) * |τ - σ| + K * ‖Y τ - Y σ‖ := by
    intro τ hτ σ hσ
    calc _ = ‖(iteratedFDeriv ℝ j (r2HeatFn γ Φ τ) (Y τ) - iteratedFDeriv ℝ j (r2HeatFn γ Φ σ) (Y τ)) +
            (iteratedFDeriv ℝ j (r2HeatFn γ Φ σ) (Y τ) - iteratedFDeriv ℝ j (r2HeatFn γ Φ σ) (Y σ))‖ := by
              congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (htm0 τ hτ σ hσ _) (hsp0 σ _ _))
  refine ⟨s102_contOn _ Y hY _ _ hmod0, fun L => s102_contOn _ Y hY _ _ (hmodL L), ?_⟩
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
  obtain ⟨L0, hL0⟩ := HRS.MC.Sec7.S7PIG3.S7PIG3_unif (isCompact_Icc (a := (0 : ℝ)) (b := T))
    (fun L τ => s102_projHeatD γ Φ (Pj L) j τ (Y τ)) (fun τ => iteratedFDeriv ℝ j (r2HeatFn γ Φ τ) (Y τ))
    (fun σ hσ e he => by
      have h1 := ((hmod σ hσ).eventually (ge_mem_nhds he)).and (self_mem_nhdsWithin : Set.Icc 0 T ∈ 𝓝[Set.Icc 0 T] σ)
      filter_upwards [h1] with τ hτ
      exact ⟨fun L => (hmodL L τ hτ.2 σ hσ).trans hτ.1, (hmod0 τ hτ.2 σ hσ).trans hτ.1⟩)
    (fun σ _ => hlim σ (Y σ)) ε hε
  exact ⟨L0, hL0⟩

end HRS.MS.R2Interp

end
