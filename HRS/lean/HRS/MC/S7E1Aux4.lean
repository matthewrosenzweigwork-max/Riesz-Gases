import HRS.MC.S7E1Aux3

/-!
# Packet `s7_E1_variance_sandwich`, file 4: passing a two-sided second-moment bound to an `L^2` limit
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.Sec7.E1Aux4

open HRS HRS.Sec7

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem e1d_inner_toLp {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ⟪hf.toLp f, hg.toLp g⟫ = ∫ x, f x * g x ∂P := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem e1d_limit (S : ℕ → Ω → ℝ) (hS : ∀ L, MemLp (S L) 2 P) (hS0 : ∀ L, ∫ ω, S L ω ∂P = 0)
    (Q : Ω → ℝ) (hQ : AEMeasurable Q P)
    (hlim : Tendsto (fun L : ℕ => ∫⁻ ω, ‖Q ω - S L ω‖ₑ ^ 2 ∂P) atTop (𝓝 0))
    {m M : ℝ} (m' M' : ℕ → ℝ) (hm' : Tendsto m' atTop (𝓝 m)) (hM' : Tendsto M' atTop (𝓝 M))
    (hb : ∀ L, m' L ≤ ∫ ω, S L ω ^ 2 ∂P ∧ ∫ ω, S L ω ^ 2 ∂P ≤ M' L) :
    MemLp Q 2 P ∧ ∫ ω, Q ω ∂P = 0 ∧ m ≤ ∫ ω, Q ω ^ 2 ∂P ∧ ∫ ω, Q ω ^ 2 ∂P ≤ M := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  -- Q is in L^2
  have hdiff : ∀ L, AEStronglyMeasurable (fun ω => Q ω - S L ω) P := fun L =>
    (hQ.aestronglyMeasurable).sub (hS L).aestronglyMeasurable
  obtain ⟨L0, hL0⟩ : ∃ L0, ∫⁻ ω, ‖Q ω - S L0 ω‖ₑ ^ 2 ∂P < ∞ := by
    have := (hlim.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < ∞ by simp))).exists
    exact this
  have hQmem : MemLp Q 2 P := by
    have h1 : eLpNorm (fun ω => Q ω - S L0 ω) 2 P < ∞ := by
      rw [E0b.e0b_lint_eq _ (hdiff L0)] at hL0
      by_contra hcon
      push_neg at hcon
      rw [top_le_iff] at hcon
      rw [hcon] at hL0
      simp at hL0
    have h2 : MemLp (fun ω => Q ω - S L0 ω) 2 P := h1
    have := h2.add (hS L0)
    refine this.ae_eq (Filter.Eventually.of_forall fun ω => ?_)
    simp
  set F : Lp ℝ 2 P := hQmem.toLp Q with hF
  set f : ℕ → Lp ℝ 2 P := fun L => (hS L).toLp (S L) with hf
  -- convergence in Lp
  have h5 : ∀ L, ∫⁻ ω, ‖Q ω - S L ω‖ₑ ^ 2 ∂P = ENNReal.ofReal ‖F - f L‖ ^ 2 := by
    intro L
    have hae : (⇑(F - f L) : Ω → ℝ) =ᵐ[P] fun ω => Q ω - S L ω := by
      filter_upwards [Lp.coeFn_sub F (f L), (hS L).coeFn_toLp, hQmem.coeFn_toLp] with ω h1 h2 h3
      rw [h1]; simp only [Pi.sub_apply, hf, hF] at *; rw [h2, h3]
    refine (E0b.e0b_lint_eq (fun ω => Q ω - S L ω) (hdiff L)).trans ?_
    rw [← eLpNorm_congr_ae hae, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  have hnorm : Tendsto (fun L => ‖F - f L‖) atTop (𝓝 0) := by
    have h6 : Tendsto (fun L => ENNReal.ofReal ‖F - f L‖ ^ 2) atTop (𝓝 0) := by
      simpa only [h5] using hlim
    have h7 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h6
    have h8 : ∀ L, (ENNReal.ofReal ‖F - f L‖ ^ 2).toReal = ‖F - f L‖ ^ 2 := fun L => by
      rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (norm_nonneg _)]
    have h9 : Tendsto (fun L => ‖F - f L‖ ^ 2) atTop (𝓝 0) := by
      simpa [Function.comp_def, h8] using h7
    have h10 := (Real.continuous_sqrt.tendsto 0).comp h9
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using h10
  have hfF : Tendsto f atTop (𝓝 F) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [norm_sub_rev] using hnorm
  -- second moment
  have hnsq : ∀ (g : Ω → ℝ) (hg : MemLp g 2 P), ‖hg.toLp g‖ ^ 2 = ∫ ω, g ω ^ 2 ∂P := fun g hg => by
    rw [Lp.norm_toLp]; exact E0b.e0b_sq_eq hg
  have hsq : Tendsto (fun L => ∫ ω, S L ω ^ 2 ∂P) atTop (𝓝 (∫ ω, Q ω ^ 2 ∂P)) := by
    have := ((continuous_norm.tendsto F).comp hfF).pow 2
    rw [hF, hnsq Q hQmem] at this
    refine this.congr fun L => ?_
    simp only [Function.comp_apply, hf]
    exact hnsq _ _
  refine ⟨hQmem, ?_, le_of_tendsto_of_tendsto' hm' hsq fun L => (hb L).1,
    le_of_tendsto_of_tendsto' hsq hM' fun L => (hb L).2⟩
  -- mean
  have h1 : MemLp (fun _ : Ω => (1 : ℝ)) 2 P := memLp_const 1
  have hin : Tendsto (fun L => ⟪h1.toLp _, f L⟫) atTop (𝓝 ⟪h1.toLp _, F⟫) :=
    tendsto_const_nhds.inner hfF
  have hz : ∀ L, ⟪h1.toLp _, f L⟫ = 0 := fun L => by
    simp only [hf]; rw [e1d_inner_toLp h1 (hS L)]; simpa using hS0 L
  simp only [hz] at hin
  have := tendsto_nhds_unique hin tendsto_const_nhds
  rw [hF, e1d_inner_toLp h1 hQmem] at this
  simpa using this

end HRS.MC.Sec7.E1Aux4

end
