import HRS.MS.MfeConfAux141

/-!
# S.B.1 (SB5), packet R3a (part 2): the conditioned law of a regularised solution

For an event `{Y₀ ∈ S}` of the initial value (`Y₀` is `ℱ_0`-measurable), `cond Pm {Y₀ ∈ S}` makes `(Y₀, Brownian path)` a product
again, hence `Pc.map (Ys t) = ((Pc.map Y₀) ⊗ Wiener).map Ψ_t`.  No filtration is conditioned.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Whole HRS.MD.EQLawPath HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MfeConf

theorem sb1_cond_map_eq {Ω γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ] (Pm : Measure Ω) {g : Ω → γ}
    (hg : Measurable g) {S : Set γ} (hS : MeasurableSet S) :
    (cond Pm (g ⁻¹' S)).map g = (Pm (g ⁻¹' S))⁻¹ • (Pm.map g).restrict S := by
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul, Measure.restrict_map hg hS]
  exact hg.aemeasurable

section Meas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] {ι : Type*} [Fintype ι]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {Pm : Measure Ω} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → ι → ℝ}

theorem sb1_cond_flow_law [IsProbabilityMeasure Pm] (hW : IsBrownianFiltration Pm ℱ W') {bt : ℝ → E → E}
    (hb : IsLipschitzDrift bt) {σ : ι → E} {Y₀ : Ω → E} (hY0 : Measurable[ℱ 0] Y₀) {Ys : ℝ → Ω → E}
    (hY : IsAdditiveSDESolution Pm ℱ W' bt σ Y₀ (fun _ => ⊤) Ys) {S : Set E} (hS : MeasurableSet S)
    {t : ℝ} (ht : 0 ≤ t) :
    (cond Pm (Y₀ ⁻¹' S)).map (Ys t) =
      (((cond Pm (Y₀ ⁻¹' S)).map Y₀).prod (Pm.map (bfPath hW))).map (sb1Ψ bt σ t) := by
  have hYm : Measurable Y₀ := hY0.mono (ℱ.le _) le_rfl
  have hbf := measurable_bfPath hW
  have hf : Measurable (fun ω => (Y₀ ω, bfPath hW ω)) := hYm.prodMk hbf
  have hΨ := sb1Ψ_meas bt hb σ t
  have hae : Ys t =ᵐ[Pm] fun ω => sb1Ψ bt σ t (Y₀ ω, bfPath hW ω) := by
    filter_upwards [sb1_sol_eq_picLim hW hb hY] with ω h
    exact h t ht
  have hae' : Ys t =ᵐ[cond Pm (Y₀ ⁻¹' S)] fun ω => sb1Ψ bt σ t (Y₀ ω, bfPath hW ω) :=
    cond_absolutelyContinuous.ae_le hae
  rw [Measure.map_congr hae']
  rw [show (fun ω => sb1Ψ bt σ t (Y₀ ω, bfPath hW ω)) = sb1Ψ bt σ t ∘ (fun ω => (Y₀ ω, bfPath hW ω)) from rfl,
    ← Measure.map_map hΨ hf]
  congr 1
  have hpre : (fun ω => (Y₀ ω, bfPath hW ω)) ⁻¹' (S ×ˢ Set.univ) = Y₀ ⁻¹' S := by
    ext ω; simp
  have h1 := sb1_cond_map_eq Pm hf (hS.prod MeasurableSet.univ)
  rw [hpre] at h1
  rw [h1, sb1_cond_map_eq Pm hYm hS, sb1_joint_law hW hY0, Measure.prod_smul_left]
  congr 1
  rw [← Measure.prod_restrict, Measure.restrict_univ]

end Meas

end HRS.MS.MfeConf
