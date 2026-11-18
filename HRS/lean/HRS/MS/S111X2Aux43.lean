import HRS.MS.S111X2Aux42
import HRS.MS.S111X2Aux38

/-!
# S11.1 X2, packet H02 (part 5): the expectation of the projected window as a sum of covariance entries
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111X2

open HRS HRS.Whole HRS.MS.R2Interp
open HRS.Whole.Q34

variable {d : ℕ}

theorem s111x2_memU (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) (α : MultiIndex d) {τ : ℝ} (hτ : 0 ≤ τ) :
    MemLp (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 τ
      (oscTestFun (wholeSpaceIndex d : ℝ) α)) 2 (HRS.Whole.withDensityReal ρ) := by
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := isProbabilityMeasure_nu T.prob
  obtain ⟨⟨f, hf⟩, -⟩ := s111x2_exist_osc hd hs0 hs ha hβ hρ α (H := τ + 1) (by linarith)
  have hτI : τ ∈ Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  rw [s111x2_prop_orbit hd hs0 hs ha hβ hρ hf hτI]
  obtain ⟨B0, B1, B2, hB0, -, -, hB⟩ := HRS.MS.S111X1.classical_bounds hf
  have hI : τ + 1 - τ ∈ Icc (0 : ℝ) (τ + 1) := ⟨by linarith, by linarith⟩
  exact (MemLp.of_bound (hf.c2 _ hI).continuous.aestronglyMeasurable B0
    (Filter.Eventually.of_forall fun x => (hB _ hI x).1)).mono_exponent le_top

abbrev s111x2_CC (d : ℕ) (s a β : ℝ) (ρ : Euc d → ℝ) : WholeCoeff d :=
  (quadraticGradientDyn d s a β).coeff (fun _ => ρ)

abbrev s111x2_C0 (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (θ : ℝ) : (Euc d → ℝ) → (Euc d → ℝ) → ℝ :=
  HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) θ

/-- **Expectation of the projected window.** -/
theorem s111x2_window_exp (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {θ : ℝ} (hθ : 0 ≤ θ) {T : ℝ} (hT : 0 < T) (L : ℕ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → Ω → OscDual d (wholeSpaceIndex d : ℝ)) {u : ℝ} (hu : 0 ≤ u)
    (hZ : IsLinearGaussianEvolutionW P (s111x2_CC d s a β ρ) (wholeSpaceIndex d : ℝ)
      β⁻¹ (u + T) (s111x2_C0 d s ρ θ) Z)
    (M : OscPath d (wholeSpaceIndex d : ℝ) T [×2]→L[ℝ] ℝ) :
    ∫ ζ, M ![s102_Pj T hT L (processWindow (wholeSpaceIndex d : ℝ) T u Z ζ),
        s102_Pj T hT L (processWindow (wholeSpaceIndex d : ℝ) T u Z ζ)] ∂P =
      ∑ p ∈ s102_idx d L, ∑ q ∈ s102_idx d L,
        linearGaussianCov (s111x2_CC d s a β ρ) β⁻¹ (s111x2_C0 d s ρ θ)
          (u + ((s102_node hT L p.1 : Set.Icc (0 : ℝ) T) : ℝ)) (u + ((s102_node hT L q.1 : Set.Icc (0 : ℝ) T) : ℝ))
          (oscTestFun (wholeSpaceIndex d : ℝ) p.2) (oscTestFun (wholeSpaceIndex d : ℝ) q.2) *
        M ![s102_bpath (m := (wholeSpaceIndex d : ℝ)) T L p, s102_bpath (m := (wholeSpaceIndex d : ℝ)) T L q] := by
  classical
  obtain ⟨M₁, T₁⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := isProbabilityMeasure_nu T₁.prob
  obtain ⟨hWm, hae⟩ := HRS.MS.S111BD.s111_shifted_window_aemeas d P _ _ β⁻¹ T u (u + T) _ Z hZ hT.le hu le_rfl
  obtain ⟨-, -, hL2⟩ := HRS.MS.S111BD.s111_shifted_window_gaussian d P _ _ β⁻¹ T u (u + T) _ Z hZ hT hu le_rfl
  refine s111x2_exp_expand hT L P (processWindow (wholeSpaceIndex d : ℝ) T u Z) hL2 M _ ?_
  intro p hp q hq
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin 2 → Set.Icc (0 : ℝ) T, τ = ![s102_node hT L p.1, s102_node hT L q.1] := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : Fin 2 → MultiIndex d, α = ![p.2, q.2] := ⟨_, rfl⟩
  have hG := hZ.gaussian 2 (fun i => u + (τ i : ℝ)) (fun i => oscTestFun (wholeSpaceIndex d : ℝ) (α i))
    (fun i => ⟨by linarith [(τ i).2.1], by linarith [(τ i).2.2]⟩)
    (fun i => HRS.MS.GenPath.s56_isOscTest (wholeSpaceIndex d : ℝ) (α i))
  have hcongr : (s102_obs (m := (wholeSpaceIndex d : ℝ)) τ α) ∘ (processWindow (wholeSpaceIndex d : ℝ) T u Z) =ᵐ[P]
      fun ζ => (WithLp.toLp 2 fun i => OscDual.eval (Z (u + (τ i : ℝ)) ζ)
        (oscTestFun (wholeSpaceIndex d : ℝ) (α i)) : EuclideanSpace ℝ (Fin 2)) := by
    filter_upwards [hae] with ζ hζ
    ext i
    simp only [Function.comp, s102_obs_apply, hζ (τ i), OscDual.eval_oscTestFun]
  have hmap : P.map ((s102_obs (m := (wholeSpaceIndex d : ℝ)) τ α) ∘ (processWindow (wholeSpaceIndex d : ℝ) T u Z)) =
      P.map (fun ζ => (WithLp.toLp 2 fun i => OscDual.eval (Z (u + (τ i : ℝ)) ζ)
        (oscTestFun (wholeSpaceIndex d : ℝ) (α i)) : EuclideanSpace ℝ (Fin 2))) := Measure.map_congr hcongr
  unfold HRS.law at hG
  rw [hG] at hmap
  have hexp : ∀ i : Fin 2, ∃ f, IsClassicalAdjointW (s111x2_CC d s a β ρ) (u + (τ i : ℝ))
      (oscTestFun (wholeSpaceIndex d : ℝ) (α i)) f := fun i =>
    (s111x2_exist_osc hd hs0 hs ha hβ hρ (α i) (H := u + (τ i : ℝ)) (by linarith [(τ i).2.1])).1
  choose f hf using hexp
  have hpsd := s111x2_cov_psd2 hd hs0 hs ha hβ hρ hθ (fun i => u + (τ i : ℝ))
    (fun i => by linarith [(τ i).2.1]) (fun i => oscTestFun (wholeSpaceIndex d : ℝ) (α i)) f hf
    (fun i => s111x2_memU hd hs0 hs ha hβ hρ (α i) (by linarith [(τ i).2.1]))
  have hmix := s111x2_gauss_mixed _ hpsd 0 1
  have hobsm : AEMeasurable ((s102_obs (m := (wholeSpaceIndex d : ℝ)) τ α) ∘
      (processWindow (wholeSpaceIndex d : ℝ) T u Z)) P :=
    (s102_obs (m := (wholeSpaceIndex d : ℝ)) τ α).continuous.measurable.comp_aemeasurable hWm
  have hint : ∫ ζ, s102_ellp hT L p (processWindow (wholeSpaceIndex d : ℝ) T u Z ζ) *
      s102_ellp hT L q (processWindow (wholeSpaceIndex d : ℝ) T u Z ζ) ∂P =
      ∫ x, x 0 * x 1 ∂(P.map ((s102_obs (m := (wholeSpaceIndex d : ℝ)) τ α) ∘
        (processWindow (wholeSpaceIndex d : ℝ) T u Z))) := by
    rw [integral_map hobsm (by fun_prop)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    subst hτ hα
    rfl
  rw [hint, hmap, hmix]
  subst hτ hα
  rfl

end HRS.MS.S111X2
