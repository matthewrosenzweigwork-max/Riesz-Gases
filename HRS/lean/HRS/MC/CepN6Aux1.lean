import HRS.Stochastic.Brownian
import HRS.Stochastic.Filtration

/-!
# Packet CEPN6 (aux 1): the normalised difference of two coordinates of a Brownian filtration is a
one-dimensional Brownian filtration
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepN6

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem n6_hasLaw_diff [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ mΩ}
    {W : ℝ≥0 → Ω → ι → ℝ} (hW : IsBrownianFiltration P ℱ W) {i j : ι} (hij : i ≠ j)
    {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => ((W t ω i - W s ω i) - (W t ω j - W s ω j)) / Real.sqrt 2)
      (gaussianReal 0 (t - s)) P := by
  have hDi := hW.hasLaw_incr_coord hst i
  have hDj := hW.hasLaw_incr_coord hst j
  have hind : IndepFun (fun ω => W t ω i - W s ω i) (fun ω => W t ω j - W s ω j) P :=
    (hW.iIndepFun_incr_coords hst).indepFun hij
  have hneg := gaussianReal_neg hDj
  have hind' : IndepFun (fun ω => W t ω i - W s ω i) (-(fun ω => W t ω j - W s ω j)) P :=
    hind.comp measurable_id measurable_neg
  have hsum : HasLaw ((fun ω => W t ω i - W s ω i) + -(fun ω => W t ω j - W s ω j))
      (gaussianReal (0 + -0) ((t - s) + (t - s))) P :=
    ⟨hDi.aemeasurable.add hneg.aemeasurable,
      gaussianReal_add_gaussianReal_of_indepFun hind' hDi hneg⟩
  have hdiv := gaussianReal_div_const hsum (Real.sqrt 2)
  convert hdiv using 2
  · simp
  · apply NNReal.eq
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [NNReal.coe_div]
    show ((t - s : ℝ≥0) : ℝ) = (((t - s : ℝ≥0) : ℝ) + ((t - s : ℝ≥0) : ℝ)) / Real.sqrt 2 ^ 2
    rw [h2]
    ring

theorem n6_isBrownianFiltration_diff [IsProbabilityMeasure P] {ι : Type*} [Fintype ι]
    {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ} (hW : IsBrownianFiltration P ℱ W) {i j : ι}
    (hij : i ≠ j) :
    IsBrownianFiltration P ℱ (fun t ω (_ : Fin 1) => (W t ω i - W t ω j) / Real.sqrt 2) where
  complete := hW.complete
  adapted t := by
    letI : MeasurableSpace Ω := ℱ t
    have h := hW.adapted t
    exact measurable_pi_iff.2 fun _ =>
      (((measurable_pi_apply i).comp h).sub ((measurable_pi_apply j).comp h)).div_const _
  zero ω := by funext _; simp [hW.zero ω]
  cont ω := continuous_pi fun _ =>
    (((continuous_apply i).comp (hW.cont ω)).sub ((continuous_apply j).comp (hW.cont ω))).div_const _
  indep_incr s t hst := by
    refine indep_of_indep_of_le_left (hW.indep_incr s t hst) ?_
    let F : (ι → ℝ) → (Fin 1 → ℝ) := fun v _ => (v i - v j) / Real.sqrt 2
    have hF : Measurable F := measurable_pi_iff.2 fun _ =>
      (((measurable_pi_apply i).sub (measurable_pi_apply j))).div_const _
    have hφ : (fun ω => (fun (_ : Fin 1) => (W t ω i - W t ω j) / Real.sqrt 2) -
        (fun (_ : Fin 1) => (W s ω i - W s ω j) / Real.sqrt 2)) =
        fun ω => F (W t ω - W s ω) := by
      funext ω; funext _
      simp only [Pi.sub_apply, F]
      ring
    rw [hφ]
    rintro _ ⟨S, hS, rfl⟩
    exact ⟨F ⁻¹' S, hF hS, rfl⟩
  gaussian_incr s t hst := by
    have hZ := n6_hasLaw_diff hW hij hst
    have hmp := (measurePreserving_funUnique (gaussianReal 0 (t - s)) (Fin 1)).symm
      (MeasurableEquiv.funUnique (Fin 1) ℝ)
    have := hmp.hasLaw.comp hZ
    have hfun : (⇑(MeasurableEquiv.funUnique (Fin 1) ℝ).symm ∘
        fun ω => (W t ω i - W s ω i - (W t ω j - W s ω j)) / Real.sqrt 2) =
        fun ω => (fun (_ : Fin 1) => (W t ω i - W t ω j) / Real.sqrt 2) -
          (fun (_ : Fin 1) => (W s ω i - W s ω j) / Real.sqrt 2) := by
      funext ω; funext _
      simp only [Function.comp_apply, Pi.sub_apply]
      show (W t ω i - W s ω i - (W t ω j - W s ω j)) / Real.sqrt 2 = _
      ring
    rw [hfun] at this
    exact this

end HRS.MC.CepN6
