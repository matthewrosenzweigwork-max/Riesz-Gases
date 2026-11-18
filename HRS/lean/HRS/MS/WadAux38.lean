import HRS.MS.WadAux37

/-!
# S8.3, packet D7 (Route A), part 3: the projected solution

For a frozen classical solution `w` of `-∂_r w = ℒ w` (datum `φ`, horizon `t`), the function
`f_r = w_r - μ(w_r) + μ(φ)` is an `IsAdjointSolutionG (projGeneratorW C μ) t φ f`
(`s85_proj_solution`): `ℒ` kills constants and `d/dr μ(w_r) = -μ(ℒ w_r)` (differentiation under the integral,
`|ℒ w_r(y)| ≤ B(1+|y|)`, `μ` has a first moment).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- Common analytic facts about a frozen classical solution, packaged. -/
theorem s85_cl_facts (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {t : ℝ} {φ : Euc d → ℝ} {w : ℝ → Euc d → ℝ}
    (hw : IsClassicalAdjointW (critCoeff d a β ρβ) t φ w) :
    ∃ B0 BG : ℝ, 0 ≤ B0 ∧ 0 ≤ BG ∧ (∀ r ∈ Set.Icc 0 t, ∀ x, |w r x| ≤ B0) ∧
      (∀ r ∈ Set.Icc 0 t, ∀ x, |generatorW (critCoeff d a β ρβ) r (w r) x| ≤ BG * (1 + ‖x‖)) ∧
      ContinuousOn (fun q : ℝ × Euc d => w q.1 q.2) (Set.Icc 0 t ×ˢ Set.univ) ∧
      ContinuousOn (fun q : ℝ × Euc d => generatorW (critCoeff d a β ρβ) q.1 (w q.1) q.2)
        (Set.Icc 0 t ×ˢ Set.univ) := by
  obtain ⟨B0, hB0⟩ := hw.bdd 0 (by norm_num)
  obtain ⟨BG, hBG⟩ := hw.bdd_time_deriv
  refine ⟨|B0|, |BG|, abs_nonneg _, abs_nonneg _, fun r hr x => ?_, fun r hr x => ?_, ?_, ?_⟩
  · have := hB0 r hr x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  · refine (hBG r hr x).trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  · exact s84_contOn_of_subtype (s84_cont_D0 (F := fun p : Set.Icc (0 : ℝ) t × Euc d => w p.1)
      (x := fun p => p.2) (hw.cont_c2 0 (by norm_num)))
  · exact s84_contOn_of_subtype hw.cont_time_deriv

theorem s85_first_moment {ρβ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρβ) (hg : s84_GaussReg ρβ) :
    Integrable (fun y : Euc d => 1 + ‖y‖) (HRS.Whole.withDensityReal ρβ) := by
  simpa using s85_moment_integrable hρ hg (p := 1) zero_le_one

/-- **The projected solution.** -/
theorem s85_proj_solution (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {t : ℝ} {φ : Euc d → ℝ} {w : ℝ → Euc d → ℝ}
    (hw : IsClassicalAdjointW (critCoeff d a β ρβ) t φ w) :
    IsAdjointSolutionG (projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ)) t φ
      (fun r y => w r y + (HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) φ - ∫ z, w r z ∂(HRS.Whole.withDensityReal ρβ))) := by
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hP
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  obtain ⟨B0, BG, hB0, hBG0, hb0, hbG, hwc, hGc⟩ := s85_cl_facts hd ha hβ hρ hw
  set μ := HRS.Whole.withDensityReal ρβ with hμ
  set G : ℝ → Euc d → ℝ := fun r y => generatorW (critCoeff d a β ρβ) r (w r) y with hGdef
  have hI1 : Integrable (fun y : Euc d => BG * (1 + ‖y‖)) μ := (s85_first_moment hP hg).const_mul BG
  have hIc : Integrable (fun _ : Euc d => B0) μ := integrable_const B0
  -- continuity of the mean
  have hmc : ContinuousOn (fun r => ∫ z, w r z ∂μ) (Set.Icc 0 t) :=
    s85_cont_param hIc hwc hb0
  have hm'c : ContinuousOn (fun r => ∫ z, G r z ∂μ) (Set.Icc 0 t) :=
    s85_cont_param hI1 hGc hbG
  -- derivative of the mean
  have hmd : ∀ r ∈ Set.Ioo (0 : ℝ) t, HasDerivAt (fun r' => ∫ z, w r' z ∂μ) (-∫ z, G r z ∂μ) r := by
    intro r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) t := ⟨hr.1.le, hr.2.le⟩
    have hcw : ∀ r' ∈ Set.Ioo (0 : ℝ) t, Continuous (w r') := fun r' hr'' =>
      (hw.c2 r' ⟨hr''.1.le, hr''.2.le⟩).continuous
    have hGy : Continuous (fun y => -G r y) :=
      (hGc.comp_continuous (Continuous.prodMk continuous_const continuous_id)
        (fun y => ⟨hr', Set.mem_univ _⟩)).neg
    have := s85_deriv_param (μ := μ) (t := t) (r := r) hr (F := w) (F' := fun r' y => -G r' y)
      (bd := fun y => BG * (1 + ‖y‖)) (bF := fun _ => B0) hI1 hIc hcw hGy
      (fun y => hb0 r hr' y)
      (fun r' hr'' y => by
        rw [abs_neg]; exact hbG r' ⟨hr''.1.le, hr''.2.le⟩ y)
      (fun y r' hr'' => hw.time_deriv y r' hr'')
    simpa [integral_neg] using this
  have hκd : ∀ r ∈ Set.Ioo (0 : ℝ) t,
      HasDerivAt (fun r' => HRS.Whole.pair μ φ - ∫ z, w r' z ∂μ) (∫ z, G r z ∂μ) r := by
    intro r hr
    have := (hmd r hr).const_sub (HRS.Whole.pair μ φ)
    simpa using this
  have hκc : ContinuousOn (fun r => HRS.Whole.pair μ φ - ∫ z, w r z ∂μ) (Set.Icc 0 t) :=
    continuousOn_const.sub hmc
  have key := s85_transfer (G := generatorW (critCoeff d a β ρβ)) (G' := projGeneratorW (critCoeff d a β ρβ) μ)
    (s85_cl_to_G hw) (κ := fun r => HRS.Whole.pair μ φ - ∫ z, w r z ∂μ) (κ' := fun r => ∫ z, G r z ∂μ)
    hκc hm'c hκd (by
      intro r hr x
      show projGeneratorW (critCoeff d a β ρβ) μ r
          (fun y => w r y + (HRS.Whole.pair μ φ - ∫ z, w r z ∂μ)) x = _
      have e : generatorW (critCoeff d a β ρβ) r
          (fun y => w r y + (HRS.Whole.pair μ φ - ∫ z, w r z ∂μ)) = generatorW (critCoeff d a β ρβ) r (w r) := by
        funext y; exact s85_gen_add_const a β ρβ r (w r) _ y
      unfold projGeneratorW
      rw [e])
  have hκt : HRS.Whole.pair μ φ - ∫ z, w t z ∂μ = 0 := by
    rw [hw.terminal]; unfold HRS.Whole.pair; ring
  have hfun : (fun y => φ y + (HRS.Whole.pair μ φ - ∫ z, w t z ∂μ)) = φ := by
    funext y; rw [hκt, add_zero]
  rw [hfun] at key
  exact key

end HRS.MS.Wad
