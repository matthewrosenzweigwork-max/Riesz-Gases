import HRS.MD.EQRemInt5

/-!
# EQ-REM (b), part 6: the adjoint propagator, regularity in time, measurability of the coefficient functions
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29 HRS.Quad

variable {d : ℕ} {s : ℝ}

open Classical in
theorem eqrem_isSmooth_realMode (k : NonzeroLattice d) : Torus.IsSmooth (Torus.realMode k) := by
  unfold Torus.IsSmooth Torus.IsCk
  have hdot : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Euc d => Lattice.dot k.1 y) := by
    unfold Lattice.dot
    refine ContDiff.sum fun i _ => contDiff_const.mul ?_
    exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
  have hlift : Torus.lift (Torus.realMode k) = fun y : Euc d =>
      if Lattice.IsPosHalf k.1 then Real.sqrt 2 * Real.cos (2 * Real.pi * Lattice.dot k.1 y)
      else Real.sqrt 2 * Real.sin (2 * Real.pi * Lattice.dot k.1 y) := by
    funext y
    unfold Torus.lift Torus.realMode
    simp only [Function.comp, Torus.cosMode_mk, Torus.sinMode_mk]
  rw [hlift]
  split_ifs
  · exact contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul hdot))
  · exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul hdot))

/-- The adjoint propagator of a fixed terminal datum, as a time-family of `C²` functions, continuous in time inside `(0,t)`. -/
theorem eqrem_prop_data (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t : ℝ) (φ0 : Torus d → ℝ) :
    ∃ f : ℝ → Torus d → ℝ, (∀ r, propagator D ρ r t φ0 = f r) ∧
      (∀ r ∈ Set.Icc 0 t, Torus.IsCk 2 (f r)) ∧
      (∀ x : Torus d, ContinuousOn (fun r => f r x) (Set.Ioo 0 t)) := by
  by_cases h : ∃ f, IsClassicalAdjointSolution D ρ t φ0 f
  · refine ⟨h.choose, fun r => ?_, fun r hr => ?_, fun x => ?_⟩
    · unfold propagator; rw [dif_pos h]
    · have := h.choose_spec.c2 r hr
      exact_mod_cast this
    · intro r hr
      exact (h.choose_spec.time_deriv x r hr).continuousAt.continuousWithinAt
  · refine ⟨fun _ _ => 0, fun r => ?_, fun r _ => ?_, fun x => ?_⟩
    · unfold propagator; rw [dif_neg h]; rfl
    · exact contDiff_const
    · exact continuousOn_const

/-- Measurability in time of the Fourier coefficients of a time-family continuous inside `(0,t)`. -/
theorem eqrem_coeff_meas (t : ℝ) (f : ℝ → Torus d → ℝ) (hc : ∀ r ∈ Set.Icc 0 t, Torus.IsCk 2 (f r))
    (ht : ∀ x : Torus d, ContinuousOn (fun r => f r x) (Set.Ioo 0 t)) (j : NonzeroLattice d) :
    Measurable (fun r : ℝ => if r ∈ Set.Ioo 0 t then Torus.funRealCoeff (f r) j else 0) := by
  classical
  set F : ℝ → Torus d → ℝ := fun r x => if r ∈ Set.Ioo 0 t then f r x else 0 with hF
  have hFx : ∀ x : Torus d, Measurable (fun r => F r x) := by
    intro x
    have : (fun r => F r x) = (Set.Ioo 0 t).piecewise (fun r => f r x) (fun _ => 0) := by
      funext r; rfl
    rw [this]
    exact (ContinuousOn.measurable_piecewise (ht x) continuousOn_const measurableSet_Ioo)
  have hFr : ∀ r : ℝ, Continuous (F r) := by
    intro r
    by_cases hr : r ∈ Set.Ioo 0 t
    · have : F r = f r := funext fun x => if_pos hr
      rw [this]
      exact eqrem_continuous_of_isCk (hc r ⟨hr.1.le, hr.2.le⟩)
    · have : F r = fun _ => 0 := funext fun x => if_neg hr
      rw [this]; exact continuous_const
  have hFm : Measurable (Function.uncurry (fun (x : Torus d) (r : ℝ) => F r x)) :=
    measurable_uncurry_of_continuous_of_measurable (fun r => hFr r) hFx
  have hG : Measurable (fun p : ℝ × Torus d => Torus.realMode j p.2 * F p.1 p.2) := by
    refine ((Torus.continuous_realMode j).measurable.comp measurable_snd).mul ?_
    exact hFm.comp measurable_swap
  have hint := (hG.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Torus d)))).measurable
  have e : (fun r : ℝ => if r ∈ Set.Ioo 0 t then Torus.funRealCoeff (f r) j else 0) =
      fun r => ∫ y, Torus.realMode j y * F r y := by
    funext r
    by_cases hr : r ∈ Set.Ioo 0 t
    · rw [if_pos hr]
      unfold Torus.funRealCoeff
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      show _ = Torus.realMode j y * F r y
      rw [show F r y = f r y from if_pos hr]
    · rw [if_neg hr]
      have : ∀ y, F r y = 0 := fun y => if_neg hr
      simp [this]
  rw [e]
  exact hint

end HRS.MD.EQRem

end
