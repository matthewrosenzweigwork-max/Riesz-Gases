import HRS.Main.T25PAux28

/-!
# T25P, part 29: uniqueness in law of linear fluctuation solutions (windows)

Two `IsLinearFluctuationSolution`s with the same initial law have the same finite-dimensional laws (the Gaussian part is
independent of the initial datum and has a prescribed law), hence the same window law.
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q54c HRS.Uniform.Q07c HRS.Uniform.Q45 HRS.AdjK

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem t25p_lin_fdd (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    {T' : ℝ} (hT' : 0 < T')
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr.dyn ρ m Vev)
    {K : ℝ} (hK : 0 ≤ K)
    (hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T' → ‖Vev t r‖ ≤ K)
    {Ω Ω' : Type} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y₀ : Ω → NegSobolev d m) (hY₀ : Measurable Y₀) (Y : ℝ → Ω → NegSobolev d m)
    (hY : IsLinearFluctuationSolution P htr.dyn ρ m β⁻¹ T' Y₀ Y)
    (Y₀' : Ω' → NegSobolev d m) (hY₀' : Measurable Y₀') (Y' : ℝ → Ω' → NegSobolev d m)
    (hY' : IsLinearFluctuationSolution P' htr.dyn ρ m β⁻¹ T' Y₀' Y')
    (hlaw : P.map Y₀ = P'.map Y₀') :
    ∀ (p : ℕ) (ts : Fin p → ℝ) (ks : Fin p → NonzeroLattice d), (∀ a, ts a ∈ Set.Icc 0 T') →
      P.map (fun ω a => NegSobolev.coord (Y (ts a) ω) (ks a)) =
        P'.map (fun ω a => NegSobolev.coord (Y' (ts a) ω) (ks a)) := by
  intro p ts ks hts
  set φ : Fin p → Torus d → ℝ := fun a => Torus.realMode (ks a) with hφdef
  have hφ : ∀ a, Torus.IsSmooth (φ a) := fun a => HRS.Uniform.Q48b.q48b_isSmooth_realMode (ks a)
  have hmemφ : ∀ a, MemSobolev m (φ a) := fun a =>
    HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ a) m
  have hmemU : ∀ a, MemSobolev m (propagator htr.dyn ρ 0 (ts a) (φ a)) := fun a =>
    t25p_memSobolev_propagator hd htr hdual hK le_rfl (hts a).1 (hKb 0 (ts a) le_rfl (hts a).1 (hts a).2) (hφ a)
  set W : NegSobolev d m → EuclideanSpace ℝ (Fin p) :=
    fun z => WithLp.toLp 2 fun a => NegSobolev.eval z (propagator htr.dyn ρ 0 (ts a) (φ a))
    with hWdef
  have hW : Measurable W := measurable_toLp_eval fun a => (continuous_eval_const (hmemU a)).measurable
  obtain ⟨hindY, hlawY⟩ := hY.gaussian_part p ts φ hts hφ
  obtain ⟨hindY', hlawY'⟩ := hY'.gaussian_part p ts φ hts hφ
  set Gy : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
    NegSobolev.eval (Y (ts a) ω) (φ a) -
      NegSobolev.eval (Y₀ ω) (propagator htr.dyn ρ 0 (ts a) (φ a)) with hGy
  set Gy' : Ω' → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
    NegSobolev.eval (Y' (ts a) ω) (φ a) -
      NegSobolev.eval (Y₀' ω) (propagator htr.dyn ρ 0 (ts a) (φ a)) with hGy'
  have hGym : Measurable Gy := by
    refine measurable_toLp_eval fun a => ?_
    exact ((continuous_eval_const (hmemφ a)).measurable.comp (hY.meas _)).sub
      ((continuous_eval_const (hmemU a)).measurable.comp hY₀)
  have hGym' : Measurable Gy' := by
    refine measurable_toLp_eval fun a => ?_
    exact ((continuous_eval_const (hmemφ a)).measurable.comp (hY'.meas _)).sub
      ((continuous_eval_const (hmemU a)).measurable.comp hY₀')
  have hlawG : P.map Gy = P'.map Gy' := hlawY.trans hlawY'.symm
  set Vv : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
    NegSobolev.eval (Y (ts a) ω) (φ a) with hVv
  set Vv' : Ω' → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
    NegSobolev.eval (Y' (ts a) ω) (φ a) with hVv'
  have hVV : P.map Vv = P'.map Vv' := by
    refine map_eq_of_decomp P P' Gy Y₀ Gy' Y₀' W hW hGym hY₀ hGym' hY₀' hindY hindY' hlawG hlaw
      Vv Vv' (fun ω => ?_) (fun ω => ?_)
    · ext a
      simp [hVv, hGy, hWdef]
    · ext a
      simp [hVv', hGy', hWdef]
  set Sc : EuclideanSpace ℝ (Fin p) → (Fin p → ℝ) :=
    fun v a => Lattice.jp (ks a).1 ^ (-m) * v a with hSc
  have hScm : Measurable Sc := by
    refine measurable_pi_iff.2 fun a => ?_
    exact (measurable_pi_apply a |>.comp (PiLp.continuous_ofLp 2 (fun _ : Fin p => ℝ)).measurable).const_mul _
  have e1 : (fun ω a => NegSobolev.coord (Y (ts a) ω) (ks a)) = Sc ∘ Vv := by
    funext ω a
    simp only [Function.comp, hSc, hVv]
    rw [coord_eq_eval]
  have e2 : (fun ω a => NegSobolev.coord (Y' (ts a) ω) (ks a)) = Sc ∘ Vv' := by
    funext ω a
    simp only [Function.comp, hSc, hVv']
    rw [coord_eq_eval]
  have hVm : Measurable Vv := measurable_toLp_eval fun a =>
    (continuous_eval_const (hmemφ a)).measurable.comp (hY.meas _)
  have hVm' : Measurable Vv' := measurable_toLp_eval fun a =>
    (continuous_eval_const (hmemφ a)).measurable.comp (hY'.meas _)
  rw [e1, e2, ← Measure.map_map hScm hVm, ← Measure.map_map hScm hVm', hVV]

theorem t25p_lin_unique (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    {T a : ℝ} (hT : 0 < T) (ha : 0 ≤ a)
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr.dyn ρ m Vev)
    {K : ℝ} (hK : 0 ≤ K)
    (hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖Vev t r‖ ≤ K)
    {Ω Ω' : Type} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y₀ : Ω → NegSobolev d m) (hY₀ : Measurable Y₀) (Y : ℝ → Ω → NegSobolev d m)
    (hY : IsLinearFluctuationSolution P htr.dyn ρ m β⁻¹ (a + T) Y₀ Y)
    (Y₀' : Ω' → NegSobolev d m) (hY₀' : Measurable Y₀') (Y' : ℝ → Ω' → NegSobolev d m)
    (hY' : IsLinearFluctuationSolution P' htr.dyn ρ m β⁻¹ (a + T) Y₀' Y')
    (hlaw : P.map Y₀ = P'.map Y₀') :
    law P (HRS.Main.windowPath m T a Y) = law P' (HRS.Main.windowPath m T a Y') := by
  have hT' : 0 < a + T := by linarith
  have hfdd := t25p_lin_fdd hd htr hT' hdual hK hKb P P' Y₀ hY₀ Y hY Y₀' hY₀' Y' hY' hlaw
  exact Q54c.toPath_law_eq (m := m) (T := T) hT.le P P' (fun t ω => Y (a + t) ω)
    (fun t ω => Y' (a + t) ω) (fun t => hY.meas _) (fun t => hY'.meas _)
    (by filter_upwards [hY.cont] with ω hω using HRS.Uniform.Comp28.contOn_shift (T := T) ha (Y := Y) hω)
    (by filter_upwards [hY'.cont] with ω hω using HRS.Uniform.Comp28.contOn_shift (T := T) ha (Y := Y') hω)
    (fun p ts ks hts' => hfdd p (fun i => a + ts i) ks
      (fun i => ⟨by linarith [(hts' i).1], by linarith [(hts' i).2]⟩))

end HRS.T25P
