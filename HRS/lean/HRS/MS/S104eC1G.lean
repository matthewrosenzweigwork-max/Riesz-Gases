import HRS.MS.S104eC1A

/-!
# S104E route C, packet C1 (part G): Gaussian representation of the jets of `P_h f` and joint continuity

`s104c1_Drep`: for `f ∈ Bd N B`, `h ≥ 0`, `i ≤ N`:
`D^i (P_h f)(x) = e^{-ahi} • ∫ D^i f (e^{-ah} x + σ_h z) dγ(z)`.
`c1_ou_joint`: the jets of `(h,x) ↦ P_h f(x)` are jointly continuous on `[0,H] × ℝ^d` for every `f ∈ Bd N B`
(no vanishing at infinity needed; this is the form needed by `VolHyp.P_cont`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ContDiff

namespace HRS.MS.S104e.C
open HRS HRS.Whole HRS.MS.R2WinOrbNL HRS.MS.Ul HRS.MS.Wad
variable {d : ℕ}

theorem s104c1_compCLM_smul (c : ℝ) (i : ℕ) (m : ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ) :
    m.compContinuousLinearMap (fun _ => c • ContinuousLinearMap.id ℝ (Euc d)) = c ^ i • m := by
  ext v
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, m.map_smul_univ]

theorem s104c1_Drep {a ν : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) {N : ℕ} {B : ℝ} {f : Euc d → ℝ} (hf : Bd N B f)
    {h : ℝ} (hh : 0 ≤ h) {i : ℕ} (hi : i ≤ N) (x : Euc d) :
    iteratedFDeriv ℝ i (ouSg (ouQ d a) ν h f) x =
      Real.exp (-a * h) ^ i • ∫ z, iteratedFDeriv ℝ i f (Real.exp (-a * h) • x + s83_ms a ν h • z)
        ∂(stdGaussian (Euc d)) := by
  have hd := (ul3C_smooth (ouQ d a) ν h N hf.1 (M := B) hf.2).2 i hi x
  rw [hd, s104c1_law ha hν hh]
  have hcont : Continuous (iteratedFDeriv ℝ i f) :=
    hf.1.continuous_iteratedFDeriv (by exact_mod_cast hi)
  have hm : Measurable fun z : Euc d => s83_ms a ν h • z := by fun_prop
  have hint : Continuous fun y : Euc d =>
      (iteratedFDeriv ℝ i f (ouExp (ouQ d a) h x + y)).compContinuousLinearMap
        (fun _ => ouExp (ouQ d a) h) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin i => ouExp (ouQ d a) h)).continuous.comp
      (hcont.comp (continuous_const.add continuous_id))
  rw [integral_map hm.aemeasurable hint.aestronglyMeasurable]
  simp only [s104c1_ouExp, s104c1_compCLM_smul]
  rw [integral_smul]
  simp

theorem s104c1_ms_cont (a ν : ℝ) : Continuous (s83_ms a ν) := by
  unfold s83_ms; fun_prop

/-- Joint continuity of the jets of `(h,x) ↦ P_h f(x)` on `[0,H] × ℝ^d`, `h = 0` included; no decay needed. -/
theorem c1_ou_joint (a ν : ℝ) (ha : 0 < a) (hν : 0 < ν) (N : ℕ) (H : ℝ) {B : ℝ} {f : Euc d → ℝ}
    (hf : Bd N B f) (i : ℕ) (hi : i ≤ N) :
    ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ i (ouSg (ouQ d a) ν p.1 f) p.2)
      (Icc 0 H ×ˢ univ) := by
  have hcont : Continuous (iteratedFDeriv ℝ i f) :=
    hf.1.continuous_iteratedFDeriv (by exact_mod_cast hi)
  have hb : ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ B := fun y => hf.2 i hi y
  set Fn : ℝ × Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ := fun p =>
    Real.exp (-a * p.1) ^ i • ∫ z, iteratedFDeriv ℝ i f (Real.exp (-a * p.1) • p.2 + s83_ms a ν p.1 • z)
      ∂(stdGaussian (Euc d)) with hFn
  have hFc : Continuous Fn := by
    have hI : Continuous fun p : ℝ × Euc d => ∫ z, iteratedFDeriv ℝ i f
        (Real.exp (-a * p.1) • p.2 + s83_ms a ν p.1 • z) ∂(stdGaussian (Euc d)) := by
      refine continuous_of_dominated (bound := fun _ => B) (fun p => ?_) (fun p => ?_) ?_ ?_
      · exact (hcont.comp (by fun_prop)).aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun z => hb _
      · exact integrable_const _
      · refine Filter.Eventually.of_forall fun z => ?_
        have := s104c1_ms_cont a ν
        exact hcont.comp (by fun_prop)
    exact ((by fun_prop : Continuous fun p : ℝ × Euc d => Real.exp (-a * p.1) ^ i).smul hI)
  refine hFc.continuousOn.congr fun p hp => ?_
  rw [s104c1_Drep ha hν.le hf hp.1.1 hi p.2]

end HRS.MS.S104e.C
