import HRS.MS.S104eC0
import HRS.MS.WadAux19

/-!
# S104E route C, packet C1 (part A): the OU semigroup `ouSg (ouQ d a) ν h` is the Mehler semigroup `s83_P a ν h`; stability

`s104c1_ouSg`: for continuous `f`, `ν ≥ 0`, `h ≥ 0`, `ouSg (ouQ d a) ν h f = s83_P a ν h f` (`G_{e^{-ah}, σ_h}` of `WadAux1`).
`c1_ou_stab`: `C = 1` works (the operator is a contraction on every `C_b^N`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff MatrixOrder

namespace HRS.MS.S104e.C
open HRS HRS.Whole HRS.MS.R2WinOrbNL HRS.MS.Ul HRS.MS.Lc
variable {d : ℕ}

theorem s104c1_lcQ (a : ℝ) : lcQ (ouQ d a) = a • ContinuousLinearMap.id ℝ (Euc d) := by
  ext y : 1
  simp [lcQ_apply, ouQ, Torus.matVec]

theorem s104c1_ouExp (a v : ℝ) :
    ouExp (ouQ d a) v = Real.exp (-a * v) • ContinuousLinearMap.id ℝ (Euc d) := by
  unfold ouExp
  rw [s104c1_lcQ, smul_smul]
  have : ((-v) * a) • ContinuousLinearMap.id ℝ (Euc d) = algebraMap ℝ (Euc d →L[ℝ] Euc d) ((-v) * a) := by
    ext y : 1; simp [Algebra.algebraMap_eq_smul_one]
  rw [this, ← NormedSpace.algebraMap_exp_comm, Algebra.algebraMap_eq_smul_one]
  rw [← Real.exp_eq_exp_ℝ]
  congr 2
  ring

theorem s104c1_adj (a v : ℝ) :
    ContinuousLinearMap.adjoint (ouExp (ouQ d a) v) = Real.exp (-a * v) • ContinuousLinearMap.id ℝ (Euc d) := by
  rw [s104c1_ouExp]
  ext y : 1
  apply ext_inner_left ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [real_inner_smul_left, real_inner_smul_right]

theorem s104c1_ouCov (a ν τ : ℝ) :
    ouCov (ouQ d a) ν τ = (2 * ν * ∫ v in (0:ℝ)..τ, Real.exp (-a * v) ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  ext i j
  simp only [ouCov, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply]
  have key : ∀ v : ℝ, inner ℝ (ContinuousLinearMap.adjoint (ouExp (ouQ d a) v) (EuclideanSpace.single i (1 : ℝ)))
      (ContinuousLinearMap.adjoint (ouExp (ouQ d a) v) (EuclideanSpace.single j (1 : ℝ))) =
      if i = j then Real.exp (-a * v) ^ 2 else 0 := by
    intro v
    rw [s104c1_adj]
    simp only [smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left,
      real_inner_smul_right, EuclideanSpace.inner_single_left]
    by_cases h : i = j
    · subst h; simp [pow_two]
    · simp [h]
  simp only [key]
  by_cases h : i = j
  · simp [h]
  · simp [h]

theorem s104c1_int_exp (a τ : ℝ) (ha : a ≠ 0) :
    ∫ v in (0:ℝ)..τ, Real.exp (-a * v) ^ 2 = (1 - Real.exp (-2 * a * τ)) / (2 * a) := by
  have hd : ∀ v ∈ Set.uIcc (0:ℝ) τ, HasDerivAt (fun v : ℝ => -(Real.exp (-2 * a * v)) / (2 * a))
      (Real.exp (-a * v) ^ 2) v := by
    intro v _
    have h1 : HasDerivAt (fun v : ℝ => -2 * a * v) (-2 * a) v := by
      simpa using (hasDerivAt_id v).const_mul (-2 * a)
    have h2 := (h1.exp).neg.div_const (2 * a)
    convert h2 using 1
    rw [← Real.exp_nat_mul]
    field_simp
    congr 1
    push_cast; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp only [mul_zero, Real.exp_zero]; field_simp; ring
  · apply Continuous.intervalIntegrable; fun_prop

theorem s104c1_cov2 {a ν τ : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) (hτ : 0 ≤ τ) :
    ouCov (ouQ d a) ν τ = (HRS.MS.Wad.s83_ms a ν τ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  rw [s104c1_ouCov, s104c1_int_exp a τ ha.ne', HRS.MS.Wad.s83_ms_sq ha hν hτ]
  congr 1
  field_simp

theorem s104c1_law {a ν τ : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) (hτ : 0 ≤ τ) :
    ouLaw (ouQ d a) ν τ =
      (stdGaussian (Euc d)).map (fun z => HRS.MS.Wad.s83_ms a ν τ • z) := by
  rw [ouLaw_eq_map, s104c1_cov2 ha hν hτ]
  set m := HRS.MS.Wad.s83_ms a ν τ with hm
  have hm0 : 0 ≤ m := HRS.MS.Wad.s83_ms_nonneg _ _ _
  have hs : CFC.sqrt ((m ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) = m • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    apply CFC.sqrt_unique
    · rw [smul_mul_smul_comm, mul_one, pow_two]
    · exact Matrix.nonneg_iff_posSemidef.2 (Matrix.PosSemidef.one.smul hm0)
  rw [hs]
  congr 1
  funext x
  simp

theorem s104c1_ouSg {a ν τ : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) (hτ : 0 ≤ τ) {f : Euc d → ℝ}
    (hf : Continuous f) : ouSg (ouQ d a) ν τ f = HRS.MS.Wad.s83_P a ν τ f := by
  funext x
  unfold ouSg HRS.MS.Wad.s83_P HRS.MS.Wad.s83_G
  have hm : Measurable fun z : Euc d => HRS.MS.Wad.s83_ms a ν τ • z := by fun_prop
  have hc : Continuous fun y : Euc d => f (ouExp (ouQ d a) τ x + y) :=
    hf.comp (continuous_const.add continuous_id)
  rw [s104c1_law ha hν hτ, integral_map hm.aemeasurable hc.aestronglyMeasurable, s104c1_ouExp]
  simp [HRS.MS.Wad.s83_mc]

theorem s104c1_Enorm {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) : ‖ouExp (ouQ d a) h‖ ≤ 1 := by
  rw [s104c1_ouExp]
  refine (norm_smul _ _).trans_le ?_
  have h1 : ‖Real.exp (-a * h)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]; nlinarith
  calc ‖Real.exp (-a * h)‖ * ‖ContinuousLinearMap.id ℝ (Euc d)‖ ≤ 1 * 1 :=
        mul_le_mul h1 ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem s104c1_Dnorm {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) (i : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) ℝ) :
    ‖T.compContinuousLinearMap (fun _ => ouExp (ouQ d a) h)‖ ≤ ‖T‖ := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have := s104c1_Enorm (d := d) ha hh
  calc ‖T‖ * ∏ _i : Fin i, ‖ouExp (ouQ d a) h‖ ≤ ‖T‖ * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [Finset.prod_const]; exact pow_le_one₀ (norm_nonneg _) this
    _ = ‖T‖ := mul_one _

/-- Contraction in `C_b^N` (constant `1`). -/
theorem s104c1_stab (a ν : ℝ) (ha : 0 < a) (hν : 0 < ν) (N : ℕ) {h : ℝ} (hh : 0 ≤ h) {B : ℝ}
    {f : Euc d → ℝ} (hf : Bd N B f) : Bd N B (ouSg (ouQ d a) ν h f) := by
  obtain ⟨hs, hd⟩ := ul3C_smooth (ouQ d a) ν h N hf.1 (M := B) (fun i hi y => hf.2 i hi y)
  refine ⟨hs, fun i hi x => ?_⟩
  rw [hd i hi x]
  have := norm_integral_le_of_norm_le_const (μ := ouLaw (ouQ d a) ν h)
    (f := fun y => (iteratedFDeriv ℝ i f (ouExp (ouQ d a) h x + y)).compContinuousLinearMap
      (fun _ => ouExp (ouQ d a) h)) (C := B)
    (Filter.Eventually.of_forall fun y => (s104c1_Dnorm ha hh i _).trans (hf.2 i hi _))
  simpa using this

/-- `c1_ou_stab`: contraction in `C_b^N` (`C = 1`). -/
theorem c1_ou_stab (a ν : ℝ) (ha : 0 < a) (hν : 0 < ν) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ h : ℝ, 0 ≤ h → ∀ (B : ℝ) (f : Euc d → ℝ), Bd N B f →
      Bd N (C * B) (ouSg (ouQ d a) ν h f) :=
  ⟨1, le_rfl, fun h hh B f hf => by simpa using s104c1_stab a ν ha hν N hh hf⟩

end HRS.MS.S104e.C
