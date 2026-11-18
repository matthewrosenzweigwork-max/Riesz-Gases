import HRS.MS.Fp81S21GaussG4U73

/-! Product-integrability inputs for centering the U7 scalar Duhamel identity. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL HRS.MS.S53

private theorem fp81s21_g4_initial_mode_uniform_bound
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    (α : MultiIndex p.d) {T : ℝ} (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q ∈ Icc (0 : ℝ) T, ∀ x : Euc p.d,
      |r26t3_U R 0 q (generatorW (r26t3_coeff R) q
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x| ≤ B := by
  let horb := s104b_orbit_of_termRegGen hterm R.admissible R.resulting α T hT
  let G : ℝ → Euc p.d → ℝ := fun τ =>
    r26t3_U R 0 τ (generatorW (r26t3_coeff R) τ
      (oscTestFun (wholeSpaceIndex p.d : ℝ) α))
  have hG : ∀ τ ∈ Icc (0 : ℝ) T, MemCb 2 (G τ) := by
    intro τ hτ
    simpa [G, r26t3_U, r26t3_coeff] using
      horb.cb1 (r := 0) (by simp [hT]) (by simpa using hτ)
  obtain ⟨G2, hG2, hd12⟩ := horb.diff12 0 ⟨le_rfl, hT⟩
  have hG2' : ∀ τ ∈ Icc (0 : ℝ) T, MemCb 2 (G2 τ) := by
    simpa only [sub_zero] using hG2
  have hd12' : S53Diff T G G2 := by
    simpa [G, r26t3_U, r26t3_coeff] using hd12
  have hGc : S53Cont T G := s53_cont_of_diff hG hG2' hd12'
  have hlocal : ∀ i : Icc (0 : ℝ) T,
      ∃ η : ℝ, 0 < η ∧ ∃ M : ℝ, 0 ≤ M ∧
        ∀ q ∈ Icc (0 : ℝ) T, |q - i.1| < η → ∀ x, |G q x| ≤ M + 1 := by
    intro i
    obtain ⟨M, hM0, hM⟩ := s53_bound3 (hG i.1 i.2)
    obtain ⟨η, hη, hclose⟩ := hGc i.1 i.2 1 (by norm_num)
    refine ⟨η, hη, M, hM0, ?_⟩
    intro q hq hdist x
    have hdiff := hclose q hq hdist 0 (by norm_num) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hdiff
    have hbase : |G i.1 x| ≤ M := by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
        hM 0 (by norm_num) x
    calc
      |G q x| = |(G q x - G i.1 x) + G i.1 x| := by congr 1; ring
      _ ≤ |G q x - G i.1 x| + |G i.1 x| := abs_add_le _ _
      _ ≤ M + 1 := by nlinarith
      _ = M + 1 := rfl
  choose η hη M hM0 hM using hlocal
  let U : Icc (0 : ℝ) T → Set ℝ := fun i => {q | |q - i.1| < η i}
  have hUopen : ∀ i, IsOpen (U i) := by
    intro i
    have hc : Continuous (fun q : ℝ => |q - i.1|) :=
      continuous_abs.comp (continuous_id.sub continuous_const)
    exact isOpen_lt hc continuous_const
  have hcover : Icc (0 : ℝ) T ⊆ ⋃ i, U i := by
    intro q hq
    refine Set.mem_iUnion.2 ⟨⟨q, hq⟩, ?_⟩
    simp [U, hη]
  obtain ⟨F, hF⟩ := isCompact_Icc.elim_finite_subcover U hUopen hcover
  let B : ℝ := ∑ i ∈ F, (M i + 1)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun i hi => add_nonneg (hM0 i) (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro q hq x
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hF hq)
  obtain ⟨hiF, hqi⟩ := Set.mem_iUnion.mp hi
  have hloc := hM i q hq (by simpa [U] using hqi) x
  calc
    |G q x| ≤ M i + 1 := hloc
    _ ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum (f := fun j => M j + 1)
        (fun j hj => add_nonneg (hM0 j) (by norm_num)) hiF

/-- The scalar propagated generator has a uniform spatial bound on each compact
terminal-time interval, and hence is integrable on the time-space product. -/
theorem fp81s21_g4_initial_scalar_prod_integrable
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    {f : Euc p.d → ℝ}
    (hf : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ q ∈ Icc (0 : ℝ) T, ∀ x,
        |r26t3_U R 0 q (generatorW (r26t3_coeff R) q f) x| ≤ B) ∧
      Integrable
        (fun z : ℝ × Euc p.d =>
          r26t3_U R 0 (s53_clamp T z.1)
            (generatorW (r26t3_coeff R) (s53_clamp T z.1) f) z.2)
        ((volume.restrict (Icc (0 : ℝ) T)).prod
          (HRS.Whole.withDensityReal R.ρβ)) := by
  classical
  have hjoint := fp81s21_g4_initial_scalar_joint_meas p R hterm hf hT
  rcases hf with ⟨S, coeff, rfl⟩
  have hmode : ∀ α : MultiIndex p.d, ∃ B : ℝ, 0 ≤ B ∧
      ∀ q ∈ Icc (0 : ℝ) T, ∀ x,
        |r26t3_U R 0 q (generatorW (r26t3_coeff R) q
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x| ≤ B := by
    intro α
    exact fp81s21_g4_initial_mode_uniform_bound p R hterm α hT
  let M : MultiIndex p.d → ℝ := fun α => Classical.choose (hmode α)
  have hM0 : ∀ α, 0 ≤ M α := fun α => (Classical.choose_spec (hmode α)).1
  have hMb : ∀ α q, q ∈ Icc (0 : ℝ) T → ∀ x,
      |r26t3_U R 0 q (generatorW (r26t3_coeff R) q
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x| ≤ M α := by
    intro α
    exact (Classical.choose_spec (hmode α)).2
  let B : ℝ := ∑ α ∈ S, |coeff α| * M α
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun α hα => mul_nonneg (abs_nonneg _) (hM0 α)
  have hcombo : ∀ q ∈ Icc (0 : ℝ) T, ∀ x,
      |r26t3_U R 0 q (generatorW (r26t3_coeff R) q
        (fun y => ∑ α ∈ S, coeff α * oscTestFun (wholeSpaceIndex p.d : ℝ) α y)) x| ≤ B := by
    intro q hq x
    have hgen := fp81s21_g4_generator_combo p R hterm (r := 0) (q := q)
      le_rfl hq.1 S coeff
    rw [congrFun hgen.2.2 x]
    calc
      |∑ α ∈ S, coeff α * r26t3_U R 0 q
          (generatorW (r26t3_coeff R) q
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x| ≤
        ∑ α ∈ S, |coeff α * r26t3_U R 0 q
          (generatorW (r26t3_coeff R) q
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ α ∈ S, |coeff α| * |r26t3_U R 0 q
          (generatorW (r26t3_coeff R) q
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x| := by simp_rw [abs_mul]
      _ ≤ ∑ α ∈ S, |coeff α| * M α := by
        apply Finset.sum_le_sum
        intro α hα
        exact mul_le_mul_of_nonneg_left (hMb α q hq x) (abs_nonneg _)
      _ = B := rfl
  let μstar : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  have hμstar : IsProbabilityMeasure μstar :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  letI : IsProbabilityMeasure μstar := hμstar
  let clampSubtype : ℝ → Icc (0 : ℝ) T := fun t =>
    ⟨s53_clamp T t, s53_clamp_mem hT t⟩
  have hclamp : Measurable clampSubtype :=
    ((s53_clamp_lip T).continuous.subtype_mk fun t => s53_clamp_mem hT t).measurable
  have hmap : Measurable (fun z : ℝ × Euc p.d => (clampSubtype z.1, z.2)) :=
    (hclamp.comp measurable_fst).prodMk measurable_snd
  have hmeas : Measurable (fun z : ℝ × Euc p.d =>
      r26t3_U R 0 (s53_clamp T z.1)
        (generatorW (r26t3_coeff R) (s53_clamp T z.1)
          (fun y => ∑ α ∈ S, coeff α * oscTestFun (wholeSpaceIndex p.d : ℝ) α y)) z.2) := by
    have heq : (fun z : ℝ × Euc p.d =>
        r26t3_U R 0 (s53_clamp T z.1)
          (generatorW (r26t3_coeff R) (s53_clamp T z.1)
            (fun y => ∑ α ∈ S, coeff α * oscTestFun (wholeSpaceIndex p.d : ℝ) α y)) z.2) =
        Function.uncurry (fun q : Icc (0 : ℝ) T => fun x =>
          r26t3_U R 0 q.1 (generatorW (r26t3_coeff R) q.1
            (fun y => ∑ α ∈ S, coeff α * oscTestFun (wholeSpaceIndex p.d : ℝ) α y)) x) ∘
            (fun z : ℝ × Euc p.d => (clampSubtype z.1, z.2)) := by
      funext z
      simp [clampSubtype]
    rw [heq]
    exact hjoint.comp hmap
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) T)) :=
    Real.isFiniteMeasure_restrict_Icc 0 T
  haveI : IsFiniteMeasure ((volume.restrict (Icc (0 : ℝ) T)).prod μstar) := inferInstance
  have hbounded : ∀ z : ℝ × Euc p.d,
      ‖r26t3_U R 0 (s53_clamp T z.1)
        (generatorW (r26t3_coeff R) (s53_clamp T z.1)
          (fun y => ∑ α ∈ S, coeff α * oscTestFun (wholeSpaceIndex p.d : ℝ) α y)) z.2‖ ≤ B := by
    intro z
    rw [Real.norm_eq_abs]
    exact hcombo (s53_clamp T z.1) (s53_clamp_mem hT z.1) z.2
  refine ⟨B, hB, hcombo, ?_⟩
  exact Integrable.of_bound hmeas.aestronglyMeasurable B
    (Filter.Eventually.of_forall hbounded)

#print axioms fp81s21_g4_initial_scalar_prod_integrable
end HRS.Fp81.S21
end
