import HRS.MS.Fp81S21JointD
import HRS.MS.Fp81S21CoeffMoments8
import HRS.MS.Fp81S21PredMap

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The diagonal observable of a finite-rank kernel, written as its actual
finite sum of products of compact oscillator tests. -/
def fp81s21_rankKernelDiagonal {d : ℕ} (D : fp81s21_RankKernel d) : Euc d → ℝ :=
  fun x => ∑ i, ∑ j, D.u i x * (D.c i j * D.u j x)

theorem fp81s21_rankKernelDiagonal_eq_kernel {d : ℕ}
    (D : fp81s21_RankKernel d) (x : Euc d) :
    fp81s21_rankKernelDiagonal D x = D.kernel x x := by
  simp only [fp81s21_rankKernelDiagonal, fp81s21_RankKernel.kernel,
    HRS.Whole.r2FiniteRankKernel]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem fp81s21_hasCompactSupport_finset_sum {d : ℕ} {α : Type*}
    [DecidableEq α] (s : Finset α) (f : α → Euc d → ℝ)
    (hf : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change HasCompactSupport (0 : Euc d → ℝ)
    exact HasCompactSupport.zero
  | @insert a s ha ih =>
    have htail : ∀ i ∈ s, HasCompactSupport (f i) := by
      intro i hi
      exact hf i (Finset.mem_insert_of_mem hi)
    have hsum : (fun x => ∑ i ∈ insert a s, f i x) =
        f a + (fun x => ∑ i ∈ s, f i x) := by
      funext x
      simp [Finset.sum_insert, ha]
    rw [hsum]
    exact (hf a (Finset.mem_insert_self a s)).add (ih htail)

theorem fp81s21_rankKernelDiagonal_isR2Test {d : ℕ}
    (D : fp81s21_RankKernel d) :
    IsR2Test (fp81s21_rankKernelDiagonal D) := by
  classical
  constructor
  · exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      (D.valid.smooth i).mul (contDiff_const.mul (D.valid.smooth j))
  · unfold fp81s21_rankKernelDiagonal
    exact fp81s21_hasCompactSupport_finset_sum Finset.univ
      (fun i x => ∑ j, D.u i x * (D.c i j * D.u j x))
      (fun i hi => fp81s21_hasCompactSupport_finset_sum Finset.univ
        (fun j x => D.u i x * (D.c i j * D.u j x))
        (fun j hj => (D.valid.compactSupport i).mul_right))

/-- The finite-rank diagonal correction has the uniform per-time M2 bound.
The weighted norm is evaluated on the actual diagonal test; its rank-dependent
value is fixed before particle count, realization, and time. -/
theorem fp81s21_particle_rankDiagonal_per_time (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ M2 : ℝ, 0 ≤ M2 ∧
          ∀ D : fp81s21_RankKernel p.d,
          ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
          ∀ u : ℝ, 0 ≤ u →
            Integrable (fun ω => ‖(1 / 2 : ℝ) • fp81s21_center A.P
              (fun ω' => Whole.pair
                (Whole.empirical (A.X u.toNNReal ω'))
                (fp81s21_rankKernelDiagonal D)) ω‖ ^ 2) A.P ∧
            (∫ ω, ‖(1 / 2 : ℝ) • fp81s21_center A.P
              (fun ω' => Whole.pair
                (Whole.empirical (A.X u.toNNReal ω'))
                (fp81s21_rankKernelDiagonal D)) ω‖ ^ 2 ∂A.P) ≤
              M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
                (fp81s21_rankKernelDiagonal D)).toReal ^ 2 /
                (4 * (N : ℝ)) := by
  obtain ⟨δ0, hδ0, hδhalf, hUniform⟩ :=
    fp81s21_particleCoeffMoments_embedded p Es
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨M2, M6, hM2, hM6, hFor⟩ := hUniform δ hδ hδle R
  refine ⟨M2, hM2, ?_⟩
  intro D N hN A u hu
  let g : Euc p.d → ℝ := fp81s21_rankKernelDiagonal D
  let f : A.Ω → ℝ := fun ω => Whole.pair
    (Whole.empirical (A.X u.toNNReal ω)) g
  let c : ℝ := Whole.pair (r26t3_mu R u) g
  have hQmember : fp81s21_particleEmpField R N A ∈
      ({fp81s21_particleEmpField R N A, fp81s21_particleQuadRawField R N A,
        fp81s21_particleQuadField R N A} :
        Set (ℝ → A.Ω → (Euc p.d → ℝ) → ℝ)) := by
    simp
  obtain ⟨qη, hRep, _, _, _, _⟩ := hFor E N hN A
    (fp81s21_particleEmpField R N A) hQmember
  have hMom := hRep.2 u hu
  rcases hMom with ⟨hqMem, hqSq, hRepAE⟩
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 4) := by
    nlinarith [p.hd]
  have hgTest : IsR2Test g := by
    simpa [g] using fp81s21_rankKernelDiagonal_isR2Test D
  have hgWeighted : IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4) g :=
    weightedTestSubmodule_iff.1
      (weighted_test_of_compact_smooth hP hgTest)
  let Cg : ℝ := (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4) g).toReal
  have hCg : 0 ≤ Cg := by
    dsimp [Cg]
    exact ENNReal.toReal_nonneg
  have hQae : (fun ω => fp81s21_particleEmpField R N A u ω g) =ᵐ[A.P]
      (fun ω => fp81s21_chartAction Es (qη u ω) g) := by
    filter_upwards [hRepAE] with ω hω
    exact (hω.1 g hgTest).symm
  have hQbound : ∀ᵐ ω ∂A.P,
      |fp81s21_particleEmpField R N A u ω g| ≤ ‖qη u ω‖ * Cg := by
    filter_upwards [hQae] with ω hω
    rw [hω]
    exact fp81s21_chartAction_weighted_bound Es (qη u ω) g hgWeighted
  have hqSqInt : Integrable (fun ω => ‖qη u ω‖ ^ 2) A.P :=
    hqMem.integrable_norm_pow (by norm_num)
  have hqSqBound : (∫ ω, ‖qη u ω‖ ^ 2 ∂A.P) ≤ M2 := hqSq
  let Q : A.Ω → ℝ := fun ω => fp81s21_particleEmpField R N A u ω g
  have hQaeStrong : AEStronglyMeasurable Q A.P := by
    have hqMeas : Measurable (qη u) := by
      exact hRep.1.comp (measurable_const.prodMk measurable_id)
    have hlin : Continuous (fun z : r26t6_Coeff => fp81s21_chartAction Es z g) := by
      change Continuous (fun z => inner ℝ z (Es.encode g))
      exact continuous_id.inner continuous_const
    have hright : AEStronglyMeasurable
        (fun ω => fp81s21_chartAction Es (qη u ω) g) A.P :=
      (hlin.measurable.comp hqMeas).aestronglyMeasurable
    exact hright.congr hQae.symm
  have hQSqBound : ∀ᵐ ω ∂A.P,
      ‖Q ω‖ ^ 2 ≤ Cg ^ 2 * ‖qη u ω‖ ^ 2 := by
    filter_upwards [hQbound] with ω hω
    rw [Real.norm_eq_abs]
    have hω' : |Q ω| ≤ Cg * ‖qη u ω‖ := by
      simpa [Q, mul_comm] using hω
    have hnonneg : 0 ≤ Cg * ‖qη u ω‖ := mul_nonneg hCg (norm_nonneg _)
    nlinarith [abs_nonneg (Q ω), sq_nonneg (|Q ω|),
      sq_nonneg (Cg * ‖qη u ω‖)]
  have hQSqInt : Integrable (fun ω => ‖Q ω‖ ^ 2) A.P := by
    apply Integrable.mono' (hqSqInt.const_mul (Cg ^ 2))
      ((hQaeStrong.aemeasurable.norm.pow_const 2).aestronglyMeasurable)
    filter_upwards [hQSqBound] with ω hω
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖Q ω‖),
      abs_of_nonneg (mul_nonneg (sq_nonneg Cg) (sq_nonneg ‖qη u ω‖))] using hω
  have hQIntBound : (∫ ω, ‖Q ω‖ ^ 2 ∂A.P) ≤ Cg ^ 2 * M2 := by
    calc
      (∫ ω, ‖Q ω‖ ^ 2 ∂A.P) ≤
          ∫ ω, Cg ^ 2 * ‖qη u ω‖ ^ 2 ∂A.P :=
        integral_mono_ae hQSqInt (hqSqInt.const_mul (Cg ^ 2)) hQSqBound
      _ = Cg ^ 2 * ∫ ω, ‖qη u ω‖ ^ 2 ∂A.P := integral_const_mul _ _
      _ ≤ Cg ^ 2 * M2 := mul_le_mul_of_nonneg_left hqSqBound (sq_nonneg Cg)
  have hQMem : MemLp Q 2 A.P :=
    (memLp_two_iff_integrable_sq_norm hQaeStrong).2 hQSqInt
  have hQInt : Integrable Q A.P := hQMem.integrable one_le_two
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hsqrtPos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hsqrtSq : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hQdef : Q = fun ω => Real.sqrt (N : ℝ) * (f ω - c) := by
    funext ω
    simp [Q, f, c, fp81s21_particleEmpField, HRS.Whole.r2EmpDistr]
  have hFrep : f = fun ω => Q ω / Real.sqrt (N : ℝ) + c := by
    funext ω
    rw [hQdef]
    field_simp [ne_of_gt hsqrtPos]
    ring
  have hfInt : Integrable f A.P := by
    rw [hFrep]
    exact (hQInt.div_const (Real.sqrt (N : ℝ))).add (integrable_const c)
  have hMeanQ : (∫ ω, Q ω ∂A.P) =
      Real.sqrt (N : ℝ) * ((∫ ω, f ω ∂A.P) - c) := by
    rw [hQdef, integral_const_mul, integral_sub hfInt (integrable_const c)]
    simp [IsProbabilityMeasure.measure_univ]
  have hCenterEq (ω : A.Ω) : fp81s21_center A.P f ω =
      (Q ω - ∫ ω', Q ω' ∂A.P) / Real.sqrt (N : ℝ) := by
    rw [fp81s21_center, hMeanQ, hQdef]
    field_simp [ne_of_gt hsqrtPos]
    ring
  have hQCenterMem : MemLp (fun ω => Q ω - ∫ ω', Q ω' ∂A.P) 2 A.P :=
    hQMem.sub (memLp_const _)
  have hQCenterSqInt : Integrable
      (fun ω => ‖Q ω - ∫ ω', Q ω' ∂A.P‖ ^ 2) A.P :=
    hQCenterMem.integrable_norm_pow (by norm_num)
  have hVarEq : ProbabilityTheory.variance Q A.P =
      ∫ ω, (Q ω - ∫ ω', Q ω' ∂A.P) ^ 2 ∂A.P := by
    rw [ProbabilityTheory.variance_eq_integral hQMem.aemeasurable]
  have hVar : ProbabilityTheory.variance Q A.P ≤
      ∫ ω, ‖Q ω‖ ^ 2 ∂A.P := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (ProbabilityTheory.variance_le_expectation_sq hQMem.aestronglyMeasurable)
  have hCenterSqBound :
      (∫ ω, ‖fp81s21_center A.P f ω‖ ^ 2 ∂A.P) ≤
        (Cg ^ 2 * M2) / (N : ℝ) := by
    have hscale : (∫ ω, ‖fp81s21_center A.P f ω‖ ^ 2 ∂A.P) =
        (1 / (N : ℝ)) *
          ∫ ω, ‖Q ω - ∫ ω', Q ω' ∂A.P‖ ^ 2 ∂A.P := by
      calc
        _ = ∫ ω, ‖(Q ω - ∫ ω', Q ω' ∂A.P) / Real.sqrt (N : ℝ)‖ ^ 2 ∂A.P := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [hCenterEq ω]
        _ = _ := by
          rw [show (fun ω => ‖(Q ω - ∫ ω', Q ω' ∂A.P) /
              Real.sqrt (N : ℝ)‖ ^ 2) =
              fun ω => (1 / (N : ℝ)) *
                ‖Q ω - ∫ ω', Q ω' ∂A.P‖ ^ 2 by
              funext ω
              rw [Real.norm_eq_abs, abs_div, abs_of_pos hsqrtPos]
              rw [div_pow, hsqrtSq]
              simp only [Real.norm_eq_abs]
              ring]
          rw [integral_const_mul]
    rw [hscale]
    have hVarReal : ProbabilityTheory.variance Q A.P =
        ∫ ω, ‖Q ω - ∫ ω', Q ω' ∂A.P‖ ^ 2 ∂A.P := by
      rw [hVarEq]
      simp [Real.norm_eq_abs, sq_abs]
    calc
      (1 / (N : ℝ)) *
          ∫ ω, ‖Q ω - ∫ ω', Q ω' ∂A.P‖ ^ 2 ∂A.P
        = (1 / (N : ℝ)) * ProbabilityTheory.variance Q A.P := by rw [hVarReal]
      _ ≤ (1 / (N : ℝ)) * ∫ ω, ‖Q ω‖ ^ 2 ∂A.P :=
        mul_le_mul_of_nonneg_left hVar (by positivity)
      _ ≤ (1 / (N : ℝ)) * (Cg ^ 2 * M2) :=
        mul_le_mul_of_nonneg_left hQIntBound (by positivity)
      _ = (Cg ^ 2 * M2) / (N : ℝ) := by ring
  have hErrInt : Integrable
      (fun ω => ‖(1 / 2 : ℝ) • fp81s21_center A.P f ω‖ ^ 2) A.P := by
    have hCenterEq' : (fun ω => fp81s21_center A.P f ω) =
        fun ω => (1 / Real.sqrt (N : ℝ)) *
          (Q ω - ∫ ω', Q ω' ∂A.P) := by
      funext ω
      rw [hCenterEq ω]
      field_simp [ne_of_gt hsqrtPos]
    have hCenterMem : MemLp (fun ω => fp81s21_center A.P f ω) 2 A.P := by
      rw [hCenterEq']
      exact hQCenterMem.const_mul (1 / Real.sqrt (N : ℝ))
    exact hCenterMem.const_mul (1 / 2)
      |>.integrable_norm_pow (by norm_num)
  have hErrBound : (∫ ω, ‖(1 / 2 : ℝ) • fp81s21_center A.P f ω‖ ^ 2 ∂A.P) ≤
      M2 * Cg ^ 2 / (4 * (N : ℝ)) := by
    calc
      (∫ ω, ‖(1 / 2 : ℝ) • fp81s21_center A.P f ω‖ ^ 2 ∂A.P) =
          (1 / 4 : ℝ) *
            ∫ ω, ‖fp81s21_center A.P f ω‖ ^ 2 ∂A.P := by
        rw [show (fun ω => ‖(1 / 2 : ℝ) • fp81s21_center A.P f ω‖ ^ 2) =
          fun ω => (1 / 4 : ℝ) * ‖fp81s21_center A.P f ω‖ ^ 2 by
            funext ω
            rw [norm_smul, Real.norm_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
            ring]
        rw [integral_const_mul]
      _ ≤ (1 / 4 : ℝ) * ((Cg ^ 2 * M2) / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hCenterSqBound (by norm_num)
      _ = M2 * Cg ^ 2 / (4 * (N : ℝ)) := by ring
  refine ⟨?_, ?_⟩
  · simpa [f, g] using hErrInt
  · simpa [f, g, Cg] using hErrBound

#print axioms HRS.Fp81.S21.fp81s21_rankKernelDiagonal_eq_kernel
#print axioms HRS.Fp81.S21.fp81s21_rankKernelDiagonal_isR2Test
#print axioms HRS.Fp81.S21.fp81s21_particle_rankDiagonal_per_time

end HRS.Fp81.S21
end
