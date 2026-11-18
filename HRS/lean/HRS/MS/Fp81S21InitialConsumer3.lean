import HRS.MS.Fp81S21InitialConsumer2
import HRS.MS.Fp81S21InitialTransport3
import HRS.MS.Fp81S21InitialTransport

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace HRS.Fp81.S21
open HRS.Whole HRS.MS.R26T3

/-- The static residual is linear in its test observable. -/
theorem fp81s21_staticResidual_const_mul
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (N : ℕ) (a : ℝ)
    (G : Measure SeqL2) (F : SeqL2 → ℝ) (c : ℝ)
    (hF : ContDiff ℝ 5 F) :
    fp81s21_staticResidual R N a G (fun z => c * F z) =
      c * fp81s21_staticResidual R N a G F := by
  have hD3 : ∀ z,
      iteratedFDeriv ℝ 3 (fun z => c * F z) z =
        c • iteratedFDeriv ℝ 3 F z := by
    intro z
    have hreg : ContDiffAt ℝ 3 F z :=
      (hF.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 5)).contDiffAt
    have h := iteratedFDeriv_const_smul_apply'
      (𝕜 := ℝ) (a := c) (f := F) (i := 3) (x := z) hreg
    simpa [smul_eq_mul] using h
  unfold fp81s21_staticResidual
  simp_rw [hD3, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  simp only [integral_const_mul]
  ring

/-- Uniform convergence and a finite bound at each sample size give the
nonnegative uniform error profile required by consumers. -/
theorem fp81s21_initial_profile_of_uniform_remainder
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    (future : Future p) (hf : ValidFuture R future)
    (hfinite : ∀ N : ℕ, 2 ≤ N → ∃ B : ℝ, 0 ≤ B ∧
      ∀ a : ℝ, ∀ ha : 0 ≤ a, ∀ Φ : Window p → ℝ,
        Φ ∈ CbUnitBall (Window p) 5 → ∀ G0 : GaussianRealization R,
          |initialRemainder R future N G0 a ha Φ| ≤ B)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N → 2 ≤ N → ∀ a : ℝ, ∀ (ha : 0 ≤ a),
        ∀ Φ : Window p → ℝ, Φ ∈ CbUnitBall (Window p) 5 →
          ∀ G0 : GaussianRealization R,
            |initialRemainder R future N G0 a ha Φ| ≤ ε) :
    ∃ α : ℕ → ℝ, (∀ N, 0 ≤ α N) ∧ Tendsto α atTop (𝓝 0) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, ∀ (ha : 0 ≤ a),
        ∀ Φ : Window p → ℝ, Φ ∈ CbUnitBall (Window p) 5 →
          ∀ G0 : GaussianRealization R,
            |initialRemainder R future N G0 a ha Φ| ≤ α N := by
  classical
  let S : ℕ → Set ℝ := fun N =>
    if hN : 2 ≤ N then
      {0} ∪ {r : ℝ | ∃ a : ℝ, ∃ ha : 0 ≤ a, ∃ Φ : Window p → ℝ,
        ∃ hΦ : Φ ∈ CbUnitBall (Window p) 5, ∃ G0 : GaussianRealization R,
          r = |initialRemainder R future N G0 a ha Φ|}
    else {0}
  let α : ℕ → ℝ := fun N => if hN : 2 ≤ N then sSup (S N) else 0
  have hS_nonempty : ∀ N, (S N).Nonempty := by
    intro N
    by_cases hN : 2 ≤ N <;> simp [S, hN]
  have hS_bdd : ∀ N, BddAbove (S N) := by
    intro N
    by_cases hN : 2 ≤ N
    · obtain ⟨B, hB, hrem⟩ := hfinite N hN
      refine ⟨B, ?_⟩
      intro r hr
      simp only [S, hN, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_setOf_eq] at hr
      rcases hr with rfl | ⟨a, ha, Φ, hΦ, G0, rfl⟩
      · exact hB
      · exact hrem a ha Φ hΦ G0
    · refine ⟨0, ?_⟩
      simp [S, hN]
  have hα_nonneg : ∀ N, 0 ≤ α N := by
    intro N
    by_cases hN : 2 ≤ N
    · rw [show α N = sSup (S N) by simp [α, hN]]
      exact le_csSup (hS_bdd N) (by simp [S, hN])
    · simp [α, hN]
  have hα_lim : Tendsto α atTop (𝓝 0) := by
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    obtain ⟨N0, hN0⟩ := hconv (ε / 2) (by linarith)
    refine ⟨max N0 2, fun N hN => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hα_nonneg N)]
    have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
    have hN0' : N0 ≤ N := (le_max_left _ _).trans hN
    have hs : sSup (S N) ≤ ε / 2 := by
      refine csSup_le (hS_nonempty N) ?_
      intro r hr
      simp only [S, hN2, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_setOf_eq] at hr
      rcases hr with rfl | ⟨a, ha, Φ, hΦ, G0, rfl⟩
      · linarith
      · exact hN0 N hN0' hN2 a ha Φ hΦ G0
    have hαeq : α N = sSup (S N) := by simp [α, hN2]
    rw [hαeq]
    linarith
  refine ⟨α, hα_nonneg, hα_lim, ?_⟩
  intro N hN a ha Φ hΦ G0
  have hmem : |initialRemainder R future N G0 a ha Φ| ∈ S N := by
    simp only [S, hN, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_setOf_eq]
    exact Or.inr ⟨a, ha, Φ, hΦ, G0, rfl⟩
  have hle := le_csSup (hS_bdd N) hmem
  simpa [α, hN] using hle

/-- The heat pullback transfers uniform static convergence to the actual
initial remainder, retaining the window test's full Cb unit-ball class. -/
theorem fp81s21_initial_remainder_uniform_from_static
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    (future : Future p) (hf : ValidFuture R future)
    (hγ : 0 < p.γ ∨ p.γ = 0)
    (hstatic : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N → 2 ≤ N → ∀ a : ℝ, 0 ≤ a →
        ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
          IsCenteredGaussianSeq G (fun i j =>
            HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
              (r26t3_mu R 0) p.γ (r26t3_qwin R a i) (r26t3_qwin R a j)) →
          ∀ F : SeqL2 → ℝ, F ∈ CbUnitBall SeqL2 5 →
            |fp81s21_staticResidual R N a G F| ≤ ε)
    (hgauss : ∀ a : ℝ, 0 ≤ a → ∃ G : Measure SeqL2,
      IsProbabilityMeasure G ∧ IsCenteredGaussianSeq G (fun i j =>
        HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
          (r26t3_mu R 0) p.γ (r26t3_qwin R a i) (r26t3_qwin R a j)))
    (hremEq : ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, ∀ (ha : 0 ≤ a),
      ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
        IsCenteredGaussianSeq G (fun i j =>
          HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
            (r26t3_mu R 0) p.γ (r26t3_qwin R a i) (r26t3_qwin R a j)) →
        ∀ G0 : GaussianRealization R, ∀ Φ : Window p → ℝ,
          Φ ∈ CbUnitBall (Window p) 5 →
            initialRemainder R future N G0 a ha Φ =
              fp81s21_staticResidual R N a G
                (fun z => initialHeat future a ha Φ 0
                  (fp81s21_initGauss_synthesis p z))) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N → 2 ≤ N → ∀ a : ℝ, ∀ (ha : 0 ≤ a),
        ∀ Φ : Window p → ℝ, Φ ∈ CbUnitBall (Window p) 5 →
          ∀ G0 : GaussianRealization R,
            |initialRemainder R future N G0 a ha Φ| ≤ ε := by
  intro ε hε
  let A : ℝ := 1 + ‖fp81s21_initGauss_synthesis p‖ ^ 5
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨N0, hN0⟩ := hstatic (ε / A) (by positivity)
  refine ⟨N0, ?_⟩
  intro N hN0N hN2 a ha Φ hΦ G0
  obtain ⟨G, hGp, hG⟩ := hgauss a ha
  letI : IsProbabilityMeasure G := hGp
  haveI : IsProbabilityMeasure (windowFuture future a ha 0) := by
    dsimp [windowFuture]
    exact (Measure.isProbabilityMeasure_map_iff
      (HRS.MS.ProClosureS111.physicalWindowRestriction
        (d := p.d) (m := wholeSpaceIndex p.d) (T := p.T)
        (H := a + p.T) ha le_rfl).continuous.aemeasurable).2
      (hf.1 (a + p.T) 0)
  obtain ⟨hFcd, _, hFball⟩ := fp81s21_initial_heat_pullback future a ha Φ hΦ
  let F : SeqL2 → ℝ := fun z => initialHeat future a ha Φ 0
    (fp81s21_initGauss_synthesis p z)
  let Fbar : SeqL2 → ℝ := fun z => A⁻¹ * F z
  have hFbarball : Fbar ∈ CbUnitBall SeqL2 5 := by
    simpa [Fbar, F, A] using hFball
  have hFbarcd : ContDiff ℝ 5 Fbar := hFbarball.1
  have hstat := hN0 N hN0N hN2 a ha hG Fbar hFbarball
  have hEq := hremEq N hN2 a ha hG G0 Φ hΦ
  have hdecomp : F = fun z => A * Fbar z := by
    funext z
    dsimp [Fbar]
    field_simp [hA.ne']
  have hscale : fp81s21_staticResidual R N a G F =
      A * fp81s21_staticResidual R N a G Fbar := by
    rw [hdecomp]
    exact fp81s21_staticResidual_const_mul R N a G Fbar A hFbarcd
  rw [hEq, hscale]
  rw [abs_mul, abs_of_pos hA]
  calc
    A * |fp81s21_staticResidual R N a G Fbar| ≤ A * (ε / A) :=
      mul_le_mul_of_nonneg_left hstat hA.le
    _ = ε := by field_simp [hA.ne']

#print axioms fp81s21_staticResidual_const_mul
#print axioms fp81s21_initial_profile_of_uniform_remainder
#print axioms fp81s21_initial_remainder_uniform_from_static
end HRS.Fp81.S21
end
