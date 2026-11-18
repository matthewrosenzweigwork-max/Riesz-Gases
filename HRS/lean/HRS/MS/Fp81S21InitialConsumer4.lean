import HRS.MS.Fp81S21InitialConsumer3
import HRS.MS.Fp81S21InitGauss

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace HRS.Fp81.S21
open HRS.Whole HRS.MS.R26T3

/-- The positive-coupling branch of the packet-28 consumer. The branch
hypothesis precedes the common radius. -/
theorem fp81s21_initial_uniform_in_shift_pos (p : Parameters) (hγ : 0 < p.γ) :
    ∃ δ28 : ℝ, 0 < δ28 ∧ δ28 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ28 → ∀ R : Trajectory p δ,
        ∀ [IsProbabilityMeasure (r26t3_mu R 0)],
        ∀ future : Future p, ValidFuture R future →
          ∃ α : ℕ → ℝ,
            (∀ N, 0 ≤ α N) ∧ Tendsto α atTop (𝓝 0) ∧
            ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, ∀ (ha : 0 ≤ a),
              ∀ Φ : Window p → ℝ, Φ ∈ CbUnitBall (Window p) 5 →
                ∀ G0 : GaussianRealization R,
                  |initialRemainder R future N G0 a ha Φ| ≤ α N := by
  obtain ⟨δs, hδs, hδsh, hstatic⟩ := fp81s21_initial_static_uniform_pos p hγ
  obtain ⟨δl, hδl, hδlh, hlarge⟩ := fp81s21_initial_large_shift p hγ
  obtain ⟨δg, hδg, hδgh, hgauss⟩ := fp81s21_initGauss_positive p
  obtain ⟨δt, hδt, hδth, htransport⟩ :=
    fp81s21_initial_remainder_eq_staticResidual p
  let δ28 := min δs (min δl (min δg δt))
  have hδ28 : 0 < δ28 := by dsimp [δ28]; positivity
  have hδ28h : δ28 ≤ 1 / 2 :=
    (min_le_left _ _).trans hδsh
  refine ⟨δ28, hδ28, hδ28h, ?_⟩
  intro δ hδ hδle R hμ future hf
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ
  have hδs' : δ ≤ δs := hδle.trans (min_le_left _ _)
  have hδl' : δ ≤ δl := hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδg' : δ ≤ δg := hδle.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδt' : δ ≤ δt := hδle.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ28h
  have hstaticR := hstatic δ hδ hδs' R
  obtain ⟨C, c, hC, hc, hlargeR⟩ := hlarge δ hδ hδl' R
  let A : ℝ := 1 + ‖fp81s21_initGauss_synthesis p‖ ^ 5
  have hA : 0 < A := by dsimp [A]; positivity
  have hgaussR : ∀ a : ℝ, 0 ≤ a → ∃ G : Measure SeqL2,
      IsProbabilityMeasure G ∧ IsCenteredGaussianSeq G (fun i j =>
        HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
          (r26t3_mu R 0) p.γ (r26t3_qwin R a i) (r26t3_qwin R a j)) := by
    intro a ha
    obtain ⟨G, hGp, hG, _⟩ := hgauss δ hδ hδg' R hγ a ha
    exact ⟨G, hGp, hG⟩
  have hremEq : ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, ∀ (ha : 0 ≤ a),
      ∀ {G : Measure SeqL2} [IsProbabilityMeasure G],
        IsCenteredGaussianSeq G (fun i j =>
          HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
            (r26t3_mu R 0) p.γ (r26t3_qwin R a i) (r26t3_qwin R a j)) →
        ∀ G0 : GaussianRealization R, ∀ Φ : Window p → ℝ,
          Φ ∈ CbUnitBall (Window p) 5 →
            initialRemainder R future N G0 a ha Φ =
              fp81s21_staticResidual R N a G
                (fun z => initialHeat future a ha Φ 0
                  (fp81s21_initGauss_synthesis p z)) := by
    intro N hN a ha G _ hG G0 Φ hΦ
    exact htransport δ hδ hδt' R (Or.inl hγ) future hf a ha G hG G0 N hN Φ hΦ
  have hfinite : ∀ N : ℕ, 2 ≤ N → ∃ B : ℝ, 0 ≤ B ∧
      ∀ a : ℝ, ∀ (ha : 0 ≤ a), ∀ Φ : Window p → ℝ,
        Φ ∈ CbUnitBall (Window p) 5 → ∀ G0 : GaussianRealization R,
          |initialRemainder R future N G0 a ha Φ| ≤ B := by
    intro N hN
    refine ⟨A * C, mul_nonneg hA.le hC, ?_⟩
    intro a ha Φ hΦ G0
    obtain ⟨G, hGp, hG⟩ := hgaussR a ha
    letI : IsProbabilityMeasure G := hGp
    haveI : IsProbabilityMeasure (windowFuture future a ha 0) := by
      dsimp [windowFuture]
      exact (Measure.isProbabilityMeasure_map_iff
        (HRS.MS.ProClosureS111.physicalWindowRestriction
          (d := p.d) (m := wholeSpaceIndex p.d) (T := p.T)
          (H := a + p.T) ha le_rfl).continuous.aemeasurable).2
        (hf.1 (a + p.T) 0)
    obtain ⟨_, _, hFball⟩ := fp81s21_initial_heat_pullback future a ha Φ hΦ
    let F : SeqL2 → ℝ := fun z => initialHeat future a ha Φ 0
      (fp81s21_initGauss_synthesis p z)
    let Fbar : SeqL2 → ℝ := fun z => A⁻¹ * F z
    have hFbarball : Fbar ∈ CbUnitBall SeqL2 5 := by
      simpa [Fbar, F, A] using hFball
    have hlargeN := hlargeR N hN a ha (G := G) hG Fbar hFbarball
    have hlargeN' : |fp81s21_staticResidual R N a G Fbar| ≤
        C * Real.exp (-c * a) := by
      simpa [fp81s21_staticResidual] using hlargeN
    have hrem := hremEq N hN a ha hG G0 Φ hΦ
    have hFbarcd : ContDiff ℝ 5 Fbar := hFbarball.1
    have hdecomp : F = fun z => A * Fbar z := by
      funext z
      dsimp [Fbar]
      field_simp [hA.ne']
    have hscale : fp81s21_staticResidual R N a G F =
        A * fp81s21_staticResidual R N a G Fbar := by
      rw [hdecomp]
      exact fp81s21_staticResidual_const_mul R N a G Fbar A hFbarcd
    have hexp : Real.exp (-c * a) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [mul_nonneg hc.le ha]
    rw [hrem, hscale, abs_mul, abs_of_pos hA]
    calc
      A * |fp81s21_staticResidual R N a G Fbar| ≤
          A * (C * Real.exp (-c * a)) := mul_le_mul_of_nonneg_left hlargeN' hA.le
      _ ≤ A * C := by
        calc
          A * (C * Real.exp (-c * a)) ≤ A * (C * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hC) hA.le
          _ = A * C := by ring
  have hconv := fp81s21_initial_remainder_uniform_from_static hδ R future hf
    (Or.inl hγ) hstaticR hgaussR hremEq
  exact fp81s21_initial_profile_of_uniform_remainder R future hf hfinite hconv

#print axioms fp81s21_initial_uniform_in_shift_pos
end HRS.Fp81.S21
end
