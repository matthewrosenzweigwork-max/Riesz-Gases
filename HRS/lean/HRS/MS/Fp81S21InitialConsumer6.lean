import HRS.MS.Fp81S21InitialConsumer5
import HRS.MS.Fp81S21QwinUniform
import HRS.MS.Fp81S21InitGaussIid

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace HRS.Fp81.S21
open HRS.Whole HRS.MS.R26T3

/-- The zero-coupling branch of the packet-28 consumer. The branch
hypothesis precedes the common radius. -/
theorem fp81s21_initial_uniform_in_shift_zero (p : Parameters) (hγ : p.γ = 0) :
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
  obtain ⟨δs, hδs, hδsh, hstatic⟩ :=
    fp81s21_initial_static_uniform_zero p hγ
  obtain ⟨δi, hδi, hδih, hiid⟩ := fp81s21_initGaussIid_endpoint p
  obtain ⟨δt, hδt, hδth, htransport⟩ :=
    fp81s21_initial_remainder_eq_staticResidual p
  obtain ⟨δq, hδq, hδqh, hqwin⟩ := fp81s21_qwin_uniform p
  obtain ⟨δf, hδf, hδfh, hfeature⟩ := fp81s21_qwin_featureSum_uniform p
  let δ28 := min δs (min δi (min δt (min δq δf)))
  have hδ28 : 0 < δ28 := by dsimp [δ28]; positivity
  have hδ28h : δ28 ≤ 1 / 2 :=
    (min_le_left _ _).trans hδsh
  refine ⟨δ28, hδ28, hδ28h, ?_⟩
  intro δ hδ hδle R hμ future hf
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ
  have hδs' : δ ≤ δs := hδle.trans (min_le_left _ _)
  have hδi' : δ ≤ δi := hδle.trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδt' : δ ≤ δt := hδle.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδq' : δ ≤ δq := hδle.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
  have hδf' : δ ≤ δf := hδle.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ28h
  have hstaticR := hstatic δ hδ hδs' R
  have hgaussR : ∀ a : ℝ, 0 ≤ a → ∃ G : Measure SeqL2,
      IsProbabilityMeasure G ∧ IsCenteredGaussianSeq G (fun i j =>
        HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
          (r26t3_mu R 0) p.γ (r26t3_qwin R a i) (r26t3_qwin R a j)) := by
    intro a ha
    obtain ⟨G, hGp, hG, _⟩ := hiid δ hδ hδi' R hγ a ha
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
    exact htransport δ hδ hδt' R (Or.inr hγ) future hf a ha G hG G0 N hN Φ hΦ
  obtain ⟨Cq, hCq, hqfamily⟩ := hqwin δ hδ hδq' R
  obtain ⟨Cs, hCs, hfsum⟩ := hfeature δ hδ hδf' R
  let D : ℝ := 2 * (Cs * (∑' j : ℕ, r26t3_feature_weight p.d j))
  have hfeatureNonneg : ∀ a : ℝ, 0 ≤ a →
      0 ≤ featureSum (r26t3_J p.d) (r26t3_qwin R a) := by
    intro a ha
    dsimp [featureSum]
    exact tsum_nonneg fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hDprod : 0 ≤ Cs * (∑' j : ℕ, r26t3_feature_weight p.d j) :=
    (hfeatureNonneg 0 le_rfl).trans (hfsum 0 le_rfl)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (by norm_num) hDprod
  have hfinite : ∀ N : ℕ, 2 ≤ N → ∃ B : ℝ, 0 ≤ B ∧
      ∀ a : ℝ, ∀ (ha : 0 ≤ a), ∀ Φ : Window p → ℝ,
        Φ ∈ CbUnitBall (Window p) 5 → ∀ G0 : GaussianRealization R,
          |initialRemainder R future N G0 a ha Φ| ≤ B := by
    intro N hN
    let A : ℝ := 1 + ‖fp81s21_initGauss_synthesis p‖ ^ 5
    let B : ℝ := A * (2 * Real.sqrt N + (1 / 6) * D ^ 3)
    have hA : 0 < A := by dsimp [A]; positivity
    have hB : 0 ≤ B := by dsimp [B]; positivity
    refine ⟨B, hB, ?_⟩
    intro a ha Φ hΦ G0
    obtain ⟨G, hGp, hG⟩ := hgaussR a ha
    letI : IsProbabilityMeasure G := hGp
    have hq := hqfamily a ha
    have hell : ∀ x : Euc p.d,
        ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖ ≤ D := by
      intro x
      have hvec := fp81s21_respIid_vector_bounds hδ hδhalf R hγ a ha x hq.1
      calc
        ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖ ≤
            2 * featureSum (r26t3_J p.d) (r26t3_qwin R a) := hvec.2.2
        _ ≤ D := by
          dsimp [D]
          exact mul_le_mul_of_nonneg_left (hfsum a ha) (by norm_num)
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
    have hstaticBound := fp81s21_initial_staticResidual_abs_bound
      hδ hδhalf R hγ N hN a ha (G := G) Fbar hFbarball D hD hell
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
    rw [hrem, hscale, abs_mul, abs_of_pos hA]
    dsimp [B]
    exact mul_le_mul_of_nonneg_left hstaticBound hA.le
  have hconv := fp81s21_initial_remainder_uniform_from_static hδ R future hf
    (Or.inr hγ) hstaticR hgaussR hremEq
  exact fp81s21_initial_profile_of_uniform_remainder R future hf hfinite hconv

/-- The two coupling branches together give the packet-28 consumer contract. -/
theorem fp81s21_initial_uniform_in_shift (p : Parameters) :
    fp81s21_initial_uniform_in_shift_contract p := by
  unfold fp81s21_initial_uniform_in_shift_contract
  rcases eq_or_lt_of_le p.hγ with hzero | hpos
  · exact fp81s21_initial_uniform_in_shift_zero p hzero.symm
  · exact fp81s21_initial_uniform_in_shift_pos p hpos

#print axioms fp81s21_initial_uniform_in_shift_zero
#print axioms fp81s21_initial_uniform_in_shift
end HRS.Fp81.S21
end
