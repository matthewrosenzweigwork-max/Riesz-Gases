import HRS.MS.Fp81S21CovRS8
import HRS.MS.R2InterpAux79

/-! A moving-reference counterpart of the stationary `hh2` integrability lemma. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- For a moving-standard trajectory and an almost surely continuous particle path,
each cylindrical covariance density is integrable on the physical horizon. -/
theorem fp81s21_moving_hh2_integrable_of_movingStd
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) c hH)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) :
    ∀ (L : ℕ), ∀ᵐ ω ∂A.P, ∀ i j : Fin (s102_q p.d L),
      IntegrableOn
        (s102_hh2 (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          (s102_tauk hH L) (s102_alk L)
          (fun v => s102_etaf (r26t3_mu R v) A.X ω v) i j)
        (Icc (0 : ℝ) H) := by
  classical
  have hN0 : 0 < N := by omega
  intro L
  have hXcont : ∀ᵐ ω ∂A.P, ∀ k : Fin N,
      Continuous fun t : ℝ≥0 => A.X t ω k := (A.strong H).cont
  filter_upwards [hXcont] with ω hω
  intro i j
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  let mn : ℝ := min (s102_tk hH L i) (s102_tk hH L j)
  have hmnT : mn ≤ H := by
    dsimp [mn]
    exact (min_le_left _ _).trans (s102_tauk hH L i).2.2
  have hmn0 : 0 ≤ mn := by
    dsimp [mn]
    exact le_min (s102_tauk hH L i).2.1 (s102_tauk hH L j).2.1
  have hi : s102_tk hH L i ∈ Icc (0 : ℝ) H := (s102_tauk hH L i).2
  have hj : s102_tk hH L j ∈ Icc (0 : ℝ) H := (s102_tauk hH L j).2
  have hF1 := s102_propagator_classical (hstd.hcls (s102_alk L i) _ hi)
  have hF2 := s102_propagator_classical (hstd.hcls (s102_alk L j) _ hj)
  have hsub1 : Icc 0 mn ⊆ Icc 0 (s102_tk hH L i) :=
    Icc_subset_Icc le_rfl (min_le_left _ _)
  have hsub2 : Icc 0 mn ⊆ Icc 0 (s102_tk hH L j) :=
    Icc_subset_Icc le_rfl (min_le_right _ _)
  have hk : ∀ k : Fin N, ContinuousOn (fun u : ℝ =>
      inner ℝ
        (gradient (propagatorW C u (s102_tk hH L i)
          (oscTestFun m (s102_alk L i))) (A.X u.toNNReal ω k))
        (gradient (propagatorW C u (s102_tk hH L j)
          (oscTestFun m (s102_alk L j))) (A.X u.toNNReal ω k))) (Icc 0 mn) := by
    intro k
    rw [continuousOn_iff_continuous_restrict]
    have hpath : Continuous fun u : Icc (0 : ℝ) mn =>
        A.X (u : ℝ).toNNReal ω k :=
      (hω k).comp (continuous_real_toNNReal.comp continuous_subtype_val)
    simp_rw [s102_inner_eq_sum]
    refine continuous_finsetSum _ fun a _ => ?_
    have h1 := s102_grad_jointCont hF1 a
    have h2 := s102_grad_jointCont hF2 a
    have p1 : Continuous fun u : Icc (0 : ℝ) mn =>
        ((⟨u.1, hsub1 u.2⟩ : Icc (0 : ℝ) (s102_tk hH L i)),
          A.X (u : ℝ).toNNReal ω k) :=
      (continuous_subtype_val.subtype_mk _).prodMk hpath
    have p2 : Continuous fun u : Icc (0 : ℝ) mn =>
        ((⟨u.1, hsub2 u.2⟩ : Icc (0 : ℝ) (s102_tk hH L j)),
          A.X (u : ℝ).toNNReal ω k) :=
      (continuous_subtype_val.subtype_mk _).prodMk hpath
    exact (h1.comp p1).mul (h2.comp p2)
  have hgram : ContinuousOn (fun u => s102_gram C m hH L u i j)
      (Icc 0 mn) := by
    simpa [C, m, mn] using hstd.hGram L i j
  have hcont : ContinuousOn (fun u =>
      s102_etaf (r26t3_mu R u) A.X ω u (fun x =>
        inner ℝ
          (gradient (propagatorW C u (s102_tk hH L i)
            (oscTestFun m (s102_alk L i))) x)
          (gradient (propagatorW C u (s102_tk hH L j)
            (oscTestFun m (s102_alk L j))) x))) (Icc 0 mn) := by
    have hfun : ∀ u ∈ Icc 0 mn,
        s102_etaf (r26t3_mu R u) A.X ω u (fun x =>
          inner ℝ
            (gradient (propagatorW C u (s102_tk hH L i)
              (oscTestFun m (s102_alk L i))) x)
            (gradient (propagatorW C u (s102_tk hH L j)
              (oscTestFun m (s102_alk L j))) x)) =
        Real.sqrt N * ((N : ℝ)⁻¹ * ∑ k : Fin N,
          inner ℝ
            (gradient (propagatorW C u (s102_tk hH L i)
              (oscTestFun m (s102_alk L i))) (A.X u.toNNReal ω k))
            (gradient (propagatorW C u (s102_tk hH L j)
              (oscTestFun m (s102_alk L j))) (A.X u.toNNReal ω k)) -
          s102_gram C m hH L u i j) := by
      intro u hu
      have huH : u ∈ Icc (0 : ℝ) H := ⟨hu.1, hu.2.trans hmnT⟩
      have hpair : HRS.Whole.pair (r26t3_mu R u) (fun x =>
          inner ℝ
            (gradient (propagatorW C u (s102_tk hH L i)
              (oscTestFun m (s102_alk L i))) x)
            (gradient (propagatorW C u (s102_tk hH L j)
              (oscTestFun m (s102_alk L j))) x)) =
          s102_gram C m hH L u i j := by
        change HRS.Whole.pair (HRS.Whole.withDensityReal (R.ρ u)) _ = _
        rw [HRS.Whole.Q09A.pair_withDensityReal ((R.resulting.global H).density u huH)]
        unfold s102_gram
        have hρC : C.ρ = R.ρ := rfl
        rw [hρC]
        exact integral_congr_ae (Eventually.of_forall fun x => by ring)
      unfold s102_etaf
      rw [HRS.Whole.pair_empirical hN0, hpair]
    refine ContinuousOn.congr ?_ hfun
    refine continuousOn_const.mul (ContinuousOn.sub ?_ hgram)
    exact continuousOn_const.mul
      (continuousOn_finsetSum _ fun k _ => hk k)
  have hI : IntegrableOn (fun u =>
      s102_etaf (r26t3_mu R u) A.X ω u (fun x =>
        inner ℝ
          (gradient (propagatorW C u (s102_tk hH L i)
            (oscTestFun m (s102_alk L i))) x)
          (gradient (propagatorW C u (s102_tk hH L j)
            (oscTestFun m (s102_alk L j))) x))) (Icc 0 mn) :=
    hcont.integrableOn_Icc
  unfold s102_hh2
  refine (integrable_indicator_iff measurableSet_Iic).2 ?_
  rw [IntegrableOn, Measure.restrict_restrict measurableSet_Iic]
  refine hI.mono_set ?_
  intro u hu
  exact ⟨hu.2.1, hu.1⟩

#print axioms HRS.Fp81.S21.fp81s21_moving_hh2_integrable_of_movingStd

end HRS.Fp81.S21
end
