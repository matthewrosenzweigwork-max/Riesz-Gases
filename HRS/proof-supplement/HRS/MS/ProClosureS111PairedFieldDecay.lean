import HRS.MS.ProClosureS111ChartCoordinates
import HRS.MS.ProClosureS111CoeffMoments
import HRS.MS.ProClosureS111PairedWick
import HRS.MS.R2ChaosAux56

/-!
The sharp physical paired scalar bounds are summed through the proved
thermal chart traces. This gives actual coefficient-norm L2 decay for
every pair of realizations satisfying the frozen chart-coordinate
identities, including the exactly zero-mass versions. No pointwise field
moment estimate is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Chaos

variable {d r : ℕ} {Pw : ℝ}

/-- Both coefficient differences decay at the sharp squared rate. The
single constant is chosen before density, preparation, horizon, chart,
probability realization, and time. The coordinate identities are used
only in their original almost-everywhere-in-time order. -/
theorem physical_paired_chart_field_decay (hd : 2 ≤ d)
    (s a beta lam : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ)/2)
    (ha : 0 < a) (hbeta : 0 < beta) (hlam : 0 < lam)
    (hr : (2 : ℝ)+(d : ℝ)/2 < r) (hPw : (d : ℝ) < 2*Pw) :
    ∃ C : ℝ, 0 < C ∧ ∀ rho : Euc d → ℝ,
      HRS.Whole.IsThermalEquilibrium d s a beta rho →
      HRS.Whole.IsR2Poincare (HRS.Whole.withDensityReal rho) lam →
      ∀ gamma : ℝ, 0 ≤ gamma →
      ∀ (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega)
        [IsProbabilityMeasure P] (H : ℝ)
        (Z : Fin 2 → ℝ → Omega → OscDual d (wholeSpaceIndex d)),
      r26t6_SharedThermalLaw P s a beta gamma H rho Z →
      ∀ (E : r26t6_WeightedChart d r Pw) (basis : ℕ → Euc d → ℝ),
      HRS.Whole.IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis →
      ∀ qLin qQuad : Fin 2 → ℝ × Omega → r26t6_Coeff,
      (∀ i, r26t6_PhysicalChartFields P rho s H E basis (Z i) (qLin i) (qQuad i)) →
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) H),
        (MemLp (fun w => qLin 0 (t,w)-qLin 1 (t,w)) 2 P ∧
          (∫ w, ‖qLin 0 (t,w)-qLin 1 (t,w)‖^2 ∂P) ≤
            C * Real.exp (-2*(lam/beta)*t)) ∧
        (MemLp (fun w => qQuad 0 (t,w)-qQuad 1 (t,w)) 2 P ∧
          (∫ w, ‖qQuad 0 (t,w)-qQuad 1 (t,w)‖^2 ∂P) ≤
            C * Real.exp (-2*(lam/beta)*t)) := by
  obtain ⟨A, hA, hdec⟩ := physical_initial_difference_variance_decay
    hd s a beta lam hs0 hs ha hbeta hlam
  obtain ⟨W, hW, hwick⟩ := physical_paired_wick_bound
    hd s a beta lam hs0 hs ha hbeta hlam
  obtain ⟨T, hT, htrace⟩ := physical_chart_thermal_traces
    hd s a beta Pw r hs0 hs ha hbeta hr hPw
  obtain ⟨L, hL, hseq⟩ := physical_gaussian_sequence_uniform hd s a beta hs0 hs ha hbeta
  let C : ℝ := 1 + (A+W)*T
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun rho hrho hgap gamma hgamma Omega _ P _ H Z hZ E basis hbasis qLin qQuad hfields => ?_⟩
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.1.1
  have hval := (htrace rho hrho E).1
  have hker := (htrace rho hrho E).2
  filter_upwards [(hfields 0).linear_coordinates, (hfields 1).linear_coordinates,
    (hfields 0).wick_coordinates, (hfields 1).wick_coordinates,
    ae_restrict_mem measurableSet_Icc] with t hl0 hl1 hw0 hw1 ht
  let e : ℝ := Real.exp (-2*(lam/beta)*t)
  have he : 0 ≤ e := (Real.exp_pos _).le
  let DL : Omega → r26t6_Coeff := fun w => qLin 0 (t,w)-qLin 1 (t,w)
  let DQ : Omega → r26t6_Coeff := fun w => qQuad 0 (t,w)-qQuad 1 (t,w)
  have hDL : ∀ j,
      MemLp (fun w => DL w j) 2 P ∧
      (∫ w, DL w j^2 ∂P) ≤ A*e * ∫ x, E.test j x^2 ∂mu := by
    intro j
    let D : Omega → ℝ := fun w =>
      OscDual.eval (Z 0 t w) (E.test j)-OscDual.eval (Z 1 t w) (E.test j)
    have hphi := r2Test_isOscTest (wholeSpaceIndex d) (E.test_smooth j)
    obtain ⟨hD4, hDsq, _⟩ := physical_shared_difference_moments
      hd hs0 hs ha hbeta hgamma hrho hZ ht hphi
    have hEq : (fun w => DL w j) =ᵐ[P] D := by
      filter_upwards [hl0 j, hl1 j] with w h0 h1
      simp only [DL, lp.coeFn_sub, Pi.sub_apply, h0, h1, D]
    refine ⟨(memLp_congr_ae hEq).2 (hD4.mono_exponent (by norm_num)), ?_⟩
    refine (le_of_eq ((integral_congr_ae (hEq.fun_comp (fun x : ℝ => x^2))).trans hDsq)).trans ?_
    exact (hdec rho hrho hgap gamma hgamma t ht.1 (E.test j) hphi).trans
      (mul_le_mul_of_nonneg_left (centered_square_le_square mu (E.test j) (hval.1 j))
        (mul_nonneg hA.le he))
  have hz : ∀ i : Fin 2,
      S94GSeq P (fun j w => OscDual.eval (Z i t w) (basis j)) L := by
    intro i
    have hi : 0 ≤ r26t6_preparation beta gamma i := by
      unfold r26t6_preparation
      split_ifs
      · exact hgamma
      · exact hbeta.le
    exact hseq rho hrho (r26t6_preparation beta gamma i) hi Omega P H (Z i)
      (hZ.evolution i) basis hbasis t ht
  have hDQ : ∀ j,
      MemLp (fun w => DQ w j) 2 P ∧
      (∫ w, DQ w j^2 ∂P) ≤ W*e * ∫ xy : Euc d × Euc d,
        HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2 ^ 2 ∂mu.prod mu := by
    intro j
    let Q0 : Omega → ℝ := fun w => -2*qQuad 0 (t,w) j
    let Q1 : Omega → ℝ := fun w => -2*qQuad 1 (t,w) j
    have hQ0 := s94_isWick_to_L2 (hz 0) (hw0 j)
    have hQ1 := s94_isWick_to_L2 (hz 1) (hw1 j)
    have hD2 : MemLp (fun w => DQ w j) 2 P := by
      have hm := (hQ0.1.sub hQ1.1).const_mul (-1/2 : ℝ)
      refine (memLp_congr_ae (ae_of_all P fun w => ?_)).1 hm
      simp only [Pi.sub_apply, DQ, lp.coeFn_sub]
      ring
    have hb := hwick rho hrho hgap gamma hgamma Omega P H Z hZ basis hbasis t ht
      (HRS.Whole.commutatorKernel d s (gradient (E.test j))) (hker.1 j)
      Q0 Q1 (hw0 j) (hw1 j) hQ0.1 hQ1.1
    have heq : (fun w => (Q0 w-Q1 w)^2) = fun w => 4*(DQ w j)^2 := by
      funext w
      simp only [Q0, Q1, DQ, lp.coeFn_sub, Pi.sub_apply]
      ring
    rw [heq, integral_const_mul] at hb
    have hn : 0 ≤ ∫ w, (DQ w j)^2 ∂P := integral_nonneg fun _ => sq_nonneg _
    exact ⟨hD2, by change _ ≤ W*Real.exp (-2*(lam/beta)*t)*_; nlinarith⟩
  have hLbound := coeff_second_moment_bound P DL (fun j => (hDL j).1)
    (fun j => A*e * ∫ x, E.test j x^2 ∂mu) (hval.2.1.mul_left (A*e))
    (fun j => (hDL j).2)
  have hQbound := coeff_second_moment_bound P DQ (fun j => (hDQ j).1)
    (fun j => W*e * ∫ xy : Euc d × Euc d,
      HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2 ^ 2 ∂mu.prod mu)
    (hker.2.1.mul_left (W*e)) (fun j => (hDQ j).2)
  have hLT : (∫ w, ‖DL w‖^2 ∂P) ≤ A*e*T := by
    refine hLbound.2.trans ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hval.2.2 (mul_nonneg hA.le he)
  have hQT : (∫ w, ‖DQ w‖^2 ∂P) ≤ W*e*T := by
    refine hQbound.2.trans ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hker.2.2 (mul_nonneg hW.le he)
  have hLC : A*T ≤ C := by dsimp [C]; nlinarith [mul_nonneg hW.le hT]
  have hQC : W*T ≤ C := by dsimp [C]; nlinarith [mul_nonneg hA.le hT]
  refine ⟨⟨hLbound.1, hLT.trans ?_⟩, ⟨hQbound.1, hQT.trans ?_⟩⟩
  · convert mul_le_mul_of_nonneg_right hLC he using 1 <;> dsimp [e] <;> ring
  · convert mul_le_mul_of_nonneg_right hQC he using 1 <;> dsimp [e] <;> ring

#print axioms physical_paired_chart_field_decay

end HRS.MS.ProClosureS111
