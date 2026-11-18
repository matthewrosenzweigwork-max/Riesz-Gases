import HRS.MS.Fp81S21WeightedGenMeas
import HRS.MS.Fp81S21WeightedGenPrimal
import HRS.MS.Fp81S21WeightedGenCoef2
import HRS.MS.S104eC5B
import HRS.Whole.MovtrAux4
import HRS.MS.SA12V4

/-! Measurability of the weighted-generator images of the chart basis. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

private theorem fp81s21_b3_rho_clamped_time_continuous
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (x : Euc p.d) :
    Continuous (fun u : ℝ => R.ρ (max u 0) x) := by
  apply continuous_iff_continuousAt.2
  intro u
  rw [Metric.continuousAt_iff]
  intro ε hε
  let T : ℝ := max u 0 + 1
  have hT : 0 < T := by dsimp [T]; linarith [le_max_right u 0]
  let N : ℕ := fp81s21_b3_q p + 2
  have hN : N ≤ 100 * p.d + 1000 := by
    dsimp [N, fp81s21_b3_q]
    omega
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  obtain ⟨η, hη, hclose⟩ := HRS.MS.S104e.c5_rho_cont p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ N 0 hN R.thermal R.resulting T (ε / 2) (by positivity)
  let η' : ℝ := min η 1
  have hη' : 0 < η' := lt_min hη zero_lt_one
  refine ⟨η', hη', ?_⟩
  intro v hv
  have hdist : dist v u < η' := hv
  have hdistη : dist v u < η := lt_of_lt_of_le hdist (min_le_left _ _)
  have hclamp : |max v 0 - max u 0| ≤ |v - u| :=
    abs_max_sub_max_le_abs v u 0
  have htime : |max v 0 - max u 0| < η := by
    have hdistAbs : |v - u| < η := by simpa [Real.dist_eq] using hdistη
    exact lt_of_le_of_lt hclamp hdistAbs
  have htime1 : |max v 0 - max u 0| < 1 := by
    have hdistAbs : |v - u| < η' := by simpa [Real.dist_eq] using hdist
    have htime' : |max v 0 - max u 0| < η' := lt_of_le_of_lt hclamp hdistAbs
    exact lt_of_lt_of_le htime' (min_le_right _ _)
  have hu_mem : max u 0 ∈ Set.Icc (0 : ℝ) T := by
    constructor
    · exact le_max_right _ _
    · dsimp [T]
      linarith
  have hv_mem : max v 0 ∈ Set.Icc (0 : ℝ) T := by
    constructor
    · exact le_max_right _ _
    · dsimp [T]
      have hupper := (abs_lt.mp htime1).2
      linarith
  have hdec := hclose (max v 0) hv_mem (max u 0) hu_mem htime
  have hiter := hdec.2 0 (by omega) x
  have hnorm : ‖R.ρ (max v 0) x - R.ρ (max u 0) x‖ ≤ ε / 2 := by
    have h' : ‖iteratedFDeriv ℝ 0 (fun y => R.ρ (max v 0) y - R.ρ (max u 0) y) x‖ ≤ ε / 2 :=
      by simpa [HRS.Whole.u2Wt] using hiter
    simpa using h'
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (by simpa [Real.dist_eq] using hnorm) (by linarith)

private theorem fp81s21_b3_conv_measurable
    {d : ℕ} {s : ℝ} (g : ℝ → Euc d → ℝ)
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun p : ℝ × Euc d =>
      convGradConvW (rieszKernelGrad d s) (g p.1) p.2) := by
  let integrand : (ℝ × Euc d) × Euc d → Euc d := fun z =>
    if ‖z.1.2 - z.2‖ ≤ (1 / 4 : ℝ) then
      (g z.1.1 z.2 - g z.1.1 z.1.2) • rieszKernelGrad d s (z.1.2 - z.2)
    else g z.1.1 z.2 • rieszKernelGrad d s (z.1.2 - z.2)
  have hsub : Measurable (fun z : (ℝ × Euc d) × Euc d => z.1.2 - z.2) :=
    measurable_snd.comp measurable_fst |>.sub measurable_snd
  have hy : Measurable (fun z : (ℝ × Euc d) × Euc d => (z.1.1, z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hx : Measurable (fun z : (ℝ × Euc d) × Euc d => (z.1.1, z.1.2)) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst)
  have hgy : Measurable (fun z : (ℝ × Euc d) × Euc d => g z.1.1 z.2) := hg.comp hy
  have hgx : Measurable (fun z : (ℝ × Euc d) × Euc d => g z.1.1 z.1.2) := hg.comp hx
  have hK : Measurable (rieszKernelGrad d s) :=
    HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) s
  have hG : Measurable (fun z : (ℝ × Euc d) × Euc d =>
      rieszKernelGrad d s (z.1.2 - z.2)) := hK.comp hsub
  have hint : Measurable integrand := by
    dsimp [integrand]
    refine Measurable.ite
      (measurableSet_le (measurable_norm.comp hsub) measurable_const) ?_ ?_
    · exact (hgy.sub hgx).smul hG
    · exact hgy.smul hG
  have hI : Measurable (fun p : ℝ × Euc d => ∫ y, integrand (p, y)) :=
    (hint.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Euc d)))).measurable
  convert hI using 1
  funext p
  simp [integrand, convGradConvW]

private theorem fp81s21_b3_coeff_drift_formula
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (u : ℝ) :
    (r26t3_coeff R).drift u = fun x =>
      -convGradConvW (rieszKernelGrad p.d p.s) (R.ρ u) x - p.a • x := by
  funext x
  simp [r26t3_coeff, WholeDyn.coeff, quadraticGradientDyn, meanFieldDriftW,
    Torus.matVec, HRS.Whole.movtr_gradient_confinement]

/-- The generator image of each strong-chart basis test is measurable in the
coefficient chart. The conditional bound is the finite-norm output contract
consumed by the primal/adjoint assembly. -/
theorem fp81s21_b3_basis_measurable
    {p : Parameters} {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ ≤ (1 / 2 : ℝ))
    (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (fp81s21_q p) (fp81s21_P p + 2))
    (E : r26t6_WeightedChart p.d (fp81s21_q p + 2) (fp81s21_P p))
    (A : ℝ) (hb : fp81s21_bound R A) :
    ∀ j, Measurable (fun u : ℝ =>
      Es.encode (generatorW (r26t3_coeff R) (max u 0) (E.test j))) := by
  let ρclamp : ℝ → Euc p.d → ℝ := fun u x => R.ρ (max u 0) x
  have hρtime : ∀ x, Continuous (fun u => ρclamp u x) :=
    fun x => fp81s21_b3_rho_clamped_time_continuous R x
  have hρspatial : ∀ u, Continuous (ρclamp u) := fun u =>
    R.resulting.regular (max u 0) (le_max_right _ _)
  have hρjoint : Measurable (Function.uncurry ρclamp) :=
    measurable_uncurry_of_continuous_of_measurable hρtime
      (fun u => (hρspatial u).measurable)
  have hforce : Measurable (fun z : ℝ × Euc p.d =>
      convGradConvW (rieszKernelGrad p.d p.s) (ρclamp z.1) z.2) :=
    fp81s21_b3_conv_measurable ρclamp hρjoint
  have hdrift : Measurable (fun p : ℝ × Euc p.d =>
      (r26t3_coeff R).drift (max p.1 0) p.2) := by
    have hformula : (fun z : ℝ × Euc p.d =>
        (r26t3_coeff R).drift (max z.1 0) z.2) = fun z =>
        -convGradConvW (rieszKernelGrad p.d p.s) (ρclamp z.1) z.2 - p.a • z.2 := by
      funext z
      exact congrFun (fp81s21_b3_coeff_drift_formula R (max z.1 0)) z.2
    rw [hformula]
    have hforce' : Measurable (fun z : ℝ × Euc p.d =>
        convGradConvW (rieszKernelGrad p.d p.s) (R.ρ (max z.1 0)) z.2) := by
      simpa [ρclamp] using hforce
    have hlinearC : Continuous (fun z : ℝ × Euc p.d => p.a • z.2) :=
      (continuous_const : Continuous (fun _ : ℝ × Euc p.d => p.a)).smul continuous_snd
    have hlinear : Measurable (fun z : ℝ × Euc p.d => p.a • z.2) := hlinearC.measurable
    exact hforce'.neg.sub hlinear
  have hP : (p.d : ℝ) < 2 * fp81s21_P p := by
    dsimp [fp81s21_P]
    have hd : 0 ≤ (p.d : ℝ) := Nat.cast_nonneg _
    linarith
  have htestInput : ∀ j, fp81s21_Input p (E.test j) := by
    intro j
    change IsR2WeightedTest (fp81s21_q p + 2) (fp81s21_P p) (E.test j)
    exact weightedTestSubmodule_iff.1
      (weighted_test_of_compact_smooth
        (r := fp81s21_q p + 2) (Pw := fp81s21_P p) hP (E.test_smooth j))
  intro j
  let f : Euc p.d → ℝ := E.test j
  have hf2 : ContDiff ℝ 2 f := by
    exact (E.test_smooth j).1.of_le (by norm_num)
  have hgrad : Continuous (gradient f) := by
    have heq : gradient f = (InnerProductSpace.toDual ℝ (Euc p.d)).symm ∘ fderiv ℝ f := rfl
    rw [heq]
    exact (InnerProductSpace.toDual ℝ (Euc p.d)).symm.continuous.comp
      (hf2.continuous_fderiv (by norm_num))
  have hlap : Continuous (Laplacian.laplacian f) :=
    HRS.MH.AdjointRd.Phase2SA12Construction.sa12v_lap_cont hf2
  have hgenJoint : Measurable (fun z : ℝ × Euc p.d =>
      generatorW (r26t3_coeff R) (max z.1 0) f z.2) := by
    have hlocalPair : Measurable (fun z : ℝ × Euc p.d =>
        inner ℝ ((r26t3_coeff R).drift (max z.1 0) z.2) (gradient f z.2)) := by
      exact continuous_inner.measurable.comp
        (hdrift.prodMk (hgrad.measurable.comp measurable_snd))
    have hlocal : Measurable (fun z : ℝ × Euc p.d =>
        (r26t3_coeff R).ν * Laplacian.laplacian f z.2 +
          inner ℝ ((r26t3_coeff R).drift (max z.1 0) z.2) (gradient f z.2)) := by
      have hlapJoint : Measurable (fun z : ℝ × Euc p.d =>
          (r26t3_coeff R).ν * Laplacian.laplacian f z.2) :=
        ((continuous_const.mul hlap).comp continuous_snd).measurable
      exact hlapJoint.add hlocalPair
    have hnonlocal : Measurable (fun z : ℝ × Euc p.d =>
        ∑ i : Fin p.d, (convGradConvW (rieszKernelGrad p.d (r26t3_coeff R).s)
          (fun y => ρclamp z.1 y *
            (Torus.matVec (r26t3_coeff R).M.transpose (gradient f y)) i) z.2) i) := by
      refine Finset.measurable_fun_sum _ fun i _ => ?_
      let src : ℝ → Euc p.d → ℝ := fun u y => ρclamp u y *
        (Torus.matVec (r26t3_coeff R).M.transpose (gradient f y)) i
      have hmatrix : Continuous (fun y : Euc p.d =>
          (Torus.matVec (r26t3_coeff R).M.transpose (gradient f y)) i) := by
        have hlin : Continuous (fun v : Euc p.d =>
            (Torus.matVec (r26t3_coeff R).M.transpose v) i) := by
          exact (EuclideanSpace.proj i).continuous.comp
            (Matrix.toEuclideanLin (r26t3_coeff R).M.transpose).continuous_of_finiteDimensional
        exact hlin.comp hgrad
      have hsrc : Measurable (Function.uncurry src) := by
        change Measurable (fun z : ℝ × Euc p.d => ρclamp z.1 z.2 *
          (Torus.matVec (r26t3_coeff R).M.transpose (gradient f z.2)) i)
        exact hρjoint.mul ((hmatrix.measurable.comp measurable_snd))
      have hconv : Measurable (fun z : ℝ × Euc p.d =>
          convGradConvW (rieszKernelGrad p.d p.s) (src z.1) z.2) :=
        fp81s21_b3_conv_measurable (d := p.d) (s := p.s) src hsrc
      exact (EuclideanSpace.proj i).continuous.measurable.comp hconv
    have heq : (fun z : ℝ × Euc p.d =>
        generatorW (r26t3_coeff R) (max z.1 0) f z.2) = fun z =>
        (r26t3_coeff R).ν * Laplacian.laplacian f z.2 +
          inner ℝ ((r26t3_coeff R).drift (max z.1 0) z.2) (gradient f z.2) -
          ∑ i : Fin p.d, (convGradConvW (rieszKernelGrad p.d (r26t3_coeff R).s)
            (fun y => ρclamp z.1 y *
              (Torus.matVec (r26t3_coeff R).M.transpose (gradient f y)) i) z.2) i := by
      funext z
      simp [generatorW, ρclamp, r26t3_coeff, WholeDyn.coeff, quadraticGradientDyn]
    rw [heq]
    exact hlocal.sub hnonlocal
  have hgenStrong : StronglyMeasurable (Function.uncurry (fun u =>
      generatorW (r26t3_coeff R) (max u 0) f)) := hgenJoint.stronglyMeasurable
  have hgenWeighted : ∀ u, IsR2WeightedTest (fp81s21_q p) (fp81s21_P p + 2)
      (generatorW (r26t3_coeff R) (max u 0) f) := by
    intro u
    exact (hb (max u 0) (le_max_right u 0) f (htestInput j)).1
  have hPEs : (p.d : ℝ) < 2 * (fp81s21_P p + 2) := by
    dsimp [fp81s21_P]
    have hd : 0 ≤ (p.d : ℝ) := Nat.cast_nonneg _
    linarith
  have henc := fp81s21_chart_encode_stronglyMeasurable_of_weighted
    Es hPEs (fun u => generatorW (r26t3_coeff R) (max u 0) f) hgenStrong hgenWeighted
  exact henc.measurable

#print axioms HRS.Fp81.S21.fp81s21_b3_basis_measurable

end HRS.Fp81.S21
