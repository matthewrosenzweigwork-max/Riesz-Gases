import HRS.MS.Fp81S21JointD2
import HRS.MS.Fp81S21B6iiEmp4
import HRS.MS.Fp81S21JointT2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

local instance fp81s21_jointD3_measurable (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_jointD3_borel (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- The finite-rank polynomial written in the empirical chart coordinates.
Its coordinates agree with the evaluations of `fp81s21_rawEtaAt` on the
finite-rank tests. -/
def fp81s21_chartPoly31 {d r : ℕ} {Pw : ℝ}
    (E : r26t6_WeightedChart d r Pw) (D : fp81s21_RankKernel d)
    (z : r26t6_Coeff) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, ∑ j, D.c i j *
    fp81s21_chartAction E z (D.u i) * fp81s21_chartAction E z (D.u j)

private theorem fp81s21_chartPoly31_continuous {d r : ℕ} {Pw : ℝ}
    (E : r26t6_WeightedChart d r Pw) (D : fp81s21_RankKernel d) :
    Continuous (fp81s21_chartPoly31 E D) := by
  have hcoord (i : Fin D.n) : Continuous
      (fun z : r26t6_Coeff => fp81s21_chartAction E z (D.u i)) := by
    change Continuous (fun z => inner ℝ z (E.encode (D.u i)))
    exact continuous_id.inner continuous_const
  unfold fp81s21_chartPoly31
  exact continuous_const.mul (continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun j _ =>
      (continuous_const.mul (hcoord i)).mul (hcoord j))

private def fp81s21_chartPoly31_bound {d r : ℕ} {Pw : ℝ}
    (_E : r26t6_WeightedChart d r Pw) (D : fp81s21_RankKernel d) : ℝ :=
  ∑ i, ∑ j, |D.c i j| *
    (weightedSobolevE r Pw (D.u i)).toReal *
    (weightedSobolevE r Pw (D.u j)).toReal

private theorem fp81s21_chartPoly31_bound_nonneg {d r : ℕ} {Pw : ℝ}
    (E : r26t6_WeightedChart d r Pw) (D : fp81s21_RankKernel d) :
    0 ≤ fp81s21_chartPoly31_bound E D := by
  unfold fp81s21_chartPoly31_bound
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  positivity

private theorem fp81s21_chartPoly31_growth {d r : ℕ} {Pw : ℝ}
    (E : r26t6_WeightedChart d r Pw) (D : fp81s21_RankKernel d)
    (hP : (d : ℝ) < 2 * Pw) (z : r26t6_Coeff) :
    |fp81s21_chartPoly31 E D z| ≤
      fp81s21_chartPoly31_bound E D * ‖z‖ ^ 2 := by
  let C : Fin D.n → ℝ := fun i =>
    (weightedSobolevE r Pw (D.u i)).toReal
  have hC (i : Fin D.n) : 0 ≤ C i := by
    dsimp [C]
    exact ENNReal.toReal_nonneg
  have ht (i : Fin D.n) : IsR2Test (D.u i) :=
    ⟨D.valid.smooth i, D.valid.compactSupport i⟩
  have hwt (i : Fin D.n) : IsR2WeightedTest r Pw (D.u i) :=
    weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP (ht i))
  have heval (i : Fin D.n) :
      |fp81s21_chartAction E z (D.u i)| ≤ ‖z‖ * C i := by
    exact fp81s21_chartAction_weighted_bound E z (D.u i) (hwt i)
  have hprod (i j : Fin D.n) :
      |fp81s21_chartAction E z (D.u i) * fp81s21_chartAction E z (D.u j)| ≤
        ‖z‖ ^ 2 * (C i * C j) := by
    rw [abs_mul]
    calc
      |fp81s21_chartAction E z (D.u i)| *
          |fp81s21_chartAction E z (D.u j)| ≤
          (‖z‖ * C i) * (‖z‖ * C j) :=
        mul_le_mul (heval i) (heval j) (abs_nonneg _) (by positivity)
      _ = ‖z‖ ^ 2 * (C i * C j) := by ring
  have hterm (i j : Fin D.n) :
      |D.c i j * (fp81s21_chartAction E z (D.u i) *
        fp81s21_chartAction E z (D.u j))| ≤
        |D.c i j| * (‖z‖ ^ 2 * (C i * C j)) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hprod i j) (abs_nonneg _)
  have hinner (i : Fin D.n) :
      |∑ j, D.c i j * (fp81s21_chartAction E z (D.u i) *
        fp81s21_chartAction E z (D.u j))| ≤
        ∑ j, |D.c i j| * (‖z‖ ^ 2 * (C i * C j)) := by
    calc
      _ ≤ ∑ j, |D.c i j * (fp81s21_chartAction E z (D.u i) *
          fp81s21_chartAction E z (D.u j))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun j _ => hterm i j
  have hsum :
      |∑ i, ∑ j, D.c i j * (fp81s21_chartAction E z (D.u i) *
        fp81s21_chartAction E z (D.u j))| ≤
        ∑ i, ∑ j, |D.c i j| * (‖z‖ ^ 2 * (C i * C j)) := by
    calc
      _ ≤ ∑ i, |∑ j, D.c i j *
          (fp81s21_chartAction E z (D.u i) * fp81s21_chartAction E z (D.u j))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ => hinner i
  have hfactor :
      (∑ i, ∑ j, |D.c i j| * (‖z‖ ^ 2 * (C i * C j))) =
        ‖z‖ ^ 2 * (∑ i, ∑ j, |D.c i j| * C i * C j) := by
    calc
      _ = ∑ i, ‖z‖ ^ 2 * (∑ j, |D.c i j| * C i * C j) := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = ∑ j, ‖z‖ ^ 2 * (|D.c i j| * C i * C j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = ‖z‖ ^ 2 * ∑ j, |D.c i j| * C i * C j := by
            rw [Finset.mul_sum]
      _ = ‖z‖ ^ 2 * (∑ i, ∑ j, |D.c i j| * C i * C j) := by
        rw [Finset.mul_sum]
  have hscaled :
      (1 / 2 : ℝ) *
        |∑ i, ∑ j, D.c i j * (fp81s21_chartAction E z (D.u i) *
          fp81s21_chartAction E z (D.u j))| ≤
        fp81s21_chartPoly31_bound E D * ‖z‖ ^ 2 := by
    calc
      _ ≤ (1 / 2 : ℝ) *
          (∑ i, ∑ j, |D.c i j| * (‖z‖ ^ 2 * (C i * C j))) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ ≤ ∑ i, ∑ j, |D.c i j| * (‖z‖ ^ 2 * (C i * C j)) := by
        have hnonneg : 0 ≤ ∑ i, ∑ j,
            |D.c i j| * (‖z‖ ^ 2 * (C i * C j)) :=
          Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
        nlinarith
      _ = ‖z‖ ^ 2 * (∑ i, ∑ j, |D.c i j| * C i * C j) := hfactor
      _ = fp81s21_chartPoly31_bound E D * ‖z‖ ^ 2 := by
        dsimp [fp81s21_chartPoly31_bound, C]
        ring
  have hsumEq :
      ∑ i, ∑ j, D.c i j * fp81s21_chartAction E z (D.u i) *
        fp81s21_chartAction E z (D.u j) =
      ∑ i, ∑ j, D.c i j *
        (fp81s21_chartAction E z (D.u i) * fp81s21_chartAction E z (D.u j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [fp81s21_chartPoly31, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ)), hsumEq]
  exact hscaled

private def fp81s21_rawPolynomialChartField31 {p r : ℕ} {Pw : ℝ}
    {Ω : Type*}
    (E : r26t6_WeightedChart p r Pw) (m : ℕ)
    (D : Fin m → fp81s21_RankKernel p)
    (q : ℝ → Ω → r26t6_Coeff) : ℝ → Ω → r26t6_Coeff :=
  fun u ω => ∑ j : Fin m,
    fp81s21_chartPoly31 E (D j) (q u ω) • fp81s21_coeffBasis j

private theorem fp81s21_particleRawEta_eval_test
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) {N : ℕ} (hN : 0 < N)
    (A : Particle R N) (u : ℝ) (hu : 0 ≤ u)
    (D : fp81s21_RankKernel p.d) (i : Fin D.n) (ω : A.Ω) :
    OscDual.eval (fp81s21_rawEtaAt R A u ω) (D.u i) =
      fp81s21_particleEmpField R N A u ω (D.u i) := by
  let μ : Measure (Euc p.d) := r26t3_mu R u
  have hρ : HRS.Whole.IsProbDensity (R.ρ u) :=
    ((r26t3_reference_data p δ hδ hδh R).2.2.1 u hu).1
  letI : IsProbabilityMeasure μ := HRS.Whole.U1.u1_isProb hρ
  haveI : IsProbabilityMeasure (Whole.empirical (d := p.d)
      (A.X u.toNNReal ω)) :=
    Whole.empirical_isProbabilityMeasure hN _
  have hm : (p.d : ℝ) < (wholeSpaceIndex p.d : ℝ) := by
    exact_mod_cast (show p.d < wholeSpaceIndex p.d by
      dsimp [wholeSpaceIndex]
      omega)
  let fS : SchwartzMap (Euc p.d) ℝ :=
    (D.valid.compactSupport i).toSchwartzMap (D.valid.smooth i)
  have hEval := OscDual.eval_ofMeasureDiff hm
    (Whole.empirical (d := p.d) (A.X u.toNNReal ω)) μ fS
  have hFun : (fS : Euc p.d → ℝ) = D.u i := by
    funext x
    simp only [fS, HasCompactSupport.toSchwartzMap_toFun]
  dsimp [fp81s21_rawEtaAt, μ, etaB, flucB]
  rw [OscDual.eval_smul]
  rw [show OscDual.eval
      (OscDual.ofMeasureDiff (wholeSpaceIndex p.d : ℝ)
        (Whole.empirical (d := p.d) (A.X u.toNNReal ω)) (r26t3_mu R u)) (D.u i) =
      ∫ x, D.u i x ∂(Whole.empirical (d := p.d) (A.X u.toNNReal ω)) -
        ∫ x, D.u i x ∂(r26t3_mu R u) by
        simpa [hFun] using hEval]
  simp [fp81s21_particleEmpField, HRS.Whole.r2EmpDistr,
    HRS.Whole.r2EmpFluct, Whole.pair, Real.toNNReal_of_nonneg hu]

private theorem fp81s21_polyAt_constant_eval31 {d : ℕ}
    (D : fp81s21_RankKernel d) (η : OscDual d (wholeSpaceIndex d : ℝ)) :
    fp81s21_polyAtD D η =
      (1 / 2 : ℝ) * ∑ i, ∑ j, D.c i j *
        (OscDual.eval η (D.u i) * OscDual.eval η (D.u j)) := by
  simp [fp81s21_polyAtD, fp81s21_constantEtaPath, fp81s21_quadPoly,
    OscPath.at']
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem fp81s21_polyAt_chart_eq_raw
    {d r : ℕ} {Pw : ℝ} (E : r26t6_WeightedChart d r Pw)
    (D : fp81s21_RankKernel d) (z : r26t6_Coeff)
    (η : OscDual d (wholeSpaceIndex d : ℝ))
    (hcoord : ∀ i : Fin D.n,
      fp81s21_chartAction E z (D.u i) = OscDual.eval η (D.u i)) :
    fp81s21_chartPoly31 E D z = fp81s21_polyAtD D η := by
  rw [fp81s21_chartPoly31, fp81s21_polyAt_constant_eval31]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hcoord i, hcoord j]
  ring

private theorem fp81s21_rawPolynomialChartField31_measurable
    {p r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart p r Pw) (m : ℕ)
    (D : Fin m → fp81s21_RankKernel p)
    (q : ℝ → Ω → r26t6_Coeff)
    (hq : Measurable (Function.uncurry q)) :
    Measurable (Function.uncurry
      (fp81s21_rawPolynomialChartField31 E m D q)) := by
  change Measurable (fun z : ℝ × Ω => ∑ j : Fin m,
    fp81s21_chartPoly31 E (D j) (q z.1 z.2) • fp81s21_coeffBasis j)
  exact Finset.measurable_sum _ fun j _ =>
    ((fp81s21_chartPoly31_continuous E (D j)).measurable.comp hq).smul
      measurable_const

private def fp81s21_rawPolynomialChartFamilyBound31 {p r : ℕ} {Pw : ℝ}
    (E : r26t6_WeightedChart p r Pw) (m : ℕ)
    (D : Fin m → fp81s21_RankKernel p) : ℝ :=
  ∑ j : Fin m, fp81s21_chartPoly31_bound E (D j)

private theorem fp81s21_rawPolynomialChartField31_growth
    {p r : ℕ} {Pw : ℝ} {Ω : Type*}
    (E : r26t6_WeightedChart p r Pw)
    (m : ℕ) (D : Fin m → fp81s21_RankKernel p)
    (q : ℝ → Ω → r26t6_Coeff) (hP : (p : ℝ) < 2 * Pw)
    (u : ℝ) (ω : Ω) :
    ‖fp81s21_rawPolynomialChartField31 E m D q u ω‖ ≤
      fp81s21_rawPolynomialChartFamilyBound31 E m D * ‖q u ω‖ ^ 2 := by
  change ‖∑ j : Fin m,
      fp81s21_chartPoly31 E (D j) (q u ω) • fp81s21_coeffBasis j‖ ≤ _
  calc
    _ ≤ ∑ j : Fin m,
        ‖fp81s21_chartPoly31 E (D j) (q u ω) • fp81s21_coeffBasis j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin m,
        fp81s21_chartPoly31_bound E (D j) * ‖q u ω‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul, fp81s21_coeffBasis.orthonormal.norm_eq_one,
        Real.norm_eq_abs]
      simpa using fp81s21_chartPoly31_growth E (D j) hP (q u ω)
    _ = fp81s21_rawPolynomialChartFamilyBound31 E m D * ‖q u ω‖ ^ 2 := by
      simp [fp81s21_rawPolynomialChartFamilyBound31, Finset.sum_mul]

private theorem fp81s21_particleRawPolynomialChartField31_ae
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (m : ℕ) (D : Fin m → fp81s21_RankKernel p.d)
    (q : ℝ → A.Ω → r26t6_Coeff)
    (hcommon : ∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u →
      ∀ f : Euc p.d → ℝ, IsR2Test f →
        fp81s21_chartAction Es (q u ω) f =
          fp81s21_particleEmpField R N A u ω f) :
    ∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u →
      fp81s21_rawPolynomialChartField31 Es m D q u ω =
        ∑ j : Fin m,
          fp81s21_polyAtD (D j) (fp81s21_rawEtaAt R A u ω) •
            fp81s21_coeffBasis j := by
  filter_upwards [hcommon] with ω hω
  intro u hu
  change ∑ j : Fin m,
      fp81s21_chartPoly31 Es (D j) (q u ω) • fp81s21_coeffBasis j = _
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply fp81s21_polyAt_chart_eq_raw
  intro i
  rw [hω u hu ((D j).u i) (⟨(D j).valid.smooth i,
    (D j).valid.compactSupport i⟩)]
  exact (fp81s21_particleRawEta_eval_test p hδ hδh R (by omega) A u hu
    (D j) i ω).symm

private theorem fp81s21_particle_quadraticGrowth_TimeL2Rep
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q r : ℝ → Ω → r26t6_Coeff) (M6 K a H : ℝ)
    (hM6 : 0 ≤ M6) (hK : 0 ≤ K) (ha : 0 ≤ a) (hH : 0 < H)
    (hq : Measurable (Function.uncurry q))
    (hr : Measurable (Function.uncurry r))
    (hsix : fp81s21_Six P q M6)
    (hgrowth : ∀ u ω, ‖r u ω‖ ≤ K * ‖q u ω‖ ^ 2) :
    ∃ Mr : ℝ, ∃ V : Ω → Lp r26t6_Coeff 2
        (volume.restrict (Set.Icc (0 : ℝ) H)),
      fp81s21_TimeL2Rep P r Mr a H V := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let g : ℝ × Ω → r26t6_Coeff := fun z => r (a + z.1) z.2
  have hg : Measurable g := hr.comp
    ((measurable_const.add measurable_fst).prodMk measurable_snd)
  let B : ℝ := K ^ 2 * (1 + M6)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsec : ∀ᵐ t ∂dt,
      MemLp (fun ω => g (t, ω)) 2 P ∧
        (∫ ω, ‖g (t, ω)‖ ^ 2 ∂P) ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hu : 0 ≤ a + t := by linarith [ha, ht.1]
    obtain ⟨_, hq6int, hq6bound⟩ := hsix (a + t) hu
    have hq4point : ∀ ω, ‖q (a + t) ω‖ ^ 4 ≤
        1 + ‖q (a + t) ω‖ ^ 6 := by
      intro ω
      let x := ‖q (a + t) ω‖
      by_cases hx : x ≤ 1
      · have hx0 : 0 ≤ x := norm_nonneg _
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 2 - 1)]
      · have hx0 : 0 ≤ x := norm_nonneg _
        have hx1 : 1 ≤ x := le_of_not_ge hx
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 2 - 1)]
    have hq4meas : AEStronglyMeasurable
        (fun ω => ‖q (a + t) ω‖ ^ 4) P :=
      ((hq.comp (measurable_const.prodMk measurable_id)).norm.pow_const 4).aestronglyMeasurable
    have hq4int : Integrable (fun ω => ‖q (a + t) ω‖ ^ 4) P := by
      apply Integrable.mono' ((integrable_const (1 : ℝ)).add hq6int) hq4meas
      filter_upwards with ω
      simpa [Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ ‖q (a + t) ω‖ ^ 4),
        abs_of_nonneg (by positivity : 0 ≤ 1 + ‖q (a + t) ω‖ ^ 6)] using
          hq4point ω
    have hq4bound : (∫ ω, ‖q (a + t) ω‖ ^ 4 ∂P) ≤ 1 + M6 := by
      calc
        _ ≤ ∫ ω, (1 + ‖q (a + t) ω‖ ^ 6) ∂P :=
          integral_mono_ae hq4int ((integrable_const (1 : ℝ)).add hq6int)
            (ae_of_all P hq4point)
        _ = 1 + ∫ ω, ‖q (a + t) ω‖ ^ 6 ∂P := by
          rw [integral_add (integrable_const (1 : ℝ)) hq6int]
          simp [IsProbabilityMeasure.measure_univ]
        _ ≤ 1 + M6 := by linarith
    have hgrowthSq : ∀ ω,
        ‖g (t, ω)‖ ^ 2 ≤ K ^ 2 * ‖q (a + t) ω‖ ^ 4 := by
      intro ω
      have hb : ‖g (t, ω)‖ ≤ K * ‖q (a + t) ω‖ ^ 2 := by
        simpa [g] using hgrowth (a + t) ω
      calc
        ‖g (t, ω)‖ ^ 2 ≤ (K * ‖q (a + t) ω‖ ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg (g (t, ω))) hb 2
        _ = K ^ 2 * ‖q (a + t) ω‖ ^ 4 := by ring
    have htarget : Integrable
        (fun ω => K ^ 2 * ‖q (a + t) ω‖ ^ 4) P :=
      hq4int.const_mul (K ^ 2)
    have hg2 : Integrable (fun ω => ‖g (t, ω)‖ ^ 2) P := by
      apply Integrable.mono' htarget
        ((hg.comp (measurable_prodMk_left (x := t))).norm.pow_const 2).aestronglyMeasurable
      filter_upwards with ω
      simpa [Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ ‖g (t, ω)‖ ^ 2),
        abs_of_nonneg (by positivity : 0 ≤ K ^ 2 * ‖q (a + t) ω‖ ^ 4)] using
          hgrowthSq ω
    have hmem : MemLp (fun ω => g (t, ω)) 2 P :=
      (memLp_two_iff_integrable_sq_norm
        (hg.comp (measurable_prodMk_left (x := t))).aestronglyMeasurable).2 hg2
    have hbound : (∫ ω, ‖g (t, ω)‖ ^ 2 ∂P) ≤ B := by
      calc
        _ ≤ ∫ ω, K ^ 2 * ‖q (a + t) ω‖ ^ 4 ∂P :=
          integral_mono_ae hg2 htarget (ae_of_all P hgrowthSq)
        _ = K ^ 2 * ∫ ω, ‖q (a + t) ω‖ ^ 4 ∂P := integral_const_mul _ _
        _ ≤ B := by dsimp [B]; exact mul_le_mul_of_nonneg_left hq4bound (sq_nonneg K)
    exact ⟨hmem, hbound⟩
  have hprod := fp81s21_memLp_prod_of_section_bound dt P g hg B hsec
  obtain ⟨V, hVm, hVL, hVeq, hVin⟩ := fp81s21_time_section_exists P H g hg hprod.1
  have hdt : (dt Set.univ).toReal = H := by
    simp [dt, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (le_of_lt hH)]
  have hbound : (∫ ω, ‖V ω‖ ^ 2 ∂P) ≤ H * B := by
    rw [hVin]
    calc
      _ ≤ (dt Set.univ).toReal * B := hprod.2
      _ = H * B := by rw [hdt]
  have hsections : ∀ᵐ ω ∂P,
      MemLp (fun t => g (t, ω)) 2 dt := by
    have hprodint : Integrable (fun z : ℝ × Ω => ‖g z‖ ^ 2) (dt.prod P) :=
      (memLp_two_iff_integrable_sq_norm hprod.1.aestronglyMeasurable).1 hprod.1
    filter_upwards [hprodint.prod_left_ae] with ω hω
    exact (memLp_two_iff_integrable_sq_norm
      (hg.comp (measurable_prodMk_right (y := ω))).aestronglyMeasurable).2 hω
  have hTime : fp81s21_TimeL2Rep P r B a H V := by
    refine ⟨hVm, hVL, hbound, ?_⟩
    filter_upwards [hsections, hVeq] with ω hω hEq
    exact ⟨hω, hEq⟩
  exact ⟨B, V, hTime⟩

/-- A common-time empirical chart representative gives a jointly measurable
raw finite-rank polynomial field and a genuine time-L² class. The bound is
uniform in particle count, realization, and the starting time; the finite-rank
data and the horizon are fixed first. -/
theorem fp81s21_particle_rawPolynomial_time_section_of_common
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (m : ℕ) (D : Fin m → fp81s21_RankKernel p.d)
    (q : ℝ → A.Ω → r26t6_Coeff) (M6 : ℝ)
    (hM6 : 0 ≤ M6)
    (hq : Measurable (Function.uncurry q))
    (hsix : fp81s21_Six A.P q M6)
    (hcommon : ∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u →
      ∀ f : Euc p.d → ℝ, IsR2Test f →
        fp81s21_chartAction Es (q u ω) f =
          fp81s21_particleEmpField R N A u ω f)
    (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H) :
    ∃ r : ℝ → A.Ω → r26t6_Coeff,
      Measurable (Function.uncurry r) ∧
      (∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u →
        r u ω = ∑ j : Fin m,
          fp81s21_polyAtD (D j) (fp81s21_rawEtaAt R A u ω) •
            fp81s21_coeffBasis j) ∧
      ∃ Mr : ℝ, ∃ V : A.Ω → Lp r26t6_Coeff 2
          (volume.restrict (Set.Icc (0 : ℝ) H)),
        fp81s21_TimeL2Rep A.P r Mr a H V := by
  let r : ℝ → A.Ω → r26t6_Coeff :=
    fp81s21_rawPolynomialChartField31 Es m D q
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 4) := by nlinarith [p.hd]
  let K : ℝ := fp81s21_rawPolynomialChartFamilyBound31 Es m D
  have hK : 0 ≤ K := by
    dsimp [K, fp81s21_rawPolynomialChartFamilyBound31]
    exact Finset.sum_nonneg fun j _ => fp81s21_chartPoly31_bound_nonneg Es (D j)
  have hr : Measurable (Function.uncurry r) := by
    simpa [r] using fp81s21_rawPolynomialChartField31_measurable Es m D q hq
  have hraw := fp81s21_particleRawPolynomialChartField31_ae
    p hδ hδh R hN A Es m D q hcommon
  obtain ⟨Mr, V, hTime⟩ := fp81s21_particle_quadraticGrowth_TimeL2Rep
    A.P q r M6 K a H hM6 hK ha hH hq hr hsix
    (fun u ω => fp81s21_rawPolynomialChartField31_growth
      Es m D q hP u ω)
  exact ⟨r, hr, hraw, Mr, V, hTime⟩

#print axioms fp81s21_chartPoly31_continuous
#print axioms fp81s21_particleRawEta_eval_test
#print axioms fp81s21_particle_rawPolynomial_time_section_of_common

end HRS.Fp81.S21
end
