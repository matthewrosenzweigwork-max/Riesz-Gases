import HRS.MS.Fp81S21RankKernel
import HRS.MS.Fp81S21QuadPoly
import HRS.MS.R2ChaosAux17
import HRS.MS.R2ChaosAux19

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal

namespace HRS.Fp81.S21

open HRS.Whole HRS.MS.R26T3

/-- The raw empirical fluctuation dual at a single physical time. This is the
same field as `fp81s21_particleEta` in the window modules, expressed directly
from its compiled definition. -/
def fp81s21_rawEtaAt {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N) (u : ℝ) (ω : A.Ω) :
    OscDual p.d (wholeSpaceIndex p.d : ℝ) :=
  etaB (wholeSpaceIndex p.d : ℝ) (A.X u.toNNReal ω) (r26t3_mu R u)

/-- Embed one raw fluctuation into a constant path so the actual `quadPoly`
definition can be evaluated at time zero. -/
def fp81s21_constantEtaPath {d : ℕ}
    (η : OscDual d (wholeSpaceIndex d : ℝ)) :
    OscPath d (wholeSpaceIndex d : ℝ) 1 :=
  ⟨fun _ => η, continuous_const⟩

/-- The uncentered finite-rank polynomial of a raw fluctuation. -/
def fp81s21_polyAtD {d : ℕ} (D : fp81s21_RankKernel d)
    (η : OscDual d (wholeSpaceIndex d : ℝ)) : ℝ :=
  fp81s21_quadPoly D.c D.u (fp81s21_constantEtaPath η)
    ⟨0, ⟨le_rfl, by norm_num⟩⟩

private theorem fp81s21_polyAt_constant_eval {d : ℕ}
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

private theorem fp81s21_rawEta_eval
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) {N : ℕ} (hN : 0 < N)
    (A : Particle R N) (u : ℝ) (hu : 0 ≤ u)
    (D : fp81s21_RankKernel p.d) (i : Fin D.n) (ω : A.Ω) :
    OscDual.eval (fp81s21_rawEtaAt R A u ω) (D.u i) =
      r2EmpFluct (r26t3_mu R u) (D.u i) A.X ω u := by
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
  simp [r2EmpFluct, Whole.pair, Real.toNNReal_of_nonneg hu]

private theorem fp81s21_center_quad_sum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m : ℕ} (c : Fin m → Fin m → ℝ)
    (z : Fin m → Ω → ℝ)
    (hz : ∀ i j, Integrable (fun ω => z i ω * z j ω) P)
    (ω : Ω) :
    fp81s21_center P (fun ω' => (1 / 2 : ℝ) *
        ∑ i, ∑ j, c i j * (z i ω' * z j ω')) ω =
      (1 / 2 : ℝ) * ∑ i, ∑ j, c i j *
        (z i ω * z j ω - ∫ ω', z i ω' * z j ω' ∂P) := by
  have hIntegral :
      ∫ ω', (1 / 2 : ℝ) * ∑ i, ∑ j, c i j * (z i ω' * z j ω') ∂P =
        (1 / 2 : ℝ) * ∑ i, ∑ j, c i j *
          ∫ ω', z i ω' * z j ω' ∂P := by
    rw [integral_const_mul]
    rw [integral_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => (hz i j).const_mul (c i j)))]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ (fun j _ => (hz i j).const_mul (c i j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  have hAlgebra :
      (1 / 2 : ℝ) * ∑ i, ∑ j, c i j * (z i ω * z j ω) -
        (1 / 2 : ℝ) * ∑ i, ∑ j, c i j *
          ∫ ω', z i ω' * z j ω' ∂P =
        (1 / 2 : ℝ) * ∑ i, ∑ j, c i j *
          (z i ω * z j ω - ∫ ω', z i ω' * z j ω' ∂P) := by
    have hInner (i : Fin m) :
        ∑ j, c i j * (z i ω * z j ω - ∫ ω', z i ω' * z j ω' ∂P) =
          (∑ j, c i j * (z i ω * z j ω)) -
            ∑ j, c i j * ∫ ω', z i ω' * z j ω' ∂P := by
      calc
        ∑ j, c i j * (z i ω * z j ω - ∫ ω', z i ω' * z j ω' ∂P) =
            ∑ j, (c i j * (z i ω * z j ω) -
              c i j * ∫ ω', z i ω' * z j ω' ∂P) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
        _ = _ := by
          simpa using (Finset.sum_sub_distrib (s := Finset.univ)
            (f := fun j : Fin m => c i j * (z i ω * z j ω))
            (g := fun j : Fin m => c i j * ∫ ω', z i ω' * z j ω' ∂P))
    have hOuter :
        ∑ i, ∑ j, c i j * (z i ω * z j ω - ∫ ω', z i ω' * z j ω' ∂P) =
          (∑ i, ∑ j, c i j * (z i ω * z j ω)) -
            ∑ i, ∑ j, c i j * ∫ ω', z i ω' * z j ω' ∂P := by
      calc
        ∑ i, ∑ j, c i j * (z i ω * z j ω - ∫ ω', z i ω' * z j ω' ∂P) =
            ∑ i, ((∑ j, c i j * (z i ω * z j ω)) -
              ∑ j, c i j * ∫ ω', z i ω' * z j ω' ∂P) := by
                apply Finset.sum_congr rfl
                intro i hi
                exact hInner i
        _ = _ := by
          simpa using (Finset.sum_sub_distrib (s := Finset.univ)
            (f := fun i : Fin m => ∑ j, c i j * (z i ω * z j ω))
            (g := fun i : Fin m => ∑ j, c i j * ∫ ω', z i ω' * z j ω' ∂P))
    rw [hOuter]
    ring
  unfold fp81s21_center
  rw [hIntegral]
  exact hAlgebra

/-- The exact finite-rank particle identity. The polynomial is the raw
quadratic polynomial of the empirical fluctuation; centering is performed
under the actual law `A.P`. The diagonal correction is also centered under
that law and has the deleted-diagonal coefficient `1/2`. -/
theorem fp81s21_particle_finiteRank_identity
    (p : Parameters) {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) {N : ℕ} (hN : 2 ≤ N)
    (A : Particle R N) (u : ℝ) (hu : 0 ≤ u)
    (D : fp81s21_RankKernel p.d) (ω : A.Ω) :
    fp81s21_particleQuad A u D.kernel ω =
      fp81s21_center A.P
        (fun ω' => fp81s21_polyAtD D (fp81s21_rawEtaAt R A u ω')) ω -
      (1 / 2 : ℝ) • fp81s21_center A.P
        (fun ω' => Whole.pair (Whole.empirical (A.X u.toNNReal ω'))
          (fun x => D.kernel x x)) ω := by
  let μ : Measure (Euc p.d) := r26t3_mu R u
  let X : ℝ≥0 → A.Ω → EucConfig p.d N := fun _ ω' => A.X u.toNNReal ω'
  have hρ : HRS.Whole.IsProbDensity (R.ρ u) :=
    ((r26t3_reference_data p δ hδ hδh R).2.2.1 u hu).1
  letI : IsProbabilityMeasure μ := HRS.Whole.U1.u1_isProb hρ
  letI : IsProbabilityMeasure A.P := inferInstance
  have hNpos : 0 < N := by omega
  have hXtime : Measurable (fun q : ℝ≥0 × A.Ω => X q.1 q.2) := by
    have hX : Measurable (A.X u.toNNReal) :=
      (A.strong (u + 1)).adapted u.toNNReal
    exact hX.comp measurable_snd
  have huTest : ∀ i, IsR2Test (D.u i) := fun i =>
    ⟨D.valid.smooth i, D.valid.compactSupport i⟩
  have hQuad := HRS.MS.R2Chaos.s94_quad_finiteRank
    (μ := μ) huTest D.valid.symm hNpos A.P X hXtime 0 ω
  let z : Fin D.n → A.Ω → ℝ := fun i ω' =>
    r2EmpFluct μ (D.u i) X ω' 0
  have hmeas : ∀ i, Measurable (z i) := by
    intro i
    have hz := HRS.MS.R2Chaos.s94_empFluct_section_measurable
      (μ := μ) (huTest i) X hXtime 0
    simpa [z, X] using hz
  have hbound : ∀ i ω', |z i ω'| ≤ Real.sqrt N *
      (2 * (Classical.choose (HRS.MS.R2Chaos.s94_test_bounded (huTest i)))) := by
    intro i ω'
    exact HRS.MS.R2Chaos.s94_abs_empFluct_le
      (μ := μ) hNpos X (Classical.choose_spec
        (HRS.MS.R2Chaos.s94_test_bounded (huTest i))) ω' 0
  have hzint : ∀ i j, Integrable (fun ω' => z i ω' * z j ω') A.P := by
    intro i j
    let Ci : ℝ := Classical.choose (HRS.MS.R2Chaos.s94_test_bounded (huTest i))
    let Cj : ℝ := Classical.choose (HRS.MS.R2Chaos.s94_test_bounded (huTest j))
    have hCi := Classical.choose_spec (HRS.MS.R2Chaos.s94_test_bounded (huTest i))
    have hCj := Classical.choose_spec (HRS.MS.R2Chaos.s94_test_bounded (huTest j))
    refine Integrable.of_bound ((hmeas i).mul (hmeas j)).aestronglyMeasurable
      (Real.sqrt N * (2 * Ci) * (Real.sqrt N * (2 * Cj))) (ae_of_all _ fun ω' => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hbound i ω') (hbound j ω') (abs_nonneg _)
      ((abs_nonneg (z i ω')).trans (hbound i ω'))
  have hCenterPoly := fp81s21_center_quad_sum D.c z hzint ω
  have hpoly : ∀ ω', fp81s21_polyAtD D (fp81s21_rawEtaAt R A u ω') =
      (1 / 2 : ℝ) * ∑ i, ∑ j, D.c i j * (z i ω' * z j ω') := by
    intro ω'
    rw [fp81s21_polyAt_constant_eval]
    apply congrArg (fun s : ℝ => (1 / 2 : ℝ) * s)
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [fp81s21_rawEta_eval hδ hδh R (by omega) A u hu D i ω',
      fp81s21_rawEta_eval hδ hδh R (by omega) A u hu D j ω']
    simp [z, X, μ, r2EmpFluct, Real.toNNReal_of_nonneg hu]
  have hpolyCenter : fp81s21_center A.P
      (fun ω' => fp81s21_polyAtD D (fp81s21_rawEtaAt R A u ω')) ω =
      (1 / 2 : ℝ) * ∑ i, ∑ j, D.c i j *
        (z i ω * z j ω - ∫ ω', z i ω' * z j ω' ∂A.P) := by
    rw [show (fun ω' => fp81s21_polyAtD D (fp81s21_rawEtaAt R A u ω')) =
      (fun ω' => (1 / 2 : ℝ) * ∑ i, ∑ j, D.c i j * (z i ω' * z j ω')) from funext hpoly]
    exact hCenterPoly
  have hdiag : ∀ ω', Whole.pair (Whole.empirical (A.X u.toNNReal ω'))
      (fun x => D.kernel x x) =
      Whole.pair (Whole.empirical (X 0 ω'))
        (fun x => ∑ i, ∑ j, D.c i j * D.u i x * D.u j x) := by
    intro ω'
    simp [X, fp81s21_RankKernel.kernel, Whole.r2FiniteRankKernel]
  have hQuad' : fp81s21_particleQuad A u D.kernel ω =
      (1 / 2 : ℝ) * ∑ i, ∑ j, D.c i j *
          (z i ω * z j ω - ∫ ω', z i ω' * z j ω' ∂A.P) -
        (1 / 2 : ℝ) *
          (Whole.pair (Whole.empirical (X 0 ω))
              (fun x => ∑ i, ∑ j, D.c i j * D.u i x * D.u j x) -
            ∫ ω', Whole.pair (Whole.empirical (X 0 ω'))
              (fun x => ∑ i, ∑ j, D.c i j * D.u i x * D.u j x) ∂A.P) := by
    have hL : r2QuadFluct μ (fun _ => D.kernel) A.P X 0 ω =
        fp81s21_particleQuad A u D.kernel ω := by
      simp [r2QuadFluct, fp81s21_particleQuad, fp81s21_center, X, μ,
        integral_const_mul]
      ring
    rw [← hL]
    exact hQuad
  rw [hpolyCenter, hQuad']
  simp only [fp81s21_center, hdiag, smul_eq_mul]

#print axioms HRS.Fp81.S21.fp81s21_particle_finiteRank_identity

end HRS.Fp81.S21
