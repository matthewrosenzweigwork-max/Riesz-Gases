import HRS.MS.Fp81S21WeightedGenUncond
import HRS.MS.ProClosureS111NoiseLinear
import HRS.MS.Fp81S21WeightedGenAssembly
import HRS.MS.Fp81S21WeightedGenPrimal2
import HRS.MS.Fp81S21WeightedGenMeas2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

private theorem fp81s21_b3_weightedSobolevE_sub_le_add
    {d r : ℕ} {P : ℝ} {f g : Euc d → ℝ}
    (hf : IsR2WeightedTest r P f) (hg : IsR2WeightedTest r P g) :
    weightedSobolevE r P (f - g) ≤
      weightedSobolevE r P f + weightedSobolevE r P g := by
  let F : weightedTestSubmodule d r P := ⟨f, (weightedTestSubmodule_iff).2 hf⟩
  let G : weightedTestSubmodule d r P := ⟨g, (weightedTestSubmodule_iff).2 hg⟩
  let H : weightedTestSubmodule d r P := F - G
  have hmap : weightedJetMap d r P H =
      weightedJetMap d r P F - weightedJetMap d r P G := by
    change weightedJetMap d r P (F - G) = _
    exact map_sub (weightedJetMap d r P) F G
  have hnormF : ‖weightedJetMap d r P F‖ =
      (weightedSobolevE r P f).toReal := by
    simpa [F] using weightedJetMap_norm F
  have hnormG : ‖weightedJetMap d r P G‖ =
      (weightedSobolevE r P g).toReal := by
    simpa [G] using weightedJetMap_norm G
  have hnormH : ‖weightedJetMap d r P H‖ =
      (weightedSobolevE r P (f - g)).toReal := by
    simpa [H, F, G] using weightedJetMap_norm H
  have hreal : (weightedSobolevE r P (f - g)).toReal ≤
      (weightedSobolevE r P f).toReal + (weightedSobolevE r P g).toReal := by
    calc
      _ = ‖weightedJetMap d r P H‖ := hnormH.symm
      _ = ‖weightedJetMap d r P F - weightedJetMap d r P G‖ := by rw [hmap]
      _ ≤ ‖weightedJetMap d r P F‖ + ‖weightedJetMap d r P G‖ := norm_sub_le _ _
      _ = _ := by rw [hnormF, hnormG]
  have hfiniteH : weightedSobolevE r P (f - g) < ⊤ := by
    have htest : IsR2WeightedTest r P (f - g) := weightedTestSubmodule_iff.1 H.property
    exact htest.2
  calc
    weightedSobolevE r P (f - g) =
        ENNReal.ofReal (weightedSobolevE r P (f - g)).toReal :=
      (ENNReal.ofReal_toReal hfiniteH.ne).symm
    _ ≤ ENNReal.ofReal ((weightedSobolevE r P f).toReal +
          (weightedSobolevE r P g).toReal) := ENNReal.ofReal_le_ofReal hreal
    _ = weightedSobolevE r P f + weightedSobolevE r P g := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hf.2.ne, ENNReal.ofReal_toReal hg.2.ne]

private theorem fp81s21_b3_source_add_smul
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) {u a : ℝ}
    {f g : Euc p.d → ℝ} (hfc : ContDiff ℝ 2 f) (hgc : ContDiff ℝ 2 g)
    (j : Fin p.d) :
    fp81s21_b3_source R u (f + a • g) j =
      fun y => fp81s21_b3_source R u f j y + a * fp81s21_b3_source R u g j y := by
  funext y
  have hgrad : gradient (f + a • g) y = gradient f y + a • gradient g y := by
    change gradient (fun z => f z + a * g z) y = _
    exact HRS.MS.ProClosureS111.gradient_add_const_mul
      ((hfc.differentiable (by norm_num)) y)
      ((hgc.differentiable (by norm_num)) y) a
  simp only [fp81s21_b3_source]
  rw [hgrad]
  simp [Torus.matVec, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private theorem fp81s21_b3_local_add_smul
    {p : Parameters} (b : Euc p.d → Euc p.d) (a : ℝ)
    {f g : Euc p.d → ℝ} (hfc : ContDiff ℝ 2 f) (hgc : ContDiff ℝ 2 g) :
    fp81s21_b3_local p b (f + a • g) =
      fun x => fp81s21_b3_local p b f x + a * fp81s21_b3_local p b g x := by
  funext x
  have hgrad : gradient (f + a • g) x = gradient f x + a • gradient g x := by
    change gradient (fun z => f z + a * g z) x = _
    exact HRS.MS.ProClosureS111.gradient_add_const_mul
      ((hfc.differentiable (by norm_num)) x)
      ((hgc.differentiable (by norm_num)) x) a
  have hlap : Laplacian.laplacian (f + a • g) x =
      Laplacian.laplacian f x + a * Laplacian.laplacian g x := by
    calc
      Laplacian.laplacian (f + a • g) x =
          Laplacian.laplacian f x + Laplacian.laplacian (a • g) x :=
        ContDiffAt.laplacian_add (hfc.contDiffAt (x := x))
          ((hgc.contDiffAt (x := x)).const_smul a)
      _ = Laplacian.laplacian f x + a * Laplacian.laplacian g x := by
        rw [InnerProductSpace.laplacian_smul a (hgc.contDiffAt (x := x))]
        simp [smul_eq_mul]
  simp only [fp81s21_b3_local]
  rw [hlap, hgrad]
  simp only [inner_add_right, inner_smul_right]
  ring

private def fp81s21_b3_nonlocal_from_source
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (u : ℝ) (f : Euc p.d → ℝ) : Euc p.d → ℝ :=
  fun x => ∑ j : Fin p.d,
    (convGradConvW (rieszKernelGrad p.d p.s)
      (fp81s21_b3_source R u f j) x) j

private theorem fp81s21_b3_g4N_eq_nonlocal_from_source
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (u : ℝ) (f : Euc p.d → ℝ) :
    fp81s21_g4N p R u f = fp81s21_b3_nonlocal_from_source R u f := by
  rfl

private theorem fp81s21_b3_nonlocal_from_source_add_smul
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) {u a : ℝ}
    {f g : Euc p.d → ℝ} (hfc : ContDiff ℝ 2 f) (hgc : ContDiff ℝ 2 g)
    (hIf : ∀ j : Fin p.d, ∀ x : Euc p.d,
      Integrable (HRS.MS.Ul.ultInt p.s (fp81s21_b3_source R u f j) x) volume)
    (hIg : ∀ j : Fin p.d, ∀ x : Euc p.d,
      Integrable (HRS.MS.Ul.ultInt p.s (fp81s21_b3_source R u g j) x) volume) :
    fp81s21_b3_nonlocal_from_source R u (f + a • g) =
      fun x => fp81s21_b3_nonlocal_from_source R u f x +
        a * fp81s21_b3_nonlocal_from_source R u g x := by
  funext x
  unfold fp81s21_b3_nonlocal_from_source
  calc
    _ = ∑ j : Fin p.d,
        (a * (convGradConvW (rieszKernelGrad p.d p.s)
          (fp81s21_b3_source R u g j) x) j +
         (convGradConvW (rieszKernelGrad p.d p.s)
          (fp81s21_b3_source R u f j) x) j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [fp81s21_b3_source_add_smul R hfc hgc j]
            have hconv := HRS.MS.S104e.C.s104c2_conv_lin
              (s := p.s) (c := a)
              (h1 := fp81s21_b3_source R u g j)
              (h2 := fp81s21_b3_source R u f j)
              x (hIg j x) (hIf j x) j
            have hswap :
                (fun y => fp81s21_b3_source R u f j y +
                  a * fp81s21_b3_source R u g j y) =
                (fun y => a * fp81s21_b3_source R u g j y +
                  fp81s21_b3_source R u f j y) := by
              funext y
              ring
            rw [hswap]
            exact hconv
    _ = fp81s21_b3_nonlocal_from_source R u f x +
          a * fp81s21_b3_nonlocal_from_source R u g x := by
          dsimp [fp81s21_b3_nonlocal_from_source]
          rw [Finset.sum_add_distrib, Finset.mul_sum]
          ring

private theorem fp81s21_b3_generator_eq_local_sub_g4N
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (u : ℝ) (f : Euc p.d → ℝ) :
    generatorW (r26t3_coeff R) u f =
      fun x => fp81s21_b3_local p ((r26t3_coeff R).drift u) f x -
        fp81s21_g4N p R u f x := by
  funext x
  rfl

/-- Assemble the local estimate and U4's all-test nonlocal estimate without
importing the duplicate source declaration in `WeightedGenAssembly2`. -/
theorem fp81s21_b3_generator_from_nonlocal_contract
    (p : Parameters)
    (hNL : ∀ B c : ℝ, 0 ≤ B → 0 < c →
      fp81s21_b3_nonlocal_all_tests_contract p B c) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ δ, 0 < δ → δ ≤ (1 / 2 : ℝ) →
        ∀ R : Trajectory p δ, fp81s21_bound R A ∧ fp81s21_linear R := by
  obtain ⟨B, c, hB, hc, hData⟩ := fp81s21_b3_coefficients p
  obtain ⟨A', hA', hNLData⟩ := hNL B c hB hc
  obtain ⟨AL, hAL, hLocal⟩ := fp81s21_b3_local_estimate p B hB
  let A : ℝ := AL + A'
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro δ hδ hδhalf R
  have hD := hData δ hδ hδhalf R
  have hNLall := hNLData R hD
  refine ⟨?_, ?_⟩
  · intro u hu f hf
    have hDu := hD u hu
    have hloc := hLocal ((r26t3_coeff R).drift u) hDu.1 hDu.2.1 f hf
    have hnonlocal := hNLall u hu f hf
    have hP4 : fp81s21_P p + 2 = (p.d : ℝ) + 4 := by
      dsimp [fp81s21_P]
      ring
    have hlocTestRaw : IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4)
        (fp81s21_b3_local p ((r26t3_coeff R).drift u) f) := by
      have hsrc : IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 3)
          (fp81s21_b3_local p ((r26t3_coeff R).drift u) f) := hloc.1
      exact fp81s21_isR2WeightedTest_mono_weight (d := p.d)
        (r := 2 * p.d + 6) (P := (p.d : ℝ) + 3) (by linarith) hsrc
    have hlocTest : IsR2WeightedTest (fp81s21_q p) (fp81s21_P p + 2)
        (fp81s21_b3_local p ((r26t3_coeff R).drift u) f) := by
      rw [fp81s21_q, hP4]
      exact hlocTestRaw
    have hnlSrc : IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 2)
        (fp81s21_g4N p R u f) := by
      simpa [fp81s21_q, fp81s21_P] using hnonlocal.2.1
    have hnlTestRaw : IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4)
        (fp81s21_g4N p R u f) := by
      exact fp81s21_isR2WeightedTest_mono_weight (d := p.d)
        (r := 2 * p.d + 6) (P := (p.d : ℝ) + 2) (by linarith) hnlSrc
    have hnlTest : IsR2WeightedTest (fp81s21_q p) (fp81s21_P p + 2)
        (fp81s21_g4N p R u f) := by
      rw [fp81s21_q, hP4]
      exact hnlTestRaw
    have hgenEq := fp81s21_b3_generator_eq_local_sub_g4N R u f
    have hgenTest : fp81s21_Output p (generatorW (r26t3_coeff R) u f) := by
      rw [hgenEq]
      apply weightedTestSubmodule_iff.1
      have hLm : fp81s21_b3_local p ((r26t3_coeff R).drift u) f ∈
          weightedTestSubmodule p.d (fp81s21_q p) (fp81s21_P p + 2) :=
        weightedTestSubmodule_iff.2 hlocTest
      have hNm : fp81s21_g4N p R u f ∈
          weightedTestSubmodule p.d (fp81s21_q p) (fp81s21_P p + 2) :=
        weightedTestSubmodule_iff.2 hnlTest
      exact (weightedTestSubmodule p.d (fp81s21_q p)
        (fp81s21_P p + 2)).sub_mem hLm hNm
    have hlocBound : weightedSobolevE (fp81s21_q p) (fp81s21_P p + 2)
        (fp81s21_b3_local p ((r26t3_coeff R).drift u) f) ≤
          ENNReal.ofReal AL * fp81s21_Ein p f := by
      exact (fp81s21_weightedSobolevE_mono_weight (by dsimp [fp81s21_P]; linarith)
        (fp81s21_b3_local p ((r26t3_coeff R).drift u) f)).trans hloc.2
    have hnlBound : weightedSobolevE (fp81s21_q p) (fp81s21_P p + 2)
        (fp81s21_g4N p R u f) ≤
          ENNReal.ofReal A' * fp81s21_Ein p f := by
      exact (fp81s21_weightedSobolevE_mono_weight (by dsimp [fp81s21_P]; linarith)
        (fp81s21_g4N p R u f)).trans hnonlocal.2.2
    refine ⟨hgenTest, ?_⟩
    calc
      weightedSobolevE (fp81s21_q p) (fp81s21_P p + 2)
          (generatorW (r26t3_coeff R) u f) ≤
        weightedSobolevE (fp81s21_q p) (fp81s21_P p + 2)
          (fp81s21_b3_local p ((r26t3_coeff R).drift u) f) +
        weightedSobolevE (fp81s21_q p) (fp81s21_P p + 2)
          (fp81s21_g4N p R u f) := by
            rw [hgenEq]
            exact fp81s21_b3_weightedSobolevE_sub_le_add hlocTest hnlTest
      _ ≤ ENNReal.ofReal AL * fp81s21_Ein p f +
          ENNReal.ofReal A' * fp81s21_Ein p f := add_le_add hlocBound hnlBound
      _ = ENNReal.ofReal A * fp81s21_Ein p f := by
          rw [← add_mul, ← ENNReal.ofReal_add hAL hA']
  · intro u hu f g hf hg a
    have hfc : ContDiff ℝ 2 f :=
      hf.1.of_le (by exact_mod_cast (show 2 ≤ fp81s21_q p + 2 by omega))
    have hgc : ContDiff ℝ 2 g :=
      hg.1.of_le (by exact_mod_cast (show 2 ≤ fp81s21_q p + 2 by omega))
    have hcomb : fp81s21_Input p (f + a • g) := by
      apply weightedTestSubmodule_iff.1
      have hfm : f ∈ weightedTestSubmodule p.d (fp81s21_q p + 2) (fp81s21_P p) :=
        weightedTestSubmodule_iff.2 hf
      have hgm : g ∈ weightedTestSubmodule p.d (fp81s21_q p + 2) (fp81s21_P p) :=
        weightedTestSubmodule_iff.2 hg
      exact (weightedTestSubmodule p.d (fp81s21_q p + 2)
        (fp81s21_P p)).add_mem hfm
          ((weightedTestSubmodule p.d (fp81s21_q p + 2)
            (fp81s21_P p)).smul_mem a hgm)
    have hnlF := hNLall u hu f hf
    have hnlG := hNLall u hu g hg
    have hIntF : ∀ j : Fin p.d, ∀ x : Euc p.d,
        Integrable (HRS.MS.Ul.ultInt p.s (fp81s21_b3_source R u f j) x) volume := by
      intro j x
      change Integrable (fun y =>
        if ‖x - y‖ ≤ (1 / 4 : ℝ) then
          (fp81s21_b3_source R u f j y - fp81s21_b3_source R u f j x) •
            rieszKernelGrad p.d p.s (x - y)
        else fp81s21_b3_source R u f j y • rieszKernelGrad p.d p.s (x - y)) volume
      exact hnlF.1 j x
    have hIntG : ∀ j : Fin p.d, ∀ x : Euc p.d,
        Integrable (HRS.MS.Ul.ultInt p.s (fp81s21_b3_source R u g j) x) volume := by
      intro j x
      change Integrable (fun y =>
        if ‖x - y‖ ≤ (1 / 4 : ℝ) then
          (fp81s21_b3_source R u g j y - fp81s21_b3_source R u g j x) •
            rieszKernelGrad p.d p.s (x - y)
        else fp81s21_b3_source R u g j y • rieszKernelGrad p.d p.s (x - y)) volume
      exact hnlG.1 j x
    have hlocLin := fp81s21_b3_local_add_smul ((r26t3_coeff R).drift u) a hfc hgc
    have hnlLin := fp81s21_b3_nonlocal_from_source_add_smul
      (u := u) (a := a) R hfc hgc hIntF hIntG
    have hg4Lin : fp81s21_g4N p R u (f + a • g) =
        fun x => fp81s21_g4N p R u f x + a * fp81s21_g4N p R u g x := by
      rw [fp81s21_b3_g4N_eq_nonlocal_from_source,
        fp81s21_b3_g4N_eq_nonlocal_from_source,
        fp81s21_b3_g4N_eq_nonlocal_from_source]
      exact hnlLin
    have hgenF := fp81s21_b3_generator_eq_local_sub_g4N R u f
    have hgenG := fp81s21_b3_generator_eq_local_sub_g4N R u g
    have hgenCombo := fp81s21_b3_generator_eq_local_sub_g4N R u (f + a • g)
    funext x
    rw [hgenCombo, hlocLin, hg4Lin, hgenF, hgenG]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

#print axioms HRS.Fp81.S21.fp81s21_b3_generator_from_nonlocal_contract

/-- The unconditional B3 weighted generator contract. -/
theorem fp81s21_b3_contract (p : Parameters) :
    fp81s21_weightedGen_contract p := by
  have hNL : ∀ B c : ℝ, 0 ≤ B → 0 < c →
      fp81s21_b3_nonlocal_all_tests_contract p B c :=
    fp81s21_b3_nonlocal_all_tests_unconditional p
  obtain ⟨A, hA, hgen⟩ := fp81s21_b3_generator_from_nonlocal_contract p hNL
  refine ⟨(1 / 2 : ℝ), by norm_num, le_rfl, A, hA, ?_⟩
  intro δ hδ hδhalf R Es E
  have hPOut : fp81s21_P p + 2 = (p.d : ℝ) + 4 := by
    dsimp [fp81s21_P]
    ring
  let Es' : r26t6_WeightedChart p.d (fp81s21_q p) (fp81s21_P p + 2) :=
    { encode := Es.encode
      test := Es.test
      add := by
        intro f g hf hg
        have hf' : IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4) f := by
          simpa only [hPOut] using hf
        have hg' : IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4) g := by
          simpa only [hPOut] using hg
        exact Es.add f g hf' hg'
      smul := by
        intro a f hf
        have hf' : IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4) f := by
          simpa only [hPOut] using hf
        exact Es.smul a f hf'
      norm := by
        intro f hf
        have hf' : IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4) f := by
          simpa only [hPOut] using hf
        simpa only [hPOut] using Es.norm f hf'
      test_smooth := Es.test_smooth
      test_coord := Es.test_coord
      dense := Es.dense }
  obtain ⟨hb, hl⟩ := hgen δ hδ hδhalf R
  obtain ⟨T, hT⟩ := fp81s21_b3_primal R Es' E A hA hb hl
  have hm := fp81s21_b3_basis_measurable hδ hδhalf R Es' E A hb
  obtain ⟨hmeas, hAdj⟩ := fp81s21_b3_adjoint R Es' E A T hT hm
  have hqRaw : (2 * p.d + 6) + 2 = 2 * p.d + 8 := by omega
  have hPOutRaw : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
  have hInput {f : Euc p.d → ℝ}
      (hf : IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f) :
      fp81s21_Input p f := by
    change IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f
    exact hf
  refine ⟨fun u => (T u).adjoint, ?_, ?_, ?_⟩
  · exact hmeas
  · intro u hu
    exact (hAdj u).1
  · intro u hu z f hf
    have hf' : fp81s21_Input p f := hInput hf
    have hbound := hb u hu f hf'
    have htest :
        IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4)
          (generatorW (r26t3_coeff R) u f) := by
      simpa only [fp81s21_Output, fp81s21_q, fp81s21_P, hPOutRaw] using hbound.1
    have hnorm :
        weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
            (generatorW (r26t3_coeff R) u f) ≤
          ENNReal.ofReal A *
            weightedSobolevE (2 * p.d + 8) ((p.d : ℝ) + 2) f := by
      simpa only [fp81s21_Eout, fp81s21_Ein, fp81s21_q, fp81s21_P,
        hqRaw, hPOutRaw] using hbound.2
    have hidentity := (hAdj u).2 z f hf'
    refine ⟨htest, hnorm, ?_⟩
    simpa only [fp81s21_chartAction, Es',
      show max u 0 = u from max_eq_left hu] using hidentity

#print axioms HRS.Fp81.S21.fp81s21_b3_contract

end HRS.Fp81.S21
