import HRS.MS.Fp81S21GaussMomRep11
import HRS.MS.Fp81S21CoeffMoments2
import HRS.MS.Fp81S21CoeffMoments9
import HRS.MS.Fp81S21GaussLin
import HRS.MS.ProClosureS111ChartTrace

/-! Uniform sixth moments for the moving Gaussian chart coefficients. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The coefficient norm is the square sum of its coordinates. -/
private theorem fp81s21_coeff_enorm_rpow_eq_tsum10
    (z : r26t6_Coeff) {s : ℝ} (hs : 0 < s) :
    ‖z‖ₑ ^ s = (∑' j : ℕ, ENNReal.ofReal (z j ^ 2)) ^ (s / 2) := by
  let z' : lp (fun _ : ℕ => ℝ) 2 := z
  have hsum : Summable (fun j : ℕ => z' j ^ 2) := HRS.StaticLimitAux.lp_sq_summable z'
  have hnorm : ‖z'‖ ^ 2 = ∑' j : ℕ, z' j ^ 2 := HRS.StaticLimitAux.lp_norm_sq z'
  have h1' : ∑' j : ℕ, ENNReal.ofReal (z' j ^ 2) = ENNReal.ofReal (‖z'‖ ^ 2) := by
    calc
      _ = ENNReal.ofReal (∑' j : ℕ, z' j ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg (z' j)) hsum).symm
      _ = _ := congrArg ENNReal.ofReal hnorm.symm
  have h1 : ∑' j : ℕ, ENNReal.ofReal (z j ^ 2) = ENNReal.ofReal (‖z‖ ^ 2) := by
    simpa [z'] using h1'
  rw [h1, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs.le,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

/-- Fixed-constant version of the coefficient Gaussian sixth-moment estimate.
The scalar Gaussian moment constant is an input, so it can be selected before
the coefficient field and probability space. -/
private theorem fp81s21_gaussian_coeff_sixthMoment_fixed
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : Ω → r26t6_Coeff) (w : ℕ → ℝ) (Cg : ℝ) (hCg : 0 ≤ Cg)
    (hgm : ∀ (ξ : Ω → ℝ), HasGaussianLaw ξ P → (∫ ω, ξ ω ∂P) = 0 →
      ∫⁻ ω, ‖ξ ω‖ₑ ^ (6 : ℝ) ∂P ≤
        ENNReal.ofReal (Cg * (∫ ω, ξ ω ^ 2 ∂P) ^ ((6 : ℝ) / 2)))
    (hq : Measurable q)
    (hw0 : ∀ j, 0 ≤ w j) (hwsum : Summable w)
    (hGaussian : ∀ j, HasGaussianLaw (fun ω => q ω j) P)
    (hMean : ∀ j, ∫ ω, q ω j ∂P = 0)
    (hVariance : ∀ j, (∫ ω, (q ω j) ^ 2 ∂P) ≤ w j) :
    fp81s21_Moment6 P q (Cg * (∑' j, w j) ^ 3) := by
  let S : ℝ := ∑' j : ℕ, w j
  have hS0 : 0 ≤ S := tsum_nonneg hw0
  have hmeasXi : ∀ j, AEMeasurable (fun ω => q ω j) P :=
    fun j => (hGaussian j).aemeasurable
  have hfin : ∀ F : Finset ℕ,
      ∫⁻ ω, (∑ j ∈ F, ENNReal.ofReal ((q ω j) ^ 2)) ^ (3 : ℝ) ∂P ≤
        ENNReal.ofReal (Cg * S ^ 3) := by
    intro F
    have hnorm : ∀ ω, (∑ j ∈ F, ENNReal.ofReal ((q ω j) ^ 2)) =
        ‖∑ j ∈ F, (q ω j) ^ 2‖ₑ := by
      intro ω
      rw [← ofReal_norm, Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _),
        ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _]
    have hmink := eLpNorm_sum_le (μ := P) (f := fun j ω => (q ω j) ^ 2)
      (s := F) (p := ENNReal.ofReal (3 : ℝ)) (by norm_num)
    have hbound : ∀ j, eLpNorm (fun ω => (q ω j) ^ 2) (ENNReal.ofReal (3 : ℝ)) P ≤
        ENNReal.ofReal (Cg ^ (1 / 3 : ℝ) * w j) := by
      intro j
      have hs6 : (2 : ℝ) ≤ 6 := by norm_num
      have hc : 0 ≤ Cg ^ ((2 : ℝ) / 6) := Real.rpow_nonneg hCg _
      have hscalar := HRS.MC.E214F.eLpNorm_sq_le
        hs6 hCg P (fun ω => q ω j) (hGaussian j)
        (hgm (fun ω => q ω j) (hGaussian j) (hMean j))
      have hbound' : eLpNorm (fun ω => (q ω j) ^ 2) (ENNReal.ofReal (6 / 2)) P ≤
          ENNReal.ofReal (Cg ^ ((2 : ℝ) / 6) * w j) := by
        exact hscalar.trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (hVariance j) hc))
      simpa [show (2 : ℝ) / 6 = 1 / 3 by norm_num,
        show (6 : ℝ) / 2 = 3 by norm_num] using hbound'
    have hsumBound :
        eLpNorm (∑ j ∈ F, fun ω => (q ω j) ^ 2) (ENNReal.ofReal (3 : ℝ)) P ≤
          ENNReal.ofReal (Cg ^ (1 / 3 : ℝ) * S) := by
      refine hmink.trans ((Finset.sum_le_sum fun j _ => hbound j).trans ?_)
      rw [← ENNReal.ofReal_sum_of_nonneg fun j _ =>
        mul_nonneg (Real.rpow_nonneg hCg _) (hw0 j)]
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hwsum.sum_le_tsum F (fun j _ => hw0 j))
        (Real.rpow_nonneg hCg _)
    have h2 :
        (∫⁻ ω, ‖∑ j ∈ F, (q ω j) ^ 2‖ₑ ^ (3 : ℝ) ∂P) =
          eLpNorm (∑ j ∈ F, fun ω => (q ω j) ^ 2)
            (ENNReal.ofReal (3 : ℝ)) P ^ (3 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofReal_ne_top
        (by
          refine Finset.aestronglyMeasurable_sum F fun j _ => ?_
          exact ((hmeasXi j).pow_const 2).aestronglyMeasurable),
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3),
        ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by norm_num), ENNReal.rpow_one]
      simp only [Finset.sum_apply]
    calc
      _ = ∫⁻ ω, ‖∑ j ∈ F, (q ω j) ^ 2‖ₑ ^ (3 : ℝ) ∂P := by simp_rw [hnorm]
      _ = _ := h2
      _ ≤ (ENNReal.ofReal (Cg ^ (1 / 3 : ℝ) * S)) ^ (3 : ℝ) :=
        ENNReal.rpow_le_rpow hsumBound (by norm_num)
      _ = ENNReal.ofReal (Cg * S ^ 3) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
        congr 1
        rw [Real.mul_rpow (Real.rpow_nonneg hCg _) hS0, ← Real.rpow_mul hCg]
        norm_num
  have hlim : ∀ ω, ‖q ω‖ₑ ^ (6 : ℝ) =
      ⨆ F : Finset ℕ,
        (∑ j ∈ F, ENNReal.ofReal ((q ω j) ^ 2)) ^ (3 : ℝ) := by
    intro ω
    rw [fp81s21_coeff_enorm_rpow_eq_tsum10 (q ω) (by norm_num), ENNReal.tsum_eq_iSup_sum]
    have hmap := Monotone.map_iSup_of_continuousAt
      (f := fun x : ℝ≥0∞ => x ^ (3 : ℝ))
      (g := fun F : Finset ℕ => ∑ j ∈ F, ENNReal.ofReal ((q ω j) ^ 2))
      (ENNReal.continuous_rpow_const.continuousAt)
      (ENNReal.monotone_rpow_of_nonneg (by norm_num))
      (by simp [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 3)])
    simpa [show (6 : ℝ) / 2 = 3 by norm_num] using hmap
  have hlin :
      (∫⁻ ω, ‖q ω‖ₑ ^ (6 : ℝ) ∂P) ≤ ENNReal.ofReal (Cg * S ^ 3) := by
    simp_rw [hlim]
    rw [lintegral_iSup_directed]
    · exact iSup_le hfin
    · intro F
      have hsumMeas : AEMeasurable
          (fun ω => ∑ j ∈ F, ENNReal.ofReal ((q ω j) ^ 2)) P :=
        Finset.aemeasurable_fun_sum F fun j _ =>
          ((hmeasXi j).pow_const 2).ennreal_ofReal
      exact hsumMeas.pow_const _
    · intro F F'
      refine ⟨F ∪ F', ?_, ?_⟩
      · intro ω
        exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (by simp)) (by norm_num)
      · intro ω
        exact ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset (by simp)) (by norm_num)
  have hnonneg : ∀ ω, 0 ≤ ‖q ω‖ ^ 6 := fun ω => by positivity
  have hmeas : Measurable (fun ω => ‖q ω‖ ^ 6) := (measurable_norm.comp hq).pow_const 6
  have hlinReal :
      (∫⁻ ω, ENNReal.ofReal (‖q ω‖ ^ 6) ∂P) ≤ ENNReal.ofReal (Cg * S ^ 3) := by
    have hpoint (ω : Ω) : ENNReal.ofReal (‖q ω‖ ^ 6) = ‖q ω‖ₑ ^ (6 : ℝ) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ← ofReal_norm]
      exact (ENNReal.rpow_natCast (ENNReal.ofReal ‖q ω‖) 6).symm
    calc
      _ = ∫⁻ ω, ‖q ω‖ₑ ^ (6 : ℝ) ∂P := lintegral_congr fun ω => hpoint ω
      _ ≤ ENNReal.ofReal (Cg * S ^ 3) := hlin
  have hi : Integrable (fun ω => ‖q ω‖ ^ 6) P := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)]
    exact lt_of_le_of_lt hlinReal ENNReal.ofReal_lt_top
  have hIntegralENN :
      (∫⁻ ω, ENNReal.ofReal (‖q ω‖ ^ 6) ∂P) =
        ENNReal.ofReal (∫ ω, ‖q ω‖ ^ 6 ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall hnonneg)).symm
  have hreal : ENNReal.ofReal (∫ ω, ‖q ω‖ ^ 6 ∂P) ≤
      ENNReal.ofReal (Cg * S ^ 3) := by
    rw [← hIntegralENN]
    simpa [S] using hlinReal
  have hfinal : (∫ ω, ‖q ω‖ ^ 6 ∂P) ≤ Cg * S ^ 3 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hreal
  exact ⟨hq.aemeasurable, hi, by simpa [S] using hfinal⟩

private theorem fp81s21_embedField_normalized_norm_le_one
    {d r r' : ℕ} {Pw Ps : ℝ}
    (hr : r + 2 = r') (hp : Pw + 2 = Ps)
    (hP : (d : ℝ) < 2 * Pw) (hPs : (d : ℝ) < 2 * Ps)
    (Es : r26t6_WeightedChart d r Ps) (E : r26t6_WeightedChart d r' Pw) :
    ‖fp81s21_embedField_normalized hr hp hP hPs Es E‖ ≤ 1 := by
  subst r'
  subst Ps
  exact fp81s21_embedField_norm_le_one hP hPs Es E

/-- Gaussian strong-chart coefficients have a uniform sixth moment. The same
coefficient family transports to the physical weak chart with unchanged
second and sixth moment constants. Both constants are chosen before `G`. -/
theorem fp81s21_gaussian_six_momentRep (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
        ∃ M2 M6 : ℝ, 0 ≤ M2 ∧ 0 ≤ M6 ∧
          ∀ G : GaussianRealization R,
            ∃ q : ℝ → G.Ω → r26t6_Coeff,
              fp81s21_MomentRep Es G.P
                (fun u ω f => OscDual.eval (G.Z u ω) f) q M2 ∧
              fp81s21_Six G.P q M6 ∧
              fp81s21_MomentRep E G.P
                (fun u ω f => OscDual.eval (G.Z u ω) f)
                (fun u ω => fp81s21_gaussian_chartEmbed p Es E (q u ω)) M2 ∧
              fp81s21_Six G.P
                (fun u ω => fp81s21_gaussian_chartEmbed p Es E (q u ω)) M6 := by
  obtain ⟨Cg, hCg, hgm⟩ := HRS.MC.E214F.gaussian_rpow_moment
    (s := (6 : ℝ)) (by norm_num)
  obtain ⟨δa, hδa, hδah, hcoords⟩ := fp81s21_gaussian_strong_coord p
  obtain ⟨δb, hδb, hδbh, hlaw⟩ := fp81s21_gaussLin_test_gaussian_law p
  refine ⟨min δa δb, lt_min hδa hδb, (min_le_left _ _).trans hδah, ?_⟩
  intro δ hδ hδle R Es E
  obtain ⟨M2, hM2, hGcoords⟩ :=
    hcoords δ hδ (hδle.trans (min_le_left _ _)) R Es E
  let M6 : ℝ := Cg * M2 ^ 3
  have hM6 : 0 ≤ M6 := by dsimp [M6]; positivity
  refine ⟨M2, M6, hM2, hM6, ?_⟩
  intro G
  obtain ⟨q, hRep, hcoord⟩ := hGcoords G
  have hgmG : ∀ (ξ : G.Ω → ℝ), HasGaussianLaw ξ G.P →
      (∫ ω, ξ ω ∂G.P) = 0 →
      ∫⁻ ω, ‖ξ ω‖ₑ ^ (6 : ℝ) ∂G.P ≤
        ENNReal.ofReal (Cg * (∫ ω, ξ ω ^ 2 ∂G.P) ^ ((6 : ℝ) / 2)) := by
    intro ξ hξ hmean
    exact hgm G.P ξ hξ hmean
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by nlinarith [p.hd]
  have hPs : (p.d : ℝ) < 2 * ((p.d : ℝ) + 4) := by nlinarith [p.hd]
  have hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
  let Es' : r26t6_WeightedChart p.d (2 * p.d + 6)
      (((p.d : ℝ) + 2) + 2) := hExp.symm ▸ Es
  let qE : ℝ → G.Ω → r26t6_Coeff := fun u ω =>
    fp81s21_gaussian_chartEmbed p Es E (q u ω)
  have hSixStrong : fp81s21_Six G.P q M6 := by
    intro u hu
    obtain ⟨hmem, hsecond, hfield⟩ := hRep.2 u hu
    have hqu : Measurable (q u) :=
      hRep.1.comp (measurable_const.prodMk measurable_id)
    have hqj : ∀ j, Measurable (fun ω => q u ω j) := by
      intro j
      exact (lp.evalCLM ℝ (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) j).continuous.measurable.comp hqu
    have hNormInt : Integrable (fun ω => ‖q u ω‖ ^ 2) G.P :=
      hmem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    let w : ℕ → ℝ := fun j => ∫ ω, (q u ω j) ^ 2 ∂G.P
    have hw0 : ∀ j, 0 ≤ w j := fun j => integral_nonneg fun ω => sq_nonneg _
    have hfinite : ∀ s : Finset ℕ, ∀ ω,
        (∑ j ∈ s, (q u ω j) ^ 2) ≤ ‖q u ω‖ ^ 2 := by
      intro s ω
      have hsum := HRS.StaticLimitAux.lp_sq_summable (q u ω)
      calc
        (∑ j ∈ s, (q u ω j) ^ 2) ≤ ∑' j, (q u ω j) ^ 2 :=
          hsum.sum_le_tsum s (fun j _ => sq_nonneg (q u ω j))
        _ = ‖q u ω‖ ^ 2 := (HRS.StaticLimitAux.lp_norm_sq (q u ω)).symm
    have htrace := HRS.MS.ProClosureS111.summable_integral_sq_of_finite_trace
      G.P (fun j ω => q u ω j) (fun ω => ‖q u ω‖ ^ 2) hqj hNormInt hfinite
    have hwsum : Summable w := by simpa [w] using htrace.2.1
    have hwsumBound : (∑' j, w j) ≤ M2 := by
      calc
        _ ≤ ∫ ω, ‖q u ω‖ ^ 2 ∂G.P := by simpa [w] using htrace.2.2
        _ ≤ M2 := hsecond
    have hGaussian : ∀ j, HasGaussianLaw (fun ω => q u ω j) G.P := by
      intro j
      let φ : Euc p.d → ℝ := Es.test j
      have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ :=
        r2Test_isOscTest _ (Es.test_smooth j)
      obtain ⟨v, hMap⟩ := hlaw δ hδ
        (hδle.trans (min_le_right _ _)) R G u hu φ hφ
      have hEvalMeas : Measurable
          (fun ω => OscDual.eval (G.Z u ω) φ) := by
        let phi : HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ) := ⟨φ, hφ⟩
        have heq : (fun ω => OscDual.eval (G.Z u ω) φ) =
            HRS.MS.ProClosureS111.gaussianOscEval phi ∘ G.Z u := by
          funext ω
          exact (HRS.MS.ProClosureS111.gaussianOscEval_apply phi (G.Z u ω)).symm
        rw [heq]
        exact (HRS.MS.ProClosureS111.gaussianOscEval phi).continuous.measurable.comp
          ((G.evolution (u + 1)).meas u)
      have hEvalGaussian : HasGaussianLaw
          (fun ω => OscDual.eval (G.Z u ω) φ) G.P := by
        refine ⟨hEvalMeas.aemeasurable, ?_⟩
        rw [hMap]
        infer_instance
      have hcoordj : (fun ω => q u ω j) =ᵐ[G.P]
          (fun ω => OscDual.eval (G.Z u ω) φ) := by
        filter_upwards [hcoord u hu j] with ω hω
        exact hω
      exact hEvalGaussian.congr hcoordj.symm
    have hMean : ∀ j, ∫ ω, q u ω j ∂G.P = 0 := by
      intro j
      let φ : Euc p.d → ℝ := Es.test j
      have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ :=
        r2Test_isOscTest _ (Es.test_smooth j)
      obtain ⟨v, hMap⟩ := hlaw δ hδ
        (hδle.trans (min_le_right _ _)) R G u hu φ hφ
      have hEvalMeas : Measurable
          (fun ω => OscDual.eval (G.Z u ω) φ) := by
        let phi : HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ) := ⟨φ, hφ⟩
        have heq : (fun ω => OscDual.eval (G.Z u ω) φ) =
            HRS.MS.ProClosureS111.gaussianOscEval phi ∘ G.Z u := by
          funext ω
          exact (HRS.MS.ProClosureS111.gaussianOscEval_apply phi (G.Z u ω)).symm
        rw [heq]
        exact (HRS.MS.ProClosureS111.gaussianOscEval phi).continuous.measurable.comp
          ((G.evolution (u + 1)).meas u)
      have hEvalMean :
          ∫ ω, OscDual.eval (G.Z u ω) φ ∂G.P = 0 := by
        calc
          _ = ∫ x, x ∂G.P.map (fun ω => OscDual.eval (G.Z u ω) φ) := by
            symm
            exact integral_map hEvalMeas.aemeasurable
              measurable_id'.aestronglyMeasurable
          _ = ∫ x, x ∂gaussianReal 0 v := by rw [hMap]
          _ = 0 := by simp
      have hcoordj : (fun ω => q u ω j) =ᵐ[G.P]
          (fun ω => OscDual.eval (G.Z u ω) φ) := by
        filter_upwards [hcoord u hu j] with ω hω
        exact hω
      calc
        _ = ∫ ω, OscDual.eval (G.Z u ω) φ ∂G.P := integral_congr_ae hcoordj
        _ = 0 := hEvalMean
    have hVariance : ∀ j, (∫ ω, (q u ω j) ^ 2 ∂G.P) ≤ w j := by
      intro j
      exact le_of_eq (by rfl)
    have hfixed := fp81s21_gaussian_coeff_sixthMoment_fixed G.P (q u) w Cg hCg hgmG
      hqu hw0 hwsum hGaussian hMean hVariance
    have hbound : Cg * (∑' j, w j) ^ 3 ≤ M6 := by
      dsimp [M6]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (tsum_nonneg hw0) hwsumBound 3) hCg
    rcases hfixed with ⟨hAEM, hInt, hfixedBound⟩
    exact ⟨hAEM, hInt, hfixedBound.trans hbound⟩
  have hWeakRep : fp81s21_MomentRep E G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f) qE M2 := by
    simpa [qE, fp81s21_gaussian_chartEmbed] using
      (fp81s21_MomentRep_embedField_normalized
        (d := p.d) (r := 2 * p.d + 6) (r' := 2 * p.d + 8)
        (Pw := (p.d : ℝ) + 2) (Ps := (p.d : ℝ) + 4)
        (by omega) (by ring)
        hP hPs Es E G.P (fun u ω f => OscDual.eval (G.Z u ω) f) q M2 hRep)
  have hWeakSix : fp81s21_Six G.P qE M6 := by
    have hKnorm : ‖fp81s21_gaussian_chartEmbed p Es E‖ ≤ 1 := by
      change ‖fp81s21_embedField_normalized
        (d := p.d) (r := 2 * p.d + 6) (r' := 2 * p.d + 8)
        (Pw := (p.d : ℝ) + 2) (Ps := (p.d : ℝ) + 4)
        (by omega) (by ring) hP hPs Es E‖ ≤ 1
      exact fp81s21_embedField_normalized_norm_le_one
        (by omega) (by ring) hP hPs Es E
    intro u hu
    obtain ⟨hMeas, hInt, hBound⟩ := hSixStrong u hu
    let K : r26t6_Coeff →L[ℝ] r26t6_Coeff := fp81s21_gaussian_chartEmbed p Es E
    have hKMeas : AEMeasurable (fun ω => K (q u ω)) G.P :=
      K.continuous.measurable.comp_aemeasurable hMeas
    have hNorm : ∀ ω, ‖K (q u ω)‖ ≤ ‖q u ω‖ := by
      intro ω
      calc
        ‖K (q u ω)‖ ≤ ‖K‖ * ‖q u ω‖ := K.le_opNorm _
        _ ≤ 1 * ‖q u ω‖ := mul_le_mul_of_nonneg_right hKnorm (norm_nonneg _)
        _ = ‖q u ω‖ := one_mul _
    have hPow : ∀ ω, ‖K (q u ω)‖ ^ 6 ≤ ‖q u ω‖ ^ 6 := by
      intro ω
      exact pow_le_pow_left₀ (norm_nonneg _) (hNorm ω) 6
    have hTargetMeas : AEMeasurable (fun ω => ‖K (q u ω)‖ ^ 6) G.P := by
      exact (measurable_norm.pow_const 6).comp_aemeasurable
        (K.continuous.measurable.comp_aemeasurable hMeas)
    have hTargetInt : Integrable (fun ω => ‖K (q u ω)‖ ^ 6) G.P := by
      exact hInt.mono_nonneg hTargetMeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun _ => by positivity)
        (Filter.Eventually.of_forall hPow)
    have hTargetBound : (∫ ω, ‖K (q u ω)‖ ^ 6 ∂G.P) ≤ M6 := by
      calc
        _ ≤ ∫ ω, ‖q u ω‖ ^ 6 ∂G.P :=
          integral_mono_ae hTargetInt hInt (Filter.Eventually.of_forall hPow)
        _ ≤ M6 := hBound
    exact ⟨hKMeas, hTargetInt, hTargetBound⟩
  exact ⟨q, hRep, hSixStrong, hWeakRep, hWeakSix⟩

#print axioms fp81s21_gaussian_six_momentRep

end HRS.Fp81.S21

end
