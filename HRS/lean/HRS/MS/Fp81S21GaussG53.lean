import HRS.MS.Fp81S21GaussG52
import HRS.MS.Fp81S21GaussG4Final
import HRS.MS.Fp81S21CoeffMoments10

/-! Dimension-free fourth moment for Gaussian chart coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

private theorem fp81s21_g5_coeff_enorm_rpow_eq_tsum
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

/-- Fixed-constant version of the coefficient Gaussian fourth-moment estimate.
The scalar Gaussian moment constant is an input, so it can be selected before
the coefficient field and probability space. -/
theorem fp81s21_g5_coeff_fourth_fixed
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : Ω → r26t6_Coeff) (w : ℕ → ℝ) (Cg : ℝ) (hCg : 0 ≤ Cg)
    (hgm : ∀ (ξ : Ω → ℝ), HasGaussianLaw ξ P → (∫ ω, ξ ω ∂P) = 0 →
      ∫⁻ ω, ‖ξ ω‖ₑ ^ (4 : ℝ) ∂P ≤
        ENNReal.ofReal (Cg * (∫ ω, ξ ω ^ 2 ∂P) ^ ((4 : ℝ) / 2)))
    (hq : Measurable q)
    (hw0 : ∀ j, 0 ≤ w j) (hwsum : Summable w)
    (hGaussian : ∀ j, HasGaussianLaw (fun ω => q ω j) P)
    (hMean : ∀ j, ∫ ω, q ω j ∂P = 0)
    (hVariance : ∀ j, (∫ ω, (q ω j) ^ 2 ∂P) ≤ w j) :
    MemLp q 4 P ∧ (∫ ω, ‖q ω‖ ^ 4 ∂P) ≤ Cg * (∑' j, w j) ^ 2 := by
  let S : ℝ := ∑' j : ℕ, w j
  have hS0 : 0 ≤ S := tsum_nonneg hw0
  have hmeasXi : ∀ j, AEMeasurable (fun ω => q ω j) P :=
    fun j => (hGaussian j).aemeasurable
  have hfin : ∀ F : Finset ℕ,
      ∫⁻ ω, (∑ j ∈ F, ENNReal.ofReal ((q ω j) ^ 2)) ^ (2 : ℝ) ∂P ≤
        ENNReal.ofReal (Cg * S ^ 2) := by
    intro F
    have hnorm : ∀ ω, (∑ j ∈ F, ENNReal.ofReal ((q ω j) ^ 2)) =
        ‖∑ j ∈ F, (q ω j) ^ 2‖ₑ := by
      intro ω
      rw [← ofReal_norm, Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _),
        ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _]
    have hmink := eLpNorm_sum_le (μ := P) (f := fun j ω => (q ω j) ^ 2)
      (s := F) (p := ENNReal.ofReal (2 : ℝ)) (by norm_num)
    have hbound : ∀ j, eLpNorm (fun ω => (q ω j) ^ 2) (ENNReal.ofReal (2 : ℝ)) P ≤
        ENNReal.ofReal (Cg ^ (1 / 2 : ℝ) * w j) := by
      intro j
      have hs6 : (2 : ℝ) ≤ 4 := by norm_num
      have hc : 0 ≤ Cg ^ ((2 : ℝ) / 4) := Real.rpow_nonneg hCg _
      have hscalar := HRS.MC.E214F.eLpNorm_sq_le
        hs6 hCg P (fun ω => q ω j) (hGaussian j)
        (hgm (fun ω => q ω j) (hGaussian j) (hMean j))
      have hbound' : eLpNorm (fun ω => (q ω j) ^ 2) (ENNReal.ofReal (4 / 2)) P ≤
          ENNReal.ofReal (Cg ^ ((2 : ℝ) / 4) * w j) := by
        exact hscalar.trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (hVariance j) hc))
      simpa [show (2 : ℝ) / 4 = 1 / 2 by norm_num,
        show (4 : ℝ) / 2 = 2 by norm_num] using hbound'
    have hsumBound :
        eLpNorm (∑ j ∈ F, fun ω => (q ω j) ^ 2) (ENNReal.ofReal (2 : ℝ)) P ≤
          ENNReal.ofReal (Cg ^ (1 / 2 : ℝ) * S) := by
      refine hmink.trans ((Finset.sum_le_sum fun j _ => hbound j).trans ?_)
      rw [← ENNReal.ofReal_sum_of_nonneg fun j _ =>
        mul_nonneg (Real.rpow_nonneg hCg _) (hw0 j)]
      apply ENNReal.ofReal_le_ofReal
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hwsum.sum_le_tsum F (fun j _ => hw0 j))
        (Real.rpow_nonneg hCg _)
    have h2 :
        (∫⁻ ω, ‖∑ j ∈ F, (q ω j) ^ 2‖ₑ ^ (2 : ℝ) ∂P) =
          eLpNorm (∑ j ∈ F, fun ω => (q ω j) ^ 2)
            (ENNReal.ofReal (2 : ℝ)) P ^ (2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofReal_ne_top
        (by
          refine Finset.aestronglyMeasurable_sum F fun j _ => ?_
          exact ((hmeasXi j).pow_const 2).aestronglyMeasurable),
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by norm_num), ENNReal.rpow_one]
      simp only [Finset.sum_apply]
    calc
      _ = ∫⁻ ω, ‖∑ j ∈ F, (q ω j) ^ 2‖ₑ ^ (2 : ℝ) ∂P := by simp_rw [hnorm]
      _ = _ := h2
      _ ≤ (ENNReal.ofReal (Cg ^ (1 / 2 : ℝ) * S)) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hsumBound (by norm_num)
      _ = ENNReal.ofReal (Cg * S ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
        congr 1
        rw [Real.mul_rpow (Real.rpow_nonneg hCg _) hS0, ← Real.rpow_mul hCg]
        norm_num
  have hlim : ∀ ω, ‖q ω‖ₑ ^ (4 : ℝ) =
      ⨆ F : Finset ℕ,
        (∑ j ∈ F, ENNReal.ofReal ((q ω j) ^ 2)) ^ (2 : ℝ) := by
    intro ω
    rw [fp81s21_g5_coeff_enorm_rpow_eq_tsum (q ω) (by norm_num), ENNReal.tsum_eq_iSup_sum]
    have hmap := Monotone.map_iSup_of_continuousAt
      (f := fun x : ℝ≥0∞ => x ^ (2 : ℝ))
      (g := fun F : Finset ℕ => ∑ j ∈ F, ENNReal.ofReal ((q ω j) ^ 2))
      (ENNReal.continuous_rpow_const.continuousAt)
      (ENNReal.monotone_rpow_of_nonneg (by norm_num))
      (by simp [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)])
    simpa [show (4 : ℝ) / 2 = 2 by norm_num] using hmap
  have hlin :
      (∫⁻ ω, ‖q ω‖ₑ ^ (4 : ℝ) ∂P) ≤ ENNReal.ofReal (Cg * S ^ 2) := by
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
  have hnonneg : ∀ ω, 0 ≤ ‖q ω‖ ^ 4 := fun ω => by positivity
  have hmeas : Measurable (fun ω => ‖q ω‖ ^ 4) := (measurable_norm.comp hq).pow_const 4
  have hlinReal :
      (∫⁻ ω, ENNReal.ofReal (‖q ω‖ ^ 4) ∂P) ≤ ENNReal.ofReal (Cg * S ^ 2) := by
    have hpoint (ω : Ω) : ENNReal.ofReal (‖q ω‖ ^ 4) = ‖q ω‖ₑ ^ (4 : ℝ) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ← ofReal_norm]
      exact (ENNReal.rpow_natCast (ENNReal.ofReal ‖q ω‖) 4).symm
    calc
      _ = ∫⁻ ω, ‖q ω‖ₑ ^ (4 : ℝ) ∂P := lintegral_congr fun ω => hpoint ω
      _ ≤ ENNReal.ofReal (Cg * S ^ 2) := hlin
  have hi : Integrable (fun ω => ‖q ω‖ ^ 4) P := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)]
    exact lt_of_le_of_lt hlinReal ENNReal.ofReal_lt_top
  have hIntegralENN :
      (∫⁻ ω, ENNReal.ofReal (‖q ω‖ ^ 4) ∂P) =
        ENNReal.ofReal (∫ ω, ‖q ω‖ ^ 4 ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall hnonneg)).symm
  have hreal : ENNReal.ofReal (∫ ω, ‖q ω‖ ^ 4 ∂P) ≤
      ENNReal.ofReal (Cg * S ^ 2) := by
    rw [← hIntegralENN]
    simpa [S] using hlinReal
  have hfinal : (∫ ω, ‖q ω‖ ^ 4 ∂P) ≤ Cg * S ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hreal
  have hmem : MemLp q 4 P := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num) (by norm_num) hq.aestronglyMeasurable]
    exact lt_of_le_of_lt (by simpa using hlin) ENNReal.ofReal_lt_top
  exact ⟨hmem, by simpa [S] using hfinal⟩



/-- The actual physical Gaussian field has uniform shifted fourth increments
in every weak-chart moment representative. In particular this applies to the
G3 chart embedding of its selected strong representative. -/
theorem fp81s21_g5_physical_increment_fourth (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
      ∀ H : ℝ, 0 < H → ∃ CG : ℝ, 0 ≤ CG ∧
        ∀ G : GaussianRealization R, ∀ q : ℝ → G.Ω → r26t6_Coeff, ∀ M : ℝ,
          fp81s21_MomentRep E G.P (fun u ω f => OscDual.eval (G.Z u ω) f) q M →
          ∀ a : ℝ, 0 ≤ a → ∀ s t : Icc (0 : ℝ) H,
            MemLp (fun ω => q (a + t) ω - q (a + s) ω) 4 G.P ∧
            (∫ ω, ‖q (a + t) ω - q (a + s) ω‖ ^ 4 ∂G.P) ≤
              CG * |(t : ℝ) - s| ^ 2 := by
  obtain ⟨Cg, hCg, hgm⟩ := HRS.MC.E214F.gaussian_rpow_moment
    (s := (4 : ℝ)) (by norm_num)
  obtain ⟨δ0, hδ0, hδhalf, hg4⟩ := fp81s21_g4_physical_unconditional p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R E H hH
  letI : IsProbabilityMeasure (r26t3_mu R 0) := fp81s21_initialMeasure_isProbability p R
  obtain ⟨Mg, K, hK, henvelope⟩ := hg4 δ hδ hδle R
  obtain ⟨l, hl0, hlsum, hinc⟩ := henvelope E H hH
  refine ⟨Cg * (∑' j, l j) ^ 2, by positivity, ?_⟩
  intro G q M hq a ha s t
  have hu : 0 ≤ a + (t : ℝ) := by linarith [t.property.1]
  have hv : 0 ≤ a + (s : ℝ) := by linarith [s.property.1]
  let Y : G.Ω → r26t6_Coeff := fun ω => q (a + t) ω - q (a + s) ω
  have hqm (u : ℝ) : Measurable (q u) :=
    hq.1.comp (measurable_const.prodMk measurable_id)
  have hYm : Measurable Y := (hqm _).sub (hqm _)
  have hYjm (j : ℕ) : Measurable (fun ω => Y ω j) :=
    (lp.evalCLM ℝ (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) j).continuous.measurable.comp hYm
  have hcenter (j : ℕ) : HRS.IsCenteredGaussian (G.P.map (fun ω => Y ω j)) := by
    simpa [Y, lp.coeFn_sub, Pi.sub_apply] using
      fp81s21_g5_coord_increment_centered p R E G q M hq (a + t) (a + s) hu hv j
  have hGaussian (j : ℕ) : HasGaussianLaw (fun ω => Y ω j) G.P :=
    ⟨(hYjm j).aemeasurable, (hcenter j).1⟩
  have hMean (j : ℕ) : (∫ ω, Y ω j ∂G.P) = 0 := by
    let X : G.Ω → ℝ := fun ω =>
      (lp.evalCLM ℝ (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) j) (Y ω)
    have hXm : Measurable X :=
      (lp.evalCLM ℝ (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) j).continuous.measurable.comp hYm
    have hc : HRS.IsCenteredGaussian (G.P.map X) := by
      change HRS.IsCenteredGaussian (G.P.map (fun ω => Y ω j))
      exact hcenter j
    calc
      (∫ ω, Y ω j ∂G.P) = ∫ ω, X ω ∂G.P := rfl
      _ = ∫ x : ℝ, x ∂G.P.map X :=
        (integral_map hXm.aemeasurable continuous_id.aestronglyMeasurable).symm
      _ = 0 := by simpa using hc.2 (ContinuousLinearMap.id ℝ ℝ)
  let w : ℕ → ℝ := fun j => l j * |(t : ℝ) - s|
  have hw0 : ∀ j, 0 ≤ w j := fun j => mul_nonneg (hl0 j) (abs_nonneg _)
  have hwsum : Summable w := by
    have h := hlsum.mul_left |(t : ℝ) - s|
    exact h.congr fun j => by simp [w, mul_comm]
  have hVariance (j : ℕ) : (∫ ω, (Y ω j) ^ 2 ∂G.P) ≤ w j := by
    have hsecond := fp81s21_g5_coord_increment_second p hδ
      (hδle.trans hδhalf) R hK E G q M hq (a + t) (a + s) hu hv j
    have hb := hinc a ha (s : ℝ) s.property (t : ℝ) t.property j
    simpa [Y, w, lp.coeFn_sub, Pi.sub_apply] using hsecond.2.le.trans hb
  have hgmG : ∀ (ξ : G.Ω → ℝ), HasGaussianLaw ξ G.P →
      (∫ ω, ξ ω ∂G.P) = 0 →
      ∫⁻ ω, ‖ξ ω‖ₑ ^ (4 : ℝ) ∂G.P ≤
        ENNReal.ofReal (Cg * (∫ ω, ξ ω ^ 2 ∂G.P) ^ ((4 : ℝ) / 2)) := by
    intro ξ hξ hmean
    exact hgm G.P ξ hξ hmean
  have hfour := fp81s21_g5_coeff_fourth_fixed G.P Y w Cg hCg hgmG hYm
    hw0 hwsum hGaussian hMean hVariance
  have hsum : (∑' j, w j) = (∑' j, l j) * |(t : ℝ) - s| := by
    simp [w, tsum_mul_right]
  refine ⟨hfour.1, ?_⟩
  calc
    (∫ ω, ‖q (a + t) ω - q (a + s) ω‖ ^ 4 ∂G.P) ≤
        Cg * (∑' j, w j) ^ 2 := hfour.2
    _ = (Cg * (∑' j, l j) ^ 2) * |(t : ℝ) - s| ^ 2 := by
      rw [hsum]
      ring

#print axioms fp81s21_g5_physical_increment_fourth

#print axioms fp81s21_g5_coeff_fourth_fixed
end HRS.Fp81.S21
end
