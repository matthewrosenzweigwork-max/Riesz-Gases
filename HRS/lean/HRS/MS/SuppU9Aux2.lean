import HRS.Whole.Orbits
import HRS.Prob.HilbertBDG

/-!
# U9 (aux 2): the reconstruction map on `𝒦 = KSpace d m T`: norm bounds and continuity of `evalA`
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.U9

open HRS.Whole

variable {d : ℕ} {m T : ℝ}

lemma u9_norm_A₀_le (x : KSpace d m T) : ‖x.A₀‖ ≤ ‖x‖ :=
  WithLp.norm_fst_le (x := show WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m)) from x)

lemma u9_norm_A'_le (x : KSpace d m T) : ‖x.A'‖ ≤ ‖x‖ :=
  (WithLp.norm_fst_le (x := show WithLp 2 (L2Path d m T × OscDual d m) from
    (show WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m)) from x).snd)).trans
    (WithLp.norm_snd_le (x := show WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m)) from x))

lemma u9_norm_B_le (x : KSpace d m T) : ‖x.B‖ ≤ ‖x‖ :=
  (WithLp.norm_snd_le (x := show WithLp 2 (L2Path d m T × OscDual d m) from
    (show WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m)) from x).snd)).trans
    (WithLp.norm_snd_le (x := show WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m)) from x))

lemma u9_B_sub (x y : KSpace d m T) : (x - y).B = x.B - y.B := rfl

lemma u9_continuous_B : Continuous fun x : KSpace d m T => x.B := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm, ← u9_B_sub]
  simpa using u9_norm_B_le (x - y)


lemma u9_integrableOn (g : L2Path d m T) :
    IntegrableOn (g : ℝ → OscDual d m) (Set.Icc (0 : ℝ) T) :=
  (Lp.memLp g).integrable (by norm_num)

lemma u9_l1_le (hT : 0 ≤ T) (g : L2Path d m T) :
    ∫ τ in Set.Icc (0 : ℝ) T, ‖(g : ℝ → OscDual d m) τ‖ ≤ Real.sqrt T * ‖g‖ := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  have hmem : MemLp (g : ℝ → OscDual d m) 2 μ := Lp.memLp g
  have hae : AEStronglyMeasurable (g : ℝ → OscDual d m) μ := hmem.aestronglyMeasurable
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (p := 1) (q := 2) (by norm_num) hae
  have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by
    norm_num [ENNReal.toReal_ofNat]
  rw [hexp] at h1
  have hμu : μ Set.univ = ENNReal.ofReal T := by
    rw [hμ, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  have hint : ∫ τ in Set.Icc (0 : ℝ) T, ‖(g : ℝ → OscDual d m) τ‖ =
      (eLpNorm (g : ℝ → OscDual d m) 1 μ).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    · exact integral_norm_eq_lintegral_enorm hae
    · exact hae
  rw [hint]
  have h2 : eLpNorm (g : ℝ → OscDual d m) 2 μ ≠ ⊤ := hmem.eLpNorm_ne_top
  have h3 : μ Set.univ ^ (1 / 2 : ℝ) ≠ ⊤ := by
    rw [hμu]; exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  calc (eLpNorm (g : ℝ → OscDual d m) 1 μ).toReal
      ≤ (eLpNorm (g : ℝ → OscDual d m) 2 μ * μ Set.univ ^ (1 / 2 : ℝ)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top h2 h3) h1
    _ = Real.sqrt T * ‖g‖ := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, hμu, ENNReal.toReal_ofReal hT, Lp.norm_def,
          Real.sqrt_eq_rpow, mul_comm]

lemma u9_evalA_norm_le (hT : 0 ≤ T) (x : KSpace d m T) (t : ℝ) :
    ‖x.evalA t‖ ≤ ‖x.A₀‖ + Real.sqrt T * ‖x.A'‖ := by
  unfold KSpace.evalA
  refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
  refine (norm_integral_le_integral_norm _).trans ?_
  refine le_trans ?_ (u9_l1_le hT x.A')
  refine setIntegral_mono_set (u9_integrableOn x.A').norm (Filter.Eventually.of_forall fun τ => norm_nonneg _)
    (Filter.Eventually.of_forall ?_)
  exact Set.Icc_subset_Icc_right (min_le_right _ _)

lemma u9_continuousOn_evalA (hT : 0 ≤ T) (x : KSpace d m T) :
    ContinuousOn (fun t => x.evalA t) (Set.Icc (0 : ℝ) T) := by
  have hint : IntegrableOn (x.A' : ℝ → OscDual d m) (Set.uIcc (0 : ℝ) T) := by
    rw [Set.uIcc_of_le hT]; exact u9_integrableOn x.A'
  have hc := intervalIntegral.continuousOn_primitive_interval (a := 0) hint
  rw [Set.uIcc_of_le hT] at hc
  refine continuousOn_const.add (hc.congr fun t ht => ?_)
  simp only
  rw [min_eq_left ht.2, intervalIntegral.integral_of_le ht.1, integral_Icc_eq_integral_Ioc]

lemma u9_recon_norm_le (hT : 0 ≤ T) (x y : KSpace d m T) (t : ℝ) :
    ‖x.evalA t - x.B + y.B‖ ≤ (2 + Real.sqrt T) * ‖x‖ + ‖y‖ := by
  have h1 := u9_evalA_norm_le hT x t
  have h2 := u9_norm_A₀_le x
  have h3 := u9_norm_A'_le x
  have h4 := u9_norm_B_le x
  have h5 := u9_norm_B_le y
  have hs : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  have h6 : Real.sqrt T * ‖x.A'‖ ≤ Real.sqrt T * ‖x‖ := by gcongr
  calc ‖x.evalA t - x.B + y.B‖ ≤ ‖x.evalA t‖ + ‖x.B‖ + ‖y.B‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_sub_le _ _) _ |>.trans' le_rfl)
    _ ≤ (2 + Real.sqrt T) * ‖x‖ + ‖y‖ := by nlinarith

end HRS.MS.U9
