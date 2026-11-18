import HRS.MS.ProClosureS111WeightedCutoff
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
Compact-smooth density for the exact frozen weighted norm. The cutoff
argument uses an L2 majorant made from the original finite-norm jet vector;
the subsequent mollification is uniform on the finitely many spatial jets.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.FixEq

theorem L2_norm_tendsto_of_dominated_pointwise
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (mu : Measure X) (F : ℕ → X → V) (f : X → V)
    (hF : ∀ n, StronglyMeasurable (F n)) (hfm : StronglyMeasurable f)
    (hf : MemLp f 2 mu) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ n x, ‖F n x - f x‖ ≤ K * ‖f x‖)
    (ht : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => eLpNorm (F n - f) 2 mu) atTop (𝓝 0) := by
  have hdom : (∫⁻ x, ‖K • f x‖ₑ ^ (2 : ℝ) ∂mu) < ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (hf.const_smul K).aestronglyMeasurable).1 (hf.const_smul K).eLpNorm_lt_top
    simpa only [ENNReal.toReal_ofNat, Pi.smul_apply] using h
  have hint : Tendsto (fun n => ∫⁻ x, ‖F n x - f x‖ₑ ^ (2 : ℝ) ∂mu)
      atTop (𝓝 (∫⁻ _x, (0 : ℝ≥0∞) ∂mu)) := by
    apply tendsto_lintegral_of_dominated_convergence
      (fun x => ‖K • f x‖ₑ ^ (2 : ℝ))
    · intro n
      exact (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp
        (((hF n).sub hfm).measurable.enorm)
    · intro n
      refine ae_of_all _ fun x => ENNReal.rpow_le_rpow ?_ (by norm_num)
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
      apply ENNReal.ofReal_le_ofReal
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hK] using hb n x
    · exact hdom.ne
    · refine ae_of_all _ fun x => ?_
      have hc : Continuous (fun v : V => ‖v‖ₑ ^ (2 : ℝ)) := by fun_prop
      have h := (hc.tendsto (f x - f x)).comp ((ht x).sub tendsto_const_nhds)
      simpa [Function.comp_def] using h
  have he : ∀ n, eLpNorm (F n - f) 2 mu =
      (∫⁻ x, ‖F n x - f x‖ₑ ^ (2 : ℝ) ∂mu) ^ (1 / 2 : ℝ) := by
    intro n
    simpa only [ENNReal.toReal_ofNat, Pi.sub_apply] using
      eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        ((hF n).sub hfm).aestronglyMeasurable
  have hout := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
  simpa only [Function.comp_def, he, lintegral_zero,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
    hout.comp (by simpa only [lintegral_zero] using hint)

variable {d r : ℕ} {Pw : ℝ}

/-- Compact C^r tests approximate every finite-norm weighted test in the
actual L2 jet Hilbert space. -/
theorem weighted_compact_approximation (f : weightedTestSubmodule d r Pw) :
    ∃ h : ℕ → weightedTestSubmodule d r Pw,
      (∀ n, HasCompactSupport (h n : Euc d → ℝ)) ∧
      Tendsto (fun n => weightedJetMap d r Pw (h n)) atTop
        (𝓝 (weightedJetMap d r Pw f)) := by
  obtain ⟨K, hK, h, hreg, hbound, hlocal⟩ :=
    weighted_cutoff_family (Pw := Pw) f.property.1
  have hLp : ∀ n, MemLp (weightedJets r Pw (h n)) 2 volume := by
    intro n
    refine (f.property.2.norm.const_mul K).mono'
      (weightedJets_continuous (hreg n).1).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    exact hbound n x
  have ht : ∀ x, Tendsto (fun n => weightedJets r Pw (h n) x) atTop
      (𝓝 (weightedJets r Pw f x)) := by
    intro x
    apply tendsto_const_nhds.congr'
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : ‖x‖ < (n : ℝ) + 1 := by
      have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    ext p
    change jbracket x ^ (-Pw) * partialDeriv p.2 f x =
      jbracket x ^ (-Pw) * partialDeriv p.2 (h n) x
    congr 1
    unfold partialDeriv
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ (hlocal n x hn') p.1).self_of_nhds]
  have hnorm : Tendsto (fun n =>
      eLpNorm (weightedJets r Pw (h n) - weightedJets r Pw f) 2 volume)
      atTop (𝓝 0) :=
    L2_norm_tendsto_of_dominated_pointwise volume
      (fun n => weightedJets r Pw (h n)) (weightedJets r Pw f)
      (fun n => (weightedJets_continuous (hreg n).1).stronglyMeasurable)
      (weightedJets_continuous f.property.1).stronglyMeasurable f.property.2
      (show 0 ≤ K + 1 by linarith)
      (fun n x => (norm_sub_le _ _).trans (by
        have hh := hbound n x
        nlinarith [norm_nonneg (weightedJets r Pw f x)])) ht
  refine ⟨fun n => ⟨h n, (hreg n).1, hLp n⟩, fun n => (hreg n).2, ?_⟩
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => weightedJets r Pw (h n)) hLp
    (weightedJets r Pw f) f.property.2).2 hnorm

/-- Every finite-norm weighted test is a limit of actual compactly
supported smooth tests in the exact frozen norm. -/
theorem weighted_smooth_approximation (hP : (d : ℝ) < 2 * Pw)
    (f : weightedTestSubmodule d r Pw) :
    ∃ g : ℕ → weightedTestSubmodule d r Pw,
      (∀ n, IsR2Test (g n : Euc d → ℝ)) ∧
      Tendsto (fun n => weightedJetMap d r Pw (g n)) atTop
        (𝓝 (weightedJetMap d r Pw f)) := by
  obtain ⟨h, hc, ht⟩ := weighted_compact_approximation f
  have happ : ∀ n : ℕ, ∃ g : Euc d → ℝ, IsR2Test g ∧
      ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x,
        |partialDeriv i g x - partialDeriv i (h n) x| ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨g, hg, hgc, hb⟩ := s57p_smooth_approx (h n).property.1 (hc n)
      (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
    exact ⟨g, ⟨hg, hgc⟩, hb⟩
  choose g hg hgb using happ
  let gs : ℕ → weightedTestSubmodule d r Pw :=
    fun n => ⟨g n, weighted_test_of_compact_smooth hP (hg n)⟩
  let A : ℝ := s57pC d r Pw * ((d : ℝ) + 1) ^ r
  have hA : 0 ≤ A := mul_nonneg (s57pC_nonneg _ _ _) (by positivity)
  have hdif : ∀ n,
      ‖weightedJetMap d r Pw (gs n) - weightedJetMap d r Pw (h n)‖ ≤
        A * (1 / ((n : ℝ) + 1)) := by
    intro n
    rw [← map_sub, weightedJetMap_norm]
    have hjet : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x,
        |partialDeriv i ((gs n - h n : weightedTestSubmodule d r Pw) : Euc d → ℝ) x| ≤
          1 / ((n : ℝ) + 1) := by
      intro j hj i x
      rw [show ((gs n - h n : weightedTestSubmodule d r Pw) : Euc d → ℝ) =
        (fun y => g n y - (h n : Euc d → ℝ) y) from rfl,
        s57p_partialDeriv_sub (gs n).property.1 (h n).property.1 hj i x]
      exact hgb n j hj i x
    have hiter : ∀ j ≤ r, ∀ x,
        ‖iteratedFDeriv ℝ j
          ((gs n - h n : weightedTestSubmodule d r Pw) : Euc d → ℝ) x‖ ≤
          ((d : ℝ) + 1) ^ r * (1 / ((n : ℝ) + 1)) := by
      intro j hj x
      calc
        _ ≤ ∑ i : Fin j → Fin d,
            |partialDeriv i
              ((gs n - h n : weightedTestSubmodule d r Pw) : Euc d → ℝ) x| :=
          HRS.MS.ToriCoefA.tca_norm_iteratedFDeriv_le_sum j _ x
        _ ≤ ∑ _i : Fin j → Fin d, 1 / ((n : ℝ) + 1) :=
          Finset.sum_le_sum fun i _ => hjet j hj i x
        _ = (d : ℝ) ^ j * (1 / ((n : ℝ) + 1)) := by simp
        _ ≤ ((d : ℝ) + 1) ^ r * (1 / ((n : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact (pow_le_pow_left₀ (Nat.cast_nonneg d) (by linarith) j).trans
            (pow_le_pow_right₀
              (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) hj)
    have hE := s57p_E_le_cb hP
      (B := ((d : ℝ) + 1) ^ r * (1 / ((n : ℝ) + 1)))
      (by positivity) hiter
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hE
    rw [ENNReal.toReal_ofReal
      (mul_nonneg (s57pC_nonneg _ _ _) (by positivity))] at hreal
    simpa only [A, mul_assoc] using hreal
  have hdiff : Tendsto (fun n => weightedJetMap d r Pw (gs n) -
      weightedJetMap d r Pw (h n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.2
    refine squeeze_zero (fun n => norm_nonneg _) hdif ?_
    simpa only [mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul A
  refine ⟨gs, hg, ?_⟩
  have hsum := hdiff.add ht
  simpa only [sub_add_cancel, zero_add] using hsum

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.weighted_compact_approximation
#print axioms HRS.MS.ProClosureS111.weighted_smooth_approximation

