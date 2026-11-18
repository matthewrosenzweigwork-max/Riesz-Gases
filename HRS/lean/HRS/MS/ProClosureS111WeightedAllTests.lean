import HRS.MS.ProClosureS111WeightedEvaluation
import HRS.MS.ThCorrSAux1

/-!
Weighted evaluation on the entire frozen finite-norm C^r domain. The
conjugated function is only C^r; the accepted Sobolev representative
theorem supplies a Cb2 representative, and continuity identifies that
representative with the original function at every point. Constants,
and differences of compact chart sections from constants, are therefore
within the actual proved domain.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.FixEq HRS.MS.S85 HRS.MS.MovOsc

variable {d r : ℕ} {Pw : ℝ}

/-- The exact finite weighted-jet norm controls the ordinary Sobolev
norm of the conjugated function for every frozen weighted test. -/
theorem weighted_conjugate_sobolev_bound_all (d r : ℕ) (Pw : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, IsR2WeightedTest r Pw f →
      HRS.PDE.ToolboxRd.MemSobolev (r : ℝ)
        (fun x : Euc d => jbracket x ^ (-Pw) * f x) ∧
      HRS.Whole.sobolevNorm (r : ℝ)
        (fun x : Euc d => jbracket x ^ (-Pw) * f x) ≤
        C * (weightedSobolevE r Pw f).toReal := by
  obtain ⟨K, hK, hbound⟩ := weighted_conjugate_derivative_bound d r Pw
  let C : ℝ := Real.sqrt (((d : ℝ) + 1) ^ (r + 1)) * K
  refine ⟨C, mul_nonneg (Real.sqrt_nonneg _) hK, fun f hf => ?_⟩
  let fw : weightedTestSubmodule d r Pw := ⟨f, weightedTestSubmodule_iff.2 hf⟩
  let u : Euc d → ℝ := fun x => jbracket x ^ (-Pw) * f x
  have huf : ContDiff ℝ r u :=
    ((s85_jbpow_contDiff (-Pw)).of_le (by exact_mod_cast le_top)).mul hf.1
  have hbr : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤
      K * ‖weightedJets r Pw f x‖ := hbound f hf.1
  have hjmem : MemLp (weightedJets r Pw f) 2 volume := fw.property.2
  have hiJ : Integrable (fun x => ‖weightedJets r Pw f x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hjmem.aestronglyMeasurable).1 hjmem
  have hupt : ∀ x, ‖u x‖ ≤ K * ‖weightedJets r Pw f x‖ := by
    intro x
    simpa only [norm_iteratedFDeriv_zero] using hbr 0 (Nat.zero_le _) x
  have huL : MemLp u 2 volume :=
    (hjmem.norm.const_mul K).of_le huf.continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK,
          abs_of_nonneg (norm_nonneg _)] using hupt x)
  have hDpt : ∀ j : Fin d, ∀ m ≤ r, ∀ x,
      |((mova3b1_Dj j)^[m] u) x| ≤ K * ‖weightedJets r Pw f x‖ := by
    intro j m hm x
    rw [mova3b1_Dj_iter_apply j m (huf.of_le (by exact_mod_cast hm)) x]
    have h := (iteratedFDeriv ℝ m u x).le_opNorm
      (fun _ => EuclideanSpace.single j (1 : ℝ))
    have hn : |iteratedFDeriv ℝ m u x
        (fun _ => EuclideanSpace.single j (1 : ℝ))| ≤
        ‖iteratedFDeriv ℝ m u x‖ := by simpa using h
    exact hn.trans (hbr m hm x)
  have hDL : ∀ j : Fin d, ∀ m ≤ r,
      MemLp ((mova3b1_Dj j)^[m] u) 2 volume := by
    intro j m hm
    have hc : Continuous ((mova3b1_Dj j)^[m] u) :=
      (mova3b1_Dj_iter_contDiff j m (k := 0)
        (huf.of_le (by exact_mod_cast (show 0 + m ≤ r by omega)))).continuous
    refine (hjmem.norm.const_mul K).of_le hc.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK,
      abs_of_nonneg (norm_nonneg _)] using hDpt j m hm x
  have hInt : ∀ v : Euc d → ℝ, MemLp v 2 volume →
      (∀ x, |v x| ≤ K * ‖weightedJets r Pw f x‖) →
      (∫ x, v x ^ 2) ≤ K ^ 2 * ‖weightedJetMap d r Pw fw‖ ^ 2 := by
    intro v hv hvb
    calc
      _ ≤ ∫ x, K ^ 2 * ‖weightedJets r Pw f x‖ ^ 2 := by
        refine integral_mono hv.integrable_sq (hiJ.const_mul _) fun x => ?_
        have hsq := pow_le_pow_left₀ (abs_nonneg _) (hvb x) 2
        simpa only [sq_abs, mul_pow] using hsq
      _ = K ^ 2 * ‖weightedJetMap d r Pw fw‖ ^ 2 := by
        rw [integral_const_mul, weightedJetMap_norm_sq]
  have huInt := hInt u huL (by simpa only [Real.norm_eq_abs] using hupt)
  have hDInt : ∀ j : Fin d,
      (∫ x, ((mova3b1_Dj j)^[r] u x) ^ 2) ≤
        K ^ 2 * ‖weightedJetMap d r Pw fw‖ ^ 2 :=
    fun j => hInt _ (hDL j r le_rfl) (hDpt j r le_rfl)
  obtain ⟨hSob, hSobBd⟩ := mova3b1_sobolev_bound r huf hDL huL
  refine ⟨hSob, ?_⟩
  have hsum : (∑ j : Fin d, ∫ x, ((mova3b1_Dj j)^[r] u x) ^ 2) ≤
      (d : ℝ) * (K ^ 2 * ‖weightedJetMap d r Pw fw‖ ^ 2) := by
    calc
      _ ≤ ∑ _j : Fin d, K ^ 2 * ‖weightedJetMap d r Pw fw‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => hDInt j
      _ = _ := by simp
  have hsq : HRS.PDE.ToolboxRd.sobolevNormSq (r : ℝ) u ≤
      (C * ‖weightedJetMap d r Pw fw‖) ^ 2 := by
    calc
      _ ≤ ((d : ℝ) + 1) ^ r *
          ((∫ x, u x ^ 2) + ∑ j : Fin d, ∫ x, ((mova3b1_Dj j)^[r] u x) ^ 2) := hSobBd
      _ ≤ ((d : ℝ) + 1) ^ r *
          (K ^ 2 * ‖weightedJetMap d r Pw fw‖ ^ 2 +
            (d : ℝ) * (K ^ 2 * ‖weightedJetMap d r Pw fw‖ ^ 2)) := by gcongr
      _ = _ := by
        dsimp [C]
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), pow_succ]
        ring
  have hn : HRS.Whole.sobolevNorm (r : ℝ) u ≤ C * ‖weightedJetMap d r Pw fw‖ :=
    Real.sqrt_le_iff.2 ⟨mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK)
      (norm_nonneg _), hsq⟩
  simpa only [weightedJetMap_norm] using hn

/-- Point, gradient, and Hessian evaluation on every finite-norm C^r
weighted test. Smooth compact support is not a premise. -/
theorem weighted_jet_evaluation_all (d r : ℕ) (Pw : ℝ)
    (hr : (2 : ℝ) + (d : ℝ) / 2 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, IsR2WeightedTest r Pw f →
      ∀ j ≤ 2, ∀ x,
        ‖iteratedFDeriv ℝ j f x‖ ≤
          C * jbracket x ^ Pw * (weightedSobolevE r Pw f).toReal := by
  obtain ⟨C0, hC0, hSob⟩ := weighted_conjugate_sobolev_bound_all d r Pw
  obtain ⟨Cs, hCs, hrep⟩ := HRS.MS.TcS.tcs_rep (d := d) 2 (q := (r : ℝ)) hr
  obtain ⟨Ku, hKu, hUnweight⟩ := s85_unweight (d := d) (E := ℝ) 2 (-Pw)
  have hr2 : 2 ≤ r := by
    have hdd : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    have hrr : (2 : ℝ) ≤ r := by linarith
    exact_mod_cast hrr
  refine ⟨Ku * Cs * C0, by positivity, fun f hf j hj x => ?_⟩
  let u : Euc d → ℝ := fun y => jbracket y ^ (-Pw) * f y
  obtain ⟨hmem, hnorm⟩ := hSob f hf
  obtain ⟨R, hR, hReq, hRn⟩ := hrep u hmem
  have huc : Continuous u := by
    exact ((s85_jbpow_contDiff (-Pw)).continuous.mul hf.1.continuous)
  have he : R = u := (Continuous.ae_eq_iff_eq volume hR.1.continuous huc).1 hReq
  rw [he] at hR hRn
  change cbNorm 2 u ≤ Cs * HRS.Whole.sobolevNorm (r : ℝ) u at hRn
  have hB : ∀ k ≤ 2, ∀ y,
      ‖iteratedFDeriv ℝ k (fun z => jbracket z ^ (-Pw) • f z) y‖ ≤
        Cs * C0 * (weightedSobolevE r Pw f).toReal := by
    intro k hk y
    change ‖iteratedFDeriv ℝ k u y‖ ≤ _
    exact (chart_derivative_le_cbNorm hR hk y).trans
      (hRn.trans ((mul_le_mul_of_nonneg_left hnorm hCs).trans_eq (by ring)))
  have hu := hUnweight f (Cs * C0 * (weightedSobolevE r Pw f).toReal)
    (hf.1.of_le (by exact_mod_cast hr2)) hB j hj x
  calc
    ‖iteratedFDeriv ℝ j f x‖ = jbracket x ^ Pw *
        (jbracket x ^ (-Pw) * ‖iteratedFDeriv ℝ j f x‖) := by
      rw [← mul_assoc, ← Real.rpow_add (s57p_jbracket_pos x)]
      simp
    _ ≤ jbracket x ^ Pw * (Ku *
        (Cs * C0 * (weightedSobolevE r Pw f).toReal)) :=
      mul_le_mul_of_nonneg_left hu (Real.rpow_nonneg (s57p_jbracket_pos x).le _)
    _ = _ := by ring

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.weighted_conjugate_sobolev_bound_all
#print axioms HRS.MS.ProClosureS111.weighted_jet_evaluation_all
