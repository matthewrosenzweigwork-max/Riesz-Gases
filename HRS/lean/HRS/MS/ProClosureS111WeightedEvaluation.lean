import HRS.MS.ProClosureS111WeightedJets
import HRS.MS.FeatDecAux10
import HRS.MS.MovBridgeAux3
import HRS.MP.RdGenSob

/-!
Actual point and Hessian evaluation bounds for the frozen weighted norm.
The proof conjugates by the Japanese-bracket weight, controls every
derivative by the exact finite weighted jet vector, and uses the accepted
Euclidean integer Sobolev inequality. No evaluation bound or trace estimate
for a proposed chart is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.FixEq HRS.MS.S85 HRS.MS.MovOsc

variable {d r : ℕ} {Pw : ℝ}

theorem weighted_partial_le_jet (f : Euc d → ℝ) {j : ℕ} (hj : j ≤ r)
    (i : Fin j → Fin d) (x : Euc d) :
    jbracket x ^ (-Pw) * |partialDeriv i f x| ≤ ‖weightedJets r Pw f x‖ := by
  have h := PiLp.norm_apply_le (weightedJets r Pw f x)
    (⟨⟨j, Nat.lt_succ_of_le hj⟩, i⟩ : WeightedJetIndex d r)
  change |jbracket x ^ (-Pw) * partialDeriv i f x| ≤ _ at h
  simpa only [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (s57p_jbracket_pos x) _)] using h

theorem weighted_derivative_le_jet (f : Euc d → ℝ) {j : ℕ} (hj : j ≤ r)
    (x : Euc d) :
    jbracket x ^ (-Pw) * ‖iteratedFDeriv ℝ j f x‖ ≤
      (d : ℝ) ^ j * ‖weightedJets r Pw f x‖ := by
  calc
    _ ≤ jbracket x ^ (-Pw) *
        ∑ i : Fin j → Fin d, |partialDeriv i f x| :=
      mul_le_mul_of_nonneg_left (u2_opnorm_le_sum _)
        (Real.rpow_nonneg (s57p_jbracket_pos x).le _)
    _ = ∑ i : Fin j → Fin d,
        jbracket x ^ (-Pw) * |partialDeriv i f x| := Finset.mul_sum _ _ _
    _ ≤ ∑ _i : Fin j → Fin d, ‖weightedJets r Pw f x‖ :=
      Finset.sum_le_sum fun i _ => weighted_partial_le_jet f hj i x
    _ = _ := by simp

/-- Multiplication by the decaying weight sends all derivatives up to `r`
to functions dominated by one multiple of the actual weighted jet norm. -/
theorem weighted_conjugate_derivative_bound (d r : ℕ) (Pw : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : Euc d → ℝ, ContDiff ℝ r f →
      ∀ j ≤ r, ∀ x,
        ‖iteratedFDeriv ℝ j (fun y => jbracket y ^ (-Pw) * f y) x‖ ≤
          K * ‖weightedJets r Pw f x‖ := by
  choose! C hC0 hC using fun i (hi : i ≤ r) => s85_jb_sym (d := d) r i hi (-Pw)
  let K : ℝ := ∑ j ∈ Finset.range (r + 1),
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * C i * (d : ℝ) ^ (j - i)
  have hterm0 : ∀ j ≤ r, ∀ i ∈ Finset.range (j + 1),
      0 ≤ (j.choose i : ℝ) * C i * (d : ℝ) ^ (j - i) := by
    intro j hj i hi
    have hi' : i ≤ r := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hj
    have := hC0 i hi'
    positivity
  have hK : 0 ≤ K := Finset.sum_nonneg fun j hj =>
    Finset.sum_nonneg fun i hi => hterm0 j
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) i hi
  refine ⟨K, hK, fun f hf j hj x => ?_⟩
  have hw : ContDiff ℝ r (fun y : Euc d => jbracket y ^ (-Pw)) :=
    (s85_jbpow_contDiff (-Pw)).of_le (by exact_mod_cast le_top)
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ)
    (f := fun y : Euc d => jbracket y ^ (-Pw)) (g := f)
    (N := (r : WithTop ℕ∞)) hw hf x (n := j) (by exact_mod_cast hj)
  have hpoint : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y : Euc d => jbracket y ^ (-Pw)) x‖ *
        ‖iteratedFDeriv ℝ (j - i) f x‖ ≤
      ((j.choose i : ℝ) * C i * (d : ℝ) ^ (j - i)) *
        ‖weightedJets r Pw f x‖ := by
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hi' : i ≤ r := hij.trans hj
    have hw' : ‖iteratedFDeriv ℝ i
        (fun y : Euc d => jbracket y ^ (-Pw)) x‖ ≤
        C i * jbracket x ^ (-Pw) := by
      refine (hC i hi' x).trans (mul_le_mul_of_nonneg_left ?_ (hC0 i hi'))
      exact Real.rpow_le_rpow_of_exponent_le (s85_jb_one_le x)
        (by have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith)
    have hf' := weighted_derivative_le_jet (r := r) (Pw := Pw) f
      (j := j - i) (by omega) x
    calc
      _ ≤ (j.choose i : ℝ) * (C i * jbracket x ^ (-Pw)) *
          ‖iteratedFDeriv ℝ (j - i) f x‖ := by gcongr
      _ = ((j.choose i : ℝ) * C i) *
          (jbracket x ^ (-Pw) * ‖iteratedFDeriv ℝ (j - i) f x‖) := by ring
      _ ≤ ((j.choose i : ℝ) * C i) *
          ((d : ℝ) ^ (j - i) * ‖weightedJets r Pw f x‖) :=
        mul_le_mul_of_nonneg_left hf' (mul_nonneg (by positivity) (hC0 i hi'))
      _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1),
        ((j.choose i : ℝ) * C i * (d : ℝ) ^ (j - i)) *
          ‖weightedJets r Pw f x‖ := hmul.trans (Finset.sum_le_sum hpoint)
    _ = (∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * C i * (d : ℝ) ^ (j - i)) *
          ‖weightedJets r Pw f x‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ K * ‖weightedJets r Pw f x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact Finset.single_le_sum
        (fun j' hj' => Finset.sum_nonneg fun i hi =>
          hterm0 j' (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj')) i hi)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

theorem weightedJetMap_norm_sq (f : weightedTestSubmodule d r Pw) :
    ‖weightedJetMap d r Pw f‖ ^ 2 =
      ∫ x, ‖weightedJets r Pw (f : Euc d → ℝ) x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.property.2.coeFn_toLp] with x hx
  change inner ℝ ((f.property.2.toLp (weightedJets r Pw f)) x)
      ((f.property.2.toLp (weightedJets r Pw f)) x) = _
  rw [hx, real_inner_self_eq_norm_sq]

/-- The exact weighted norm controls the ordinary Sobolev norm of the
conjugated compact smooth test. This is the physical Sobolev input, proved
from the finite ordered jets rather than assumed. -/
theorem weighted_conjugate_sobolev_bound (d r : ℕ) (Pw : ℝ)
    (hP : (d : ℝ) < 2 * Pw) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, IsR2Test f →
      HRS.PDE.ToolboxRd.MemSobolev (r : ℝ)
        (fun x => jbracket x ^ (-Pw) * f x) ∧
      HRS.Whole.sobolevNorm (r : ℝ) (fun x => jbracket x ^ (-Pw) * f x) ≤
        C * (weightedSobolevE r Pw f).toReal := by
  obtain ⟨K, hK, hbound⟩ := weighted_conjugate_derivative_bound d r Pw
  let C : ℝ := Real.sqrt (((d : ℝ) + 1) ^ (r + 1)) * K
  refine ⟨C, mul_nonneg (Real.sqrt_nonneg _) hK, fun f hf => ?_⟩
  let fw : weightedTestSubmodule d r Pw :=
    ⟨f, weighted_test_of_compact_smooth hP hf⟩
  let u : Euc d → ℝ := fun x => jbracket x ^ (-Pw) * f x
  have huf : ContDiff ℝ ∞ u := (s85_jbpow_contDiff (-Pw)).mul hf.1
  have hbr : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤
      K * ‖weightedJets r Pw f x‖ :=
    hbound f (hf.1.of_le (by exact_mod_cast le_top))
  have hjmem : MemLp (weightedJets r Pw f) 2 volume := fw.property.2
  have hiJ : Integrable (fun x => ‖weightedJets r Pw f x‖ ^ 2) :=
    hjmem.integrable_norm_pow (by norm_num)
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
    rw [mova3b1_Dj_iter_apply j m (huf.of_le (by exact_mod_cast le_top)) x]
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
      (mova3b1_Dj_iter_contDiff j m
        (show ContDiff ℝ ((0 : ℕ) + m : ℕ) u from
          huf.of_le (by exact_mod_cast le_top))).continuous
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
  obtain ⟨hSob, hSobBd⟩ := mova3b1_sobolev_bound r
    (huf.of_le (by exact_mod_cast le_top)) hDL huL
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
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        rw [pow_succ]
        ring
  have hn : HRS.Whole.sobolevNorm (r : ℝ) u ≤ C * ‖weightedJetMap d r Pw fw‖ :=
    Real.sqrt_le_iff.2 ⟨mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hK)
      (norm_nonneg _), hsq⟩
  simpa only [weightedJetMap_norm] using hn

/-- Point and Hessian evaluation are bounded by the exact frozen weighted
norm with the expected polynomial weight. The constant is chosen before
the test and the spatial point. -/
theorem weighted_test_jet_evaluation (d r : ℕ) (Pw : ℝ)
    (hr : (2 : ℝ) + (d : ℝ) / 2 < r) (hP : (d : ℝ) < 2 * Pw) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, IsR2Test f →
      ∀ j ≤ 2, ∀ x,
        ‖iteratedFDeriv ℝ j f x‖ ≤
          C * jbracket x ^ Pw * (weightedSobolevE r Pw f).toReal := by
  obtain ⟨C0, hC0, hSob⟩ := weighted_conjugate_sobolev_bound d r Pw hP
  choose! Cs hCs0 hCs using fun j (hj : j ≤ 2) =>
    HRS.MP.RdGen.rg_sobolev_embedding (d := d) j (q := (r : ℝ))
      (by
        have hj' : (j : ℝ) ≤ 2 := by exact_mod_cast hj
        linarith [hr])
  let D : ℝ := ∑ j ∈ Finset.range 3, Cs j
  have hD : 0 ≤ D := Finset.sum_nonneg fun j hj =>
    hCs0 j (by have := Finset.mem_range.1 hj; omega)
  have hCsD : ∀ j ≤ 2, Cs j ≤ D := fun j hj =>
    Finset.single_le_sum
      (fun k hk => hCs0 k (by have := Finset.mem_range.1 hk; omega))
      (Finset.mem_range.2 (by omega))
  obtain ⟨Ku, hKu, hUnweight⟩ := s85_unweight (d := d) (E := ℝ) 2 (-Pw)
  refine ⟨Ku * D * C0, by positivity, fun f hf j hj x => ?_⟩
  obtain ⟨hmem, hnorm⟩ := hSob f hf
  have hwf : ContDiff ℝ ∞ (fun y : Euc d => jbracket y ^ (-Pw) * f y) :=
    (s85_jbpow_contDiff (-Pw)).mul hf.1
  have hB : ∀ k ≤ 2, ∀ y,
      ‖iteratedFDeriv ℝ k (fun z => jbracket z ^ (-Pw) • f z) y‖ ≤
        D * C0 * (weightedSobolevE r Pw f).toReal := by
    intro k hk y
    change ‖iteratedFDeriv ℝ k (fun z => jbracket z ^ (-Pw) * f z) y‖ ≤ _
    calc
      _ ≤ Cs k * HRS.Whole.sobolevNorm (r : ℝ)
          (fun z => jbracket z ^ (-Pw) * f z) := hCs k hk _ hwf hmem y
      _ ≤ D * (C0 * (weightedSobolevE r Pw f).toReal) :=
        mul_le_mul (hCsD k hk) hnorm (Real.sqrt_nonneg _) hD
      _ = _ := by ring
  have hu := hUnweight f (D * C0 * (weightedSobolevE r Pw f).toReal)
    (hf.1.of_le (by simp)) hB j hj x
  calc
    ‖iteratedFDeriv ℝ j f x‖ = jbracket x ^ Pw *
        (jbracket x ^ (-Pw) * ‖iteratedFDeriv ℝ j f x‖) := by
      rw [← mul_assoc, ← Real.rpow_add (s57p_jbracket_pos x)]
      simp
    _ ≤ jbracket x ^ Pw * (Ku *
        (D * C0 * (weightedSobolevE r Pw f).toReal)) :=
      mul_le_mul_of_nonneg_left hu (Real.rpow_nonneg (s57p_jbracket_pos x).le _)
    _ = _ := by ring

#print axioms weighted_conjugate_sobolev_bound
#print axioms weighted_test_jet_evaluation

end HRS.MS.ProClosureS111
