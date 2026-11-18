import HRS.MS.ProClosureS111WeightedJets
import HRS.MS.ToriCoefAAux1

/-!
Cutoff approximation for every finite-norm weighted test. The pointwise
majorant is the original weighted jet vector, so no global boundedness of
the uncut function or of its derivatives is imposed.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.FixEq

variable {d r : ℕ} {Pw : ℝ}

theorem finite_euclidean_norm_le {I : Type*} [Fintype I]
    (z : EuclideanSpace ℝ I) {B : ℝ} (hB : 0 ≤ B)
    (hz : ∀ i, ‖z i‖ ≤ B) : ‖z‖ ≤ ((Fintype.card I : ℝ) + 1) * B := by
  have hsq : ‖z‖ ^ 2 ≤ (Fintype.card I : ℝ) * B ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _i : I, B ^ 2 := Finset.sum_le_sum fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hz i) 2
      _ = _ := by simp
  have hc : (Fintype.card I : ℝ) ≤ ((Fintype.card I : ℝ) + 1) ^ 2 := by
    nlinarith [(Nat.cast_nonneg (Fintype.card I) : (0 : ℝ) ≤ Fintype.card I),
      sq_nonneg (Fintype.card I : ℝ)]
  have hsq' : ‖z‖ ^ 2 ≤ (((Fintype.card I : ℝ) + 1) * B) ^ 2 :=
    hsq.trans ((mul_le_mul_of_nonneg_right hc (sq_nonneg B)).trans_eq (by ring))
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) hB)).1 hsq'

theorem weighted_partial_le_jets (f : Euc d → ℝ) {j : ℕ}
    (hj : j ≤ r) (i : Fin j → Fin d) (x : Euc d) :
    jbracket x ^ (-Pw) * |partialDeriv i f x| ≤ ‖weightedJets r Pw f x‖ := by
  have h := PiLp.norm_apply_le (weightedJets r Pw f x)
    (⟨⟨j, Nat.lt_succ_of_le hj⟩, i⟩ : WeightedJetIndex d r)
  change ‖jbracket x ^ (-Pw) * partialDeriv i f x‖ ≤ _ at h
  simpa only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (s57p_jbracket_pos x).le _)] using h

theorem weighted_iterated_le_jets (f : Euc d → ℝ) {j : ℕ}
    (hj : j ≤ r) (x : Euc d) :
    jbracket x ^ (-Pw) * ‖iteratedFDeriv ℝ j f x‖ ≤
      ((d : ℝ) + 1) ^ r * ‖weightedJets r Pw f x‖ := by
  calc
    _ ≤ jbracket x ^ (-Pw) * ∑ i : Fin j → Fin d, |partialDeriv i f x| :=
      mul_le_mul_of_nonneg_left
        (HRS.MS.ToriCoefA.tca_norm_iteratedFDeriv_le_sum j f x)
        (Real.rpow_nonneg (s57p_jbracket_pos x).le _)
    _ = ∑ i : Fin j → Fin d, jbracket x ^ (-Pw) * |partialDeriv i f x| := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _i : Fin j → Fin d, ‖weightedJets r Pw f x‖ :=
      Finset.sum_le_sum fun i _ => weighted_partial_le_jets f hj i x
    _ = (d : ℝ) ^ j * ‖weightedJets r Pw f x‖ := by simp
    _ ≤ ((d : ℝ) + 1) ^ r * ‖weightedJets r Pw f x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (pow_le_pow_left₀ (Nat.cast_nonneg d) (by linarith) j).trans
        (pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) hj)

/-- One sequence of compact C^r cutoffs converges locally to the original
test, with all weighted jets dominated by a fixed multiple of its own
weighted jet vector. -/
theorem weighted_cutoff_family {f : Euc d → ℝ} (hf : ContDiff ℝ r f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ h : ℕ → Euc d → ℝ,
      (∀ n, ContDiff ℝ r (h n) ∧ HasCompactSupport (h n)) ∧
      (∀ n x, ‖weightedJets r Pw (h n) x‖ ≤ K * ‖weightedJets r Pw f x‖) ∧
      ∀ (n : ℕ) (x : Euc d), ‖x‖ < (n : ℝ) + 1 → h n =ᶠ[𝓝 x] f := by
  obtain ⟨chi, hchi, hchis, hchi1, C, hC, hCb⟩ := s57p_cutoff (d := d) r
  let chiR : ℕ → Euc d → ℝ := fun n x => chi (((n : ℝ) + 1)⁻¹ • x)
  let h : ℕ → Euc d → ℝ := fun n x => chiR n x * f x
  have hR : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hcs : ∀ n, ContDiff ℝ ∞ (chiR n) := fun n => hchi.comp (contDiff_const_smul _)
  have hcc : ∀ n, HasCompactSupport (chiR n) := fun n =>
    hchis.comp_smul (inv_ne_zero (hR n).ne')
  have hcb : ∀ n, ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (chiR n) x‖ ≤ C := by
    intro n j hj x
    have he := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := j)
      (f := chi) ((n : ℝ) + 1)⁻¹ (hchi.of_le (by exact_mod_cast le_top))
    rw [show chiR n = fun y => chi (((n : ℝ) + 1)⁻¹ • y) from rfl, he]
    simp only [norm_smul, norm_pow, norm_inv, Real.norm_eq_abs, abs_of_pos (hR n)]
    have hp : (((n : ℝ) + 1)⁻¹) ^ j ≤ 1 :=
      pow_le_one₀ (inv_nonneg.2 (hR n).le)
        (inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
    exact (mul_le_mul hp (hCb j hj _) (norm_nonneg _) zero_le_one).trans_eq (one_mul C)
  let A : ℝ := 2 ^ r * (C * ((d : ℝ) + 1) ^ r)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hjh : ∀ n, ∀ j ≤ r, ∀ x,
      jbracket x ^ (-Pw) * ‖iteratedFDeriv ℝ j (h n) x‖ ≤
        A * ‖weightedJets r Pw f x‖ := by
    intro n j hj x
    have hw : 0 ≤ jbracket x ^ (-Pw) := Real.rpow_nonneg (s57p_jbracket_pos x).le _
    have hm := norm_iteratedFDeriv_mul_le (𝕜 := ℝ)
      (f := chiR n) (g := f) (N := (r : WithTop ℕ∞))
      ((hcs n).of_le (by exact_mod_cast le_top)) hf x (n := j) (by exact_mod_cast hj)
    calc
      _ ≤ jbracket x ^ (-Pw) * ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (chiR n) x‖ *
            ‖iteratedFDeriv ℝ (j - i) f x‖ := mul_le_mul_of_nonneg_left hm hw
      _ = ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * (‖iteratedFDeriv ℝ i (chiR n) x‖ *
            (jbracket x ^ (-Pw) * ‖iteratedFDeriv ℝ (j - i) f x‖)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ ≤ ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * (C * (((d : ℝ) + 1) ^ r * ‖weightedJets r Pw f x‖)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact mul_le_mul (hcb n i (hij.trans hj) x)
            (weighted_iterated_le_jets f ((Nat.sub_le j i).trans hj) x)
            (mul_nonneg hw (norm_nonneg _)) hC
      _ = 2 ^ j * (C * (((d : ℝ) + 1) ^ r * ‖weightedJets r Pw f x‖)) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose j
      _ ≤ 2 ^ r * (C * (((d : ℝ) + 1) ^ r * ‖weightedJets r Pw f x‖)) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (by positivity)
      _ = _ := by dsimp [A]; ring
  refine ⟨((Fintype.card (WeightedJetIndex d r) : ℝ) + 1) * A,
    mul_nonneg (by positivity) hA, h, ?_, ?_, ?_⟩
  · intro n
    exact ⟨((hcs n).of_le (by exact_mod_cast le_top)).mul hf, (hcc n).mul_right⟩
  · intro n x
    have hc : ∀ p : WeightedJetIndex d r,
        ‖weightedJets r Pw (h n) x p‖ ≤ A * ‖weightedJets r Pw f x‖ := by
      intro p
      change ‖jbracket x ^ (-Pw) * partialDeriv p.2 (h n) x‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (s57p_jbracket_pos x).le _)]
      exact (mul_le_mul_of_nonneg_left (s57p_abs_partialDeriv_le p.2 (h n) x)
        (Real.rpow_nonneg (s57p_jbracket_pos x).le _)).trans
        (hjh n p.1 (Nat.lt_succ_iff.1 p.1.isLt) x)
    simpa only [mul_assoc] using finite_euclidean_norm_le
      (weightedJets r Pw (h n) x) (mul_nonneg hA (norm_nonneg _)) hc
  · intro n x hx
    have hev : ∀ᶠ y in 𝓝 x, ‖y‖ < (n : ℝ) + 1 :=
      (isOpen_lt continuous_norm continuous_const).mem_nhds hx
    filter_upwards [hev] with y hy
    have he : chiR n y = 1 := by
      apply hchi1
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hR n),
        inv_mul_le_iff₀ (hR n)]
      simpa only [mul_one] using hy.le
    simp only [h, he, one_mul]

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.weighted_cutoff_family

