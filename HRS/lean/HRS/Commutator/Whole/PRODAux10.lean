import HRS.Commutator.Whole.PRODAux9

/-!
# CMX-PROD helper file 10: measurability from the Bessel pairing, exponent identities
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.PROD

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

/-- A function that is locally integrable against every Schwartz function is a.e. strongly
measurable. -/
lemma prod_aesm_of_integrable_mul {W : Euc d → ℂ}
    (h : ∀ φ : SchwartzMap (Euc d) ℂ, Integrable (fun x => W x * φ x)) :
    AEStronglyMeasurable W volume := by
  have key : ∀ R : ℕ, AEStronglyMeasurable W (volume.restrict (closedBall (0 : Euc d) R)) := by
    intro R
    let b : ContDiffBump (0 : Euc d) := ⟨(R : ℝ) + 1, (R : ℝ) + 2, by positivity, by linarith⟩
    have hc : HasCompactSupport (fun x : Euc d => ((b x : ℝ) : ℂ)) :=
      b.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    have hs : ContDiff ℝ ∞ (fun x : Euc d => ((b x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp b.contDiff
    let ψ : SchwartzMap (Euc d) ℂ := hc.toSchwartzMap hs
    have h1 := ((h ψ).aestronglyMeasurable).restrict (s := closedBall (0 : Euc d) R)
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    have hb : b x = 1 := by
      apply b.one_of_mem_closedBall
      have := mem_closedBall_zero_iff.1 hx
      simp only [b, mem_closedBall_zero_iff]
      linarith
    show W x * ((b x : ℝ) : ℂ) = W x
    rw [hb]; simp
  have := aestronglyMeasurable_iUnion_iff.2 key
  rwa [iUnion_closedBall_nat, Measure.restrict_univ] at this

/-- The exponent identity `1/p₁ + 1/p₂ = 1/2`. -/
lemma prod_exponent_identity (hd : 3 ≤ d) {s : ℝ} (hsd : s < (d : ℝ) - 2) (hs0 : 0 ≤ s) :
    (ENNReal.ofReal (p1E d s))⁻¹ + (ENNReal.ofReal (p2E d s))⁻¹ = 2⁻¹ := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 < (d : ℝ) - s - 2 := by linarith
  have h2 : 0 < s + 2 := by linarith
  have hP0 : 0 < p1E d s := by unfold p1E; positivity
  have hQ0 : 0 < p2E d s := by unfold p2E; positivity
  rw [← ENNReal.ofReal_inv_of_pos hP0, ← ENNReal.ofReal_inv_of_pos hQ0,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have : (p1E d s)⁻¹ + (p2E d s)⁻¹ = (2 : ℝ)⁻¹ := by
    unfold p1E p2E
    field_simp
    ring
  rw [this, ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

lemma prod_p2_gt_one (hd : 3 ≤ d) {s : ℝ} (hsd : s < (d : ℝ) - 2) (hs0 : 0 ≤ s) : 1 < p2E d s := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold p2E
  rw [lt_div_iff₀ (by linarith)]
  linarith

end HRS.Commutator.Whole.PROD
