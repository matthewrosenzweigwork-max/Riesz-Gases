import HRS.MS.Fp81S21WeightedRellich10
import HRS.MS.ProClosureS111WeightedEvaluation

/-!
For the weighted chart norm, the relevant local size is the L² norm of its
ordered weighted jets.  This file turns the uniform pointwise Leibniz bound
for a scaled cutoff into a bound on that L² jet norm.  The constant depends
on the derivative bound for the cutoff and on the finite jet dimensions,
but not on its spatial radius.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.FixEq

/-- A uniformly bounded smooth multiplier acts boundedly on each frozen
weighted ordered-jet space.  The operator bound is stated through the
common derivative bound `C`, so scaled cutoffs from the preceding file have
one bound independent of the radius. -/
theorem fp81s21_weightedRellich_cutoff_product_energy_le
    {d q : ℕ} {P C : ℝ} {χ f : Euc d → ℝ}
    (hC : 0 ≤ C)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hχB : ∀ k ≤ q + 2, ∀ x,
      ‖iteratedFDeriv ℝ k χ x‖ ≤ C) :
    weightedSobolevE (q + 2) P (fun x => χ x * f x) ≤
      ENNReal.ofReal
        (((Fintype.card (HRS.MS.ProClosureS111.WeightedJetIndex d (q + 2)) : ℝ) + 1) *
          (∑ j ∈ Finset.range (q + 3),
            ∑ k ∈ Finset.range (j + 1),
              (j.choose k : ℝ) * C * (d : ℝ) ^ (j - k))) *
        weightedSobolevE (q + 2) P f := by
  let L : ℝ := ∑ j ∈ Finset.range (q + 3),
    ∑ k ∈ Finset.range (j + 1),
      (j.choose k : ℝ) * C * (d : ℝ) ^ (j - k)
  let N : ℝ := (Fintype.card
    (HRS.MS.ProClosureS111.WeightedJetIndex d (q + 2)) : ℝ) + 1
  let K : ℝ := N * L
  have hcoeff : ∀ j, ∀ k ∈ Finset.range (j + 1),
      0 ≤ (j.choose k : ℝ) * C * (d : ℝ) ^ (j - k) := by
    intro j k hk
    positivity
  have hL : 0 ≤ L := by
    dsimp [L]
    refine Finset.sum_nonneg fun j hj => ?_
    exact Finset.sum_nonneg fun k hk => hcoeff j k hk
  have hK : 0 ≤ K := by
    dsimp [K, N]
    exact mul_nonneg (by positivity) hL
  have hlocalCoeff : ∀ j ≤ q + 2,
      (∑ k ∈ Finset.range (j + 1),
        (j.choose k : ℝ) * C * (d : ℝ) ^ (j - k)) ≤ L := by
    intro j hj
    dsimp [L]
    have hjmem : j ∈ Finset.range (q + 3) := by
      simp only [Finset.mem_range]
      omega
    refine Finset.single_le_sum
      (f := fun j' => ∑ k ∈ Finset.range (j' + 1),
        (j'.choose k : ℝ) * C * (d : ℝ) ^ (j' - k)) ?_ hjmem
    intro j' hj'
    exact Finset.sum_nonneg fun k hk => hcoeff j' k hk
  have hcoord : ∀ j ≤ q + 2, ∀ i : Fin j → Fin d, ∀ x,
      jbracket x ^ (-P) *
        |partialDeriv i (fun y => χ y * f y) x| ≤
          L * ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖ := by
    intro j hj i x
    have hprod := fp81s21_weightedRellich_productDerivative_bound
      hχ hf hC hχB j hj i x
    have hwpos : 0 < jbracket x ^ (-P) :=
      Real.rpow_pos_of_pos (s57p_jbracket_pos x) _
    have hsum : jbracket x ^ (-P) *
        (∑ k ∈ Finset.range (j + 1),
          (j.choose k : ℝ) *
            (C * ‖iteratedFDeriv ℝ (j - k) f x‖)) ≤
          L * ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖ := by
      calc
        _ = ∑ k ∈ Finset.range (j + 1),
            (j.choose k : ℝ) * C *
              (jbracket x ^ (-P) *
                ‖iteratedFDeriv ℝ (j - k) f x‖) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k hk => ?_
              ring
        _ ≤ ∑ k ∈ Finset.range (j + 1),
            (j.choose k : ℝ) * C *
              ((d : ℝ) ^ (j - k) *
                ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖) := by
              refine Finset.sum_le_sum fun k hk => ?_
              have hk' : k ≤ j := by
                exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
              have hmk : j - k ≤ q + 2 := (Nat.sub_le j k).trans hj
              have hder := HRS.MS.ProClosureS111.weighted_derivative_le_jet
                (r := q + 2) (Pw := P) f hmk x
              have hnonneg : 0 ≤ (j.choose k : ℝ) * C := by positivity
              calc
                (j.choose k : ℝ) * C *
                    (jbracket x ^ (-P) *
                      ‖iteratedFDeriv ℝ (j - k) f x‖)
                  ≤ (j.choose k : ℝ) * C *
                    ((d : ℝ) ^ (j - k) *
                      ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖) :=
                    mul_le_mul_of_nonneg_left hder hnonneg
                _ = _ := by ring
        _ = (∑ k ∈ Finset.range (j + 1),
              (j.choose k : ℝ) * C * (d : ℝ) ^ (j - k)) *
              ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖ := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun k hk => ?_
              ring
        _ ≤ L * ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖ :=
            mul_le_mul_of_nonneg_right (hlocalCoeff j hj) (norm_nonneg _)
    exact (mul_le_mul_of_nonneg_left hprod hwpos.le).trans hsum
  have hg : ContDiff ℝ (q + 2) (fun x => χ x * f x) :=
    (hχ.mul hf).of_le (by simp)
  have hf' : ContDiff ℝ (q + 2) f := hf.of_le (by simp)
  have hjet : ∀ x,
      ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P
          (fun y => χ y * f y) x‖ ≤
        K * ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖ := by
    intro x
    let A : ℝ := L *
      ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖
    have hA : 0 ≤ A := mul_nonneg hL (norm_nonneg _)
    have hterm : ∀ p : HRS.MS.ProClosureS111.WeightedJetIndex d (q + 2),
        (jbracket x ^ (-2 * P)) *
          (partialDeriv p.2 (fun y => χ y * f y) x) ^ 2 ≤ A ^ 2 := by
      intro p
      have hj : p.1.1 ≤ q + 2 := Nat.lt_succ_iff.mp p.1.2
      have hcp := hcoord p.1.1 hj p.2 x
      have hweight : (jbracket x ^ (-P)) ^ 2 = jbracket x ^ (-2 * P) := by
        rw [← Real.rpow_two, ← Real.rpow_mul (s57p_jbracket_pos x).le]
        congr 1
        ring
      have hcp' : jbracket x ^ (-P) *
          |partialDeriv p.2 (fun y => χ y * f y) x| ≤ A := by
        simpa [A] using hcp
      have hcp0 : 0 ≤ jbracket x ^ (-P) *
          |partialDeriv p.2 (fun y => χ y * f y) x| :=
        mul_nonneg (Real.rpow_nonneg (s57p_jbracket_pos x).le _)
          (abs_nonneg _)
      have hsq := mul_le_mul hcp' hcp' hcp0 hA
      calc
        _ = (jbracket x ^ (-P) *
            |partialDeriv p.2 (fun y => χ y * f y) x|) ^ 2 := by
              rw [← hweight, mul_pow, sq_abs]
        _ ≤ A ^ 2 := by simpa [pow_two] using hsq
    have hsumSq :
        ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P
            (fun y => χ y * f y) x‖ ^ 2 ≤
          (Fintype.card
            (HRS.MS.ProClosureS111.WeightedJetIndex d (q + 2)) : ℝ) * A ^ 2 := by
      rw [HRS.MS.ProClosureS111.weightedJets_norm_sq]
      calc
        _ ≤ ∑ _p : HRS.MS.ProClosureS111.WeightedJetIndex d (q + 2), A ^ 2 :=
          Finset.sum_le_sum fun p hp => hterm p
        _ = (Fintype.card
            (HRS.MS.ProClosureS111.WeightedJetIndex d (q + 2)) : ℝ) * A ^ 2 := by
          simp
    have hcard :
        (Fintype.card
          (HRS.MS.ProClosureS111.WeightedJetIndex d (q + 2)) : ℝ) ≤ N ^ 2 := by
      dsimp [N]
      have hn : 0 ≤ (Fintype.card
        (HRS.MS.ProClosureS111.WeightedJetIndex d (q + 2)) : ℝ) := by positivity
      nlinarith
    have hsq :
        ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P
            (fun y => χ y * f y) x‖ ^ 2 ≤
          (N * A) ^ 2 := by
      calc
        _ ≤ (Fintype.card
            (HRS.MS.ProClosureS111.WeightedJetIndex d (q + 2)) : ℝ) * A ^ 2 := hsumSq
        _ ≤ N ^ 2 * A ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg A)
        _ = (N * A) ^ 2 := by ring
    have hNA : 0 ≤ N * A := by
      apply mul_nonneg
      · dsimp [N]
        positivity
      · exact hA
    have hnorm_le :
        ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P
            (fun y => χ y * f y) x‖ ≤ N * A := by
      by_contra hnot
      have hlt : N * A <
          ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P
            (fun y => χ y * f y) x‖ := lt_of_not_ge hnot
      have hplus : 0 < N * A +
          ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P
            (fun y => χ y * f y) x‖ := by
        linarith [hNA, norm_nonneg (HRS.MS.ProClosureS111.weightedJets
          (q + 2) P (fun y => χ y * f y) x)]
      have hprod' := mul_pos (by linarith : 0 <
          ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P
            (fun y => χ y * f y) x‖ - N * A) hplus
      nlinarith
    calc
      _ ≤ N * A := hnorm_le
      _ = K * ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖ := by
        dsimp [K, A]
        ring
  have hLp :
      eLpNorm (HRS.MS.ProClosureS111.weightedJets (q + 2) P
        (fun x => χ x * f x)) 2 volume ≤
        ENNReal.ofReal K * eLpNorm
          (HRS.MS.ProClosureS111.weightedJets (q + 2) P f) 2 volume :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (g := fun x => HRS.MS.ProClosureS111.weightedJets (q + 2) P f x)
      (c := K)
    ((HRS.MS.ProClosureS111.weightedJets_continuous hg).aestronglyMeasurable)
    (ae_of_all _ hjet) (2 : ℝ≥0∞)
  rw [HRS.MS.ProClosureS111.weightedJets_eLpNorm hg,
    HRS.MS.ProClosureS111.weightedJets_eLpNorm hf'] at hLp
  simpa only [ENNReal.ofReal_mul] using hLp

#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_cutoff_product_energy_le

end HRS.Fp81.S21
