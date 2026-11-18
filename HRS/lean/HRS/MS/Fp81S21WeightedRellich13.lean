import HRS.MS.Fp81S21WeightedRellich12

/-! The cutoff remainder is small in the weaker weighted norm.  Its
derivatives vanish in the inner ball; on the exterior, the target weight
contributes the uniform factor `ρ⁻²` after taking the L² norm. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.FixEq

/-- Spatial cutoff remainder bound from `(q + 2, P)` to `(q, P + 2)`.
The constant `K` is selected before `ρ`; the displayed `ρ⁻²` is the norm
decay resulting from the additional two powers in the target weight. -/
theorem fp81s21_weightedRellich_remainder_energy_profile
    {d q : ℕ} {P : ℝ} :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      ∀ f : Euc d → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f →
      ∃ χ : Euc d → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
        HasCompactSupport χ ∧
        (∀ x, ‖x‖ ≤ ρ → χ x = 1) ∧
        (∀ x, 2 * ρ ≤ ‖x‖ → χ x = 0) ∧
        weightedSobolevE q (P + 2) (fun x => f x - χ x * f x) ≤
          ENNReal.ofReal (K * ρ ^ (-2 : ℝ)) *
            weightedSobolevE (q + 2) P f := by
  obtain ⟨C, hC0, hremUniform⟩ :=
    fp81s21_weightedRellich_remainder_uniform (d := d) (q := q)
  let L : ℝ := ∑ j ∈ Finset.range (q + 3),
    ∑ k ∈ Finset.range (j + 1),
      (j.choose k : ℝ) * C * (d : ℝ) ^ (j - k)
  let N : ℝ := (Fintype.card
    (HRS.MS.ProClosureS111.WeightedJetIndex d q) : ℝ) + 1
  let K : ℝ := N * (1 + L)
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
    positivity
  have hlocalCoeff : ∀ j ≤ q,
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
  refine ⟨K, hK, ?_⟩
  intro ρ hρ f hf
  obtain ⟨χ, hχs, hχc, hχone, hχzero, hCbound, hremzero, htsupp, hremderiv⟩ :=
    hremUniform ρ hρ f hf
  let r : Euc d → ℝ := fun x => f x - χ x * f x
  have hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := by
    dsimp [r]
    exact hf.sub (hχs.mul hf)
  have hrq : ContDiff ℝ q r := hr.of_le (by simp)
  have hfq : ContDiff ℝ (q + 2) f := hf.of_le (by simp)
  have hcoord : ∀ j ≤ q, ∀ i : Fin j → Fin d, ∀ x,
      jbracket x ^ (-(P + 2)) * |partialDeriv i r x| ≤
        (1 + L) * ρ ^ (-2 : ℝ) *
          ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖ := by
    intro j hj i x
    by_cases htail : ρ ≤ jbracket x
    · have hrem := hremderiv j (by omega) i x
      have hbase := HRS.MS.ProClosureS111.weighted_partial_le_jet
        (r := q + 2) (Pw := P) f (by omega) i x
      have hweightId : jbracket x ^ (-(P + 2)) =
          jbracket x ^ (-2 : ℝ) * jbracket x ^ (-P) := by
        rw [show -(P + 2) = (-2 : ℝ) + (-P) by ring,
          Real.rpow_add (s57p_jbracket_pos x)]
      have htailWeight : jbracket x ^ (-2 : ℝ) ≤ ρ ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by linarith : 0 < ρ) htail (by norm_num)
      have hinner : jbracket x ^ (-P) *
          (|partialDeriv i f x| +
            ∑ k ∈ Finset.range (j + 1),
              (j.choose k : ℝ) *
                (C * ‖iteratedFDeriv ℝ (j - k) f x‖)) ≤
          (1 + L) *
            ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖ := by
        calc
          _ = jbracket x ^ (-P) * |partialDeriv i f x| +
              ∑ k ∈ Finset.range (j + 1),
                (j.choose k : ℝ) * C *
                  (jbracket x ^ (-P) *
                    ‖iteratedFDeriv ℝ (j - k) f x‖) := by
                rw [mul_add]
                congr 1
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun k hk => ?_
                ring
          _ ≤ ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖ +
              ∑ k ∈ Finset.range (j + 1),
                (j.choose k : ℝ) * C *
                  ((d : ℝ) ^ (j - k) *
                    ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖) := by
                apply add_le_add hbase
                refine Finset.sum_le_sum fun k hk => ?_
                have hmk : j - k ≤ q + 2 :=
                  (Nat.sub_le j k).trans (hj.trans (by omega))
                have hder := HRS.MS.ProClosureS111.weighted_derivative_le_jet
                  (r := q + 2) (Pw := P) f hmk x
                have hnonneg : 0 ≤ (j.choose k : ℝ) * C := by positivity
                exact mul_le_mul_of_nonneg_left hder hnonneg
          _ = (1 +
              ∑ k ∈ Finset.range (j + 1),
                (j.choose k : ℝ) * C * (d : ℝ) ^ (j - k)) *
              ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖ := by
                calc
                  _ = ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖ +
                      ∑ k ∈ Finset.range (j + 1),
                        ((j.choose k : ℝ) * C * (d : ℝ) ^ (j - k)) *
                          ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖ := by
                        congr 1
                        refine Finset.sum_congr rfl fun k hk => ?_
                        ring
                  _ = _ := by
                        rw [add_mul, one_mul, Finset.sum_mul]
          _ ≤ (1 + L) *
              ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖ := by
                apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                linarith [hlocalCoeff j hj]
      have hremBound : jbracket x ^ (-P) *
          |partialDeriv i r x| ≤
          jbracket x ^ (-P) *
            (|partialDeriv i f x| +
              ∑ k ∈ Finset.range (j + 1),
                (j.choose k : ℝ) *
                  (C * ‖iteratedFDeriv ℝ (j - k) f x‖)) := by
        exact mul_le_mul_of_nonneg_left hrem
          (Real.rpow_nonneg (s57p_jbracket_pos x).le (-P))
      have hweightNonneg : 0 ≤ jbracket x ^ (-2 : ℝ) :=
        Real.rpow_nonneg (s57p_jbracket_pos x).le _
      have hsumNonneg : 0 ≤
          ∑ k ∈ Finset.range (j + 1),
            (j.choose k : ℝ) *
              (C * ‖iteratedFDeriv ℝ (j - k) f x‖) := by
        refine Finset.sum_nonneg fun k hk => ?_
        positivity
      have hweakNonneg : 0 ≤ jbracket x ^ (-P) *
          (|partialDeriv i f x| +
            ∑ k ∈ Finset.range (j + 1),
              (j.choose k : ℝ) *
                (C * ‖iteratedFDeriv ℝ (j - k) f x‖)) :=
        mul_nonneg (Real.rpow_nonneg (s57p_jbracket_pos x).le _)
          (add_nonneg (abs_nonneg _) hsumNonneg)
      calc
        _ = jbracket x ^ (-2 : ℝ) *
            (jbracket x ^ (-P) * |partialDeriv i r x|) := by
              rw [hweightId]
              ring
        _ ≤ jbracket x ^ (-2 : ℝ) *
            (jbracket x ^ (-P) *
              (|partialDeriv i f x| +
                ∑ k ∈ Finset.range (j + 1),
                  (j.choose k : ℝ) *
                    (C * ‖iteratedFDeriv ℝ (j - k) f x‖))) :=
              mul_le_mul_of_nonneg_left hremBound hweightNonneg
        _ ≤ ρ ^ (-2 : ℝ) *
            (jbracket x ^ (-P) *
              (|partialDeriv i f x| +
                ∑ k ∈ Finset.range (j + 1),
                  (j.choose k : ℝ) *
                    (C * ‖iteratedFDeriv ℝ (j - k) f x‖))) :=
              mul_le_mul_of_nonneg_right htailWeight hweakNonneg
        _ ≤ ρ ^ (-2 : ℝ) *
            ((1 + L) *
              ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖) :=
              mul_le_mul_of_nonneg_left hinner
                (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ ρ) _)
        _ = _ := by ring
    · have hzero := fp81s21_weightedRellich_partialDeriv_zero_inner
        (d := d) (ρ := ρ) (g := r) hremzero (lt_of_not_ge htail) i
      have hR : 0 ≤ (1 + L) * ρ ^ (-2 : ℝ) *
          ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖ := by
        apply mul_nonneg
        · apply mul_nonneg
          · linarith
          · exact Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ ρ) _
        · exact norm_nonneg _
      simpa [hzero] using hR
  have hjet : ∀ x,
      ‖HRS.MS.ProClosureS111.weightedJets q (P + 2) r x‖ ≤
        K * ρ ^ (-2 : ℝ) *
          ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖ := by
    intro x
    let A : ℝ := (1 + L) * ρ ^ (-2 : ℝ) *
      ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖
    have hA : 0 ≤ A := by
      dsimp [A]
      positivity
    have hterm : ∀ p : HRS.MS.ProClosureS111.WeightedJetIndex d q,
        jbracket x ^ (-2 * (P + 2)) *
          (partialDeriv p.2 r x) ^ 2 ≤ A ^ 2 := by
      intro p
      have hj : p.1.1 ≤ q := Nat.lt_succ_iff.mp p.1.2
      have hcp := hcoord p.1.1 hj p.2 x
      have hweight : (jbracket x ^ (-(P + 2))) ^ 2 =
          jbracket x ^ (-2 * (P + 2)) := by
        rw [← Real.rpow_two, ← Real.rpow_mul (s57p_jbracket_pos x).le]
        congr 1
        ring
      have hcp' : jbracket x ^ (-(P + 2)) * |partialDeriv p.2 r x| ≤ A := by
        simpa [A, mul_assoc, mul_left_comm, mul_comm] using hcp
      have hcp0 : 0 ≤ jbracket x ^ (-(P + 2)) * |partialDeriv p.2 r x| :=
        mul_nonneg (Real.rpow_nonneg (s57p_jbracket_pos x).le _) (abs_nonneg _)
      have hsq := mul_le_mul hcp' hcp' hcp0 hA
      calc
        _ = (jbracket x ^ (-(P + 2)) * |partialDeriv p.2 r x|) ^ 2 := by
          rw [← hweight, mul_pow, sq_abs]
        _ ≤ A ^ 2 := by simpa [pow_two] using hsq
    have hsumSq :
        ‖HRS.MS.ProClosureS111.weightedJets q (P + 2) r x‖ ^ 2 ≤
          (Fintype.card (HRS.MS.ProClosureS111.WeightedJetIndex d q) : ℝ) * A ^ 2 := by
      rw [HRS.MS.ProClosureS111.weightedJets_norm_sq]
      calc
        _ ≤ ∑ _p : HRS.MS.ProClosureS111.WeightedJetIndex d q, A ^ 2 :=
          Finset.sum_le_sum fun p hp => hterm p
        _ = (Fintype.card (HRS.MS.ProClosureS111.WeightedJetIndex d q) : ℝ) * A ^ 2 := by
          simp
    have hcard :
        (Fintype.card (HRS.MS.ProClosureS111.WeightedJetIndex d q) : ℝ) ≤ N ^ 2 := by
      dsimp [N]
      have hn : 0 ≤ (Fintype.card
        (HRS.MS.ProClosureS111.WeightedJetIndex d q) : ℝ) := by positivity
      nlinarith
    have hsq :
        ‖HRS.MS.ProClosureS111.weightedJets q (P + 2) r x‖ ^ 2 ≤ (N * A) ^ 2 := by
      calc
        _ ≤ (Fintype.card
            (HRS.MS.ProClosureS111.WeightedJetIndex d q) : ℝ) * A ^ 2 := hsumSq
        _ ≤ N ^ 2 * A ^ 2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg A)
        _ = (N * A) ^ 2 := by ring
    have hNA : 0 ≤ N * A := by
      apply mul_nonneg
      · dsimp [N]
        positivity
      · exact hA
    have hnorm : ‖HRS.MS.ProClosureS111.weightedJets q (P + 2) r x‖ ≤ N * A := by
      by_contra hnot
      have hlt : N * A < ‖HRS.MS.ProClosureS111.weightedJets q (P + 2) r x‖ :=
        lt_of_not_ge hnot
      have hplus : 0 < N * A + ‖HRS.MS.ProClosureS111.weightedJets q (P + 2) r x‖ := by
        linarith [hNA, norm_nonneg (HRS.MS.ProClosureS111.weightedJets q (P + 2) r x)]
      have hprod := mul_pos (by linarith : 0 <
        ‖HRS.MS.ProClosureS111.weightedJets q (P + 2) r x‖ - N * A) hplus
      nlinarith
    calc
      _ ≤ N * A := hnorm
      _ = K * ρ ^ (-2 : ℝ) *
          ‖HRS.MS.ProClosureS111.weightedJets (q + 2) P f x‖ := by
        dsimp [A, K, N]
        ring
  have hcoef : 0 ≤ K * ρ ^ (-2 : ℝ) := by
    exact mul_nonneg hK (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ ρ) _)
  have hLp :
      eLpNorm (HRS.MS.ProClosureS111.weightedJets q (P + 2) r) 2 volume ≤
        ENNReal.ofReal (K * ρ ^ (-2 : ℝ)) *
          eLpNorm (HRS.MS.ProClosureS111.weightedJets (q + 2) P f) 2 volume :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (g := fun x => HRS.MS.ProClosureS111.weightedJets (q + 2) P f x)
      (c := K * ρ ^ (-2 : ℝ))
      ((HRS.MS.ProClosureS111.weightedJets_continuous hrq).aestronglyMeasurable)
      (ae_of_all _ hjet) (2 : ℝ≥0∞)
  rw [HRS.MS.ProClosureS111.weightedJets_eLpNorm hrq,
    HRS.MS.ProClosureS111.weightedJets_eLpNorm hfq] at hLp
  refine ⟨χ, hχs, hχc, hχone, hχzero, ?_⟩
  simpa only [ENNReal.ofReal_mul] using hLp

#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_remainder_energy_profile

end HRS.Fp81.S21
