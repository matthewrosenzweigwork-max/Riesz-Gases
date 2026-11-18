import HRS.MS.Fp81S21WeightedRellich14

/-!
For a fixed compact cutoff, every sequence in the strong unit ball has a
weakly Cauchy subsequence.  Completeness of the weak L² jet space upgrades
this to sequential compactness of the closure, hence total boundedness of
the cutoff image.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Filter MeasureTheory Topology Set
open scoped ENNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.FixEq

/-- The image of the strong unit ball under a fixed spatial cutoff is totally
bounded in the weak weighted jet space. -/
theorem fp81s21_weightedRellich_fixedCutoff_totallyBounded
    {d q : ℕ} {P ρ C : ℝ} (hρ : 1 ≤ ρ) (hC0 : 0 ≤ C)
    {χ : Euc d → ℝ}
    (hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχone : ∀ x, ‖x‖ ≤ ρ → χ x = 1)
    (hχzero : ∀ x, 2 * ρ ≤ ‖x‖ → χ x = 0)
    (hχB : ∀ k ≤ q + 2, ∀ x, ‖iteratedFDeriv ℝ k χ x‖ ≤ C) :
    TotallyBounded {z : HRS.MS.R26T3.JetSpace d q (P + 2) |
      ∃ f : Euc d → ℝ, IsR2Test f ∧
        weightedSobolevE (q + 2) P f ≤ 1 ∧
        z = HRS.MS.R26T3.r26t3_jet q (P + 2) (fun x => χ x * f x)} := by
  let S : Set (HRS.MS.R26T3.JetSpace d q (P + 2)) :=
    {z | ∃ f : Euc d → ℝ, IsR2Test f ∧
      weightedSobolevE (q + 2) P f ≤ 1 ∧
      z = HRS.MS.R26T3.r26t3_jet q (P + 2) (fun x => χ x * f x)}
  have hseq : IsSeqCompact (closure S) := by
    intro v hv
    have happrox : ∀ n, ∃ y ∈ S,
        dist (v n) y < ((n : ℝ) + 1)⁻¹ := by
      intro n
      have hpos : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
      obtain ⟨y, hy, hd⟩ :=
        (Metric.mem_closure_iff.1 (hv n)) ((n : ℝ) + 1)⁻¹ hpos
      exact ⟨y, hy, hd⟩
    choose y hyMem hyDist using happrox
    have hrepresent : ∀ n, ∃ f : Euc d → ℝ,
        IsR2Test f ∧ weightedSobolevE (q + 2) P f ≤ 1 ∧
        y n = HRS.MS.R26T3.r26t3_jet q (P + 2)
          (fun x => χ x * f x) := by
      intro n
      simpa [S] using hyMem n
    choose f hf hE hrepr using hrepresent
    obtain ⟨σ, hσ, hjetCauchy⟩ :=
      fp81s21_weightedRellich_fixedCutoffFamily_cauchy
        hρ hC0 hχs hχc hχone hχzero hχB f hf hE
    have hyCauchy : CauchySeq (fun n => y (σ n)) := by
      simpa only [hrepr] using hjetCauchy
    have hσid : ∀ n, n ≤ σ n := by
      intro n
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
          have hlt : σ n < σ (Nat.succ n) := hσ (Nat.lt_succ_self n)
          exact (Nat.succ_le_succ ih).trans (Nat.succ_le_of_lt hlt)
    have hvCauchy : CauchySeq (fun n => v (σ n)) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ :=
        (Metric.cauchySeq_iff.1 hyCauchy) (ε / 3) (by linarith)
      obtain ⟨M, hM⟩ := exists_nat_gt (3 / ε)
      refine ⟨max N M, ?_⟩
      intro m hm n hn
      have hmN : N ≤ m := le_trans (le_max_left _ _) hm
      have hnN : N ≤ n := le_trans (le_max_left _ _) hn
      have hmM : M ≤ m := le_trans (le_max_right _ _) hm
      have hnM : M ≤ n := le_trans (le_max_right _ _) hn
      have hdenm : 3 / ε < ((σ m : ℝ) + 1) := by
        calc
          3 / ε < (M : ℝ) := hM
          _ ≤ (m : ℝ) := by exact_mod_cast hmM
          _ ≤ (σ m : ℝ) := by exact_mod_cast hσid m
          _ ≤ (σ m : ℝ) + 1 := by linarith
      have hdenn : 3 / ε < ((σ n : ℝ) + 1) := by
        calc
          3 / ε < (M : ℝ) := hM
          _ ≤ (n : ℝ) := by exact_mod_cast hnM
          _ ≤ (σ n : ℝ) := by exact_mod_cast hσid n
          _ ≤ (σ n : ℝ) + 1 := by linarith
      have hmulm : 3 < (((σ m : ℝ) + 1) * ε) :=
        (div_lt_iff₀ hε).1 hdenm
      have hmuln : 3 < (((σ n : ℝ) + 1) * ε) :=
        (div_lt_iff₀ hε).1 hdenn
      have hinvm : ((σ m : ℝ) + 1)⁻¹ < ε / 3 := by
        have hdenpos : 0 < ((σ m : ℝ) + 1) := by positivity
        have hthree : 3 / ((σ m : ℝ) + 1) < ε :=
          (div_lt_iff₀ hdenpos).2 (by nlinarith [hmulm])
        calc
          ((σ m : ℝ) + 1)⁻¹ =
              (3 / ((σ m : ℝ) + 1)) / 3 := by
            field_simp [hdenpos.ne'] <;> ring
          _ < ε / 3 := div_lt_div_of_pos_right hthree (by norm_num)
      have hinvn : ((σ n : ℝ) + 1)⁻¹ < ε / 3 := by
        have hdenpos : 0 < ((σ n : ℝ) + 1) := by positivity
        have hthree : 3 / ((σ n : ℝ) + 1) < ε :=
          (div_lt_iff₀ hdenpos).2 (by nlinarith [hmuln])
        calc
          ((σ n : ℝ) + 1)⁻¹ =
              (3 / ((σ n : ℝ) + 1)) / 3 := by
            field_simp [hdenpos.ne'] <;> ring
          _ < ε / 3 := div_lt_div_of_pos_right hthree (by norm_num)
      have hleft : dist (v (σ m)) (y (σ m)) < ε / 3 :=
        (hyDist (σ m)).trans hinvm
      have hmid := hN m hmN n hnN
      have hright : dist (y (σ n)) (v (σ n)) < ε / 3 := by
        rw [dist_comm]
        exact (hyDist (σ n)).trans hinvn
      calc
        dist (v (σ m)) (v (σ n)) ≤
            dist (v (σ m)) (y (σ m)) + dist (y (σ m)) (v (σ n)) :=
              dist_triangle _ _ _
        _ ≤ dist (v (σ m)) (y (σ m)) +
            (dist (y (σ m)) (y (σ n)) + dist (y (σ n)) (v (σ n))) :=
              add_le_add le_rfl (dist_triangle _ _ _)
        _ < ε := by linarith
    obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hvCauchy
    refine ⟨a, ?_, σ, hσ, ha⟩
    exact isClosed_closure.mem_of_tendsto ha
      (Filter.Eventually.of_forall fun n => hv (σ n))
  have htbClosure : TotallyBounded (closure S) := hseq.totallyBounded
  have htbS : TotallyBounded S := htbClosure.subset subset_closure
  simpa [S] using htbS

/-- Choosing the uniform scaled cutoff gives a totally bounded cutoff image
for every fixed radius. -/
theorem fp81s21_weightedRellich_cutoffFamily_totallyBounded
    {d q : ℕ} {P ρ : ℝ} (hρ : 1 ≤ ρ) :
    ∃ χ : Euc d → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      (∀ x, ‖x‖ ≤ ρ → χ x = 1) ∧
      (∀ x, 2 * ρ ≤ ‖x‖ → χ x = 0) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ k ≤ q + 2, ∀ x, ‖iteratedFDeriv ℝ k χ x‖ ≤ C) ∧
        TotallyBounded {z : HRS.MS.R26T3.JetSpace d q (P + 2) |
          ∃ f : Euc d → ℝ, IsR2Test f ∧
            weightedSobolevE (q + 2) P f ≤ 1 ∧
            z = HRS.MS.R26T3.r26t3_jet q (P + 2)
              (fun x => χ x * f x)} := by
  obtain ⟨C, hC0, hCut⟩ :=
    fp81s21_weightedRellich_scaledCutoff_uniform (d := d) (q := q)
  obtain ⟨χ, hχs, hχc, hχone, hχzero, hχB⟩ := hCut ρ hρ
  refine ⟨χ, hχs, hχc, hχone, hχzero, C, hC0, hχB, ?_⟩
  exact fp81s21_weightedRellich_fixedCutoff_totallyBounded
    hρ hC0 hχs hχc hχone hχzero hχB

#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_fixedCutoff_totallyBounded
#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_cutoffFamily_totallyBounded

end HRS.Fp81.S21
