import HRS.MS.R26T8AP21l

/-!
# S8.2 local Newton layer, packet T8A.P21: symmetric Taylor expansion of the exact leading source
`midPair` of the leading source is `-(s/2) |z|^(-s-2) Q(X,z)` with `Q` the symmetric cubic Taylor remainder of `Df`; its nested jets are
bounded through the integral Taylor formula (`r26t8a_Q_integral`), the contraction chain (parts c-f), differentiation under the integral
(parts g, h) and the nested Leibniz rule with the cutoff kernel (part k).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_leading_source (d : ℕ) (hd : 2 ≤ d) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → TestBound (k+4) A f →
      Conormal k 0 0 (criticalS d-2) (C*A) (fun x y =>
        (1/2:ℝ)*hSource f x y + (criticalS d/2)*‖x-y‖^(-criticalS d)*
          (fderiv ℝ (fderiv ℝ f) ((1/2:ℝ)•(x+y)))
            (‖x-y‖⁻¹•(x-y)) (‖x-y‖⁻¹•(x-y))) := by
  obtain ⟨chi, hchi⟩ := r26t8a_exists_cutoff d
  obtain ⟨Ck, hCk0, hCk⟩ := r26t8a_kz_jet d k
  have hd1 : 1 ≤ d := by omega
  have hs : 0 < criticalS d := by
    unfold criticalS
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  refine ⟨((k : ℝ) + 1) * 2 ^ k * Ck * (2 * ((k : ℝ) + 1) ^ 4 + 12 * ((k : ℝ) + 1) ^ 2), by positivity,
    fun f A hA hT => ?_⟩
  obtain ⟨hf, hTb⟩ := hT
  show Conormal k 0 0 (criticalS d - 2) _ (r26t8a_lead f)
  refine ⟨?_, fun p q hpq X z hz => ?_⟩
  · have hL : ∀ x y : Euc d, x ≠ y → r26t8a_lead f x y =
        r26t8a_kz d (x - y) * r26t8a_Q f ((1 / 2 : ℝ) • (x + y)) (x - y) := by
      intro x y hxy
      have := r26t8a_lead_mid hd1 f ((1 / 2 : ℝ) • (x + y)) (sub_ne_zero.2 hxy)
      unfold midPair at this
      rwa [show (1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • (x - y) = x by module,
        show (1 / 2 : ℝ) • (x + y) - (1 / 2 : ℝ) • (x - y) = y by module] at this
    have hQc := r26t8a_Q_contDiff hf k
    have hQ2 : ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => r26t8a_Q f ((1 / 2 : ℝ) • (p.1 + p.2)) (p.1 - p.2)) :=
      hQc.comp (((contDiff_fst.add contDiff_snd).const_smul (1 / 2 : ℝ)).prodMk (contDiff_fst.sub contDiff_snd))
    have hK2 : ContDiffOn ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => r26t8a_kz d (p.1 - p.2)) {p | p.1 ≠ p.2} :=
      fun p hp => (((r26t8a_kz_contDiffAt (sub_ne_zero.2 hp)).comp p
        (contDiff_fst.sub contDiff_snd).contDiffAt).of_le (by exact_mod_cast le_top)).contDiffWithinAt
    exact (hK2.mul hQ2.contDiffOn).congr (fun p hp => hL p.1 p.2 hp)
  · have h0 := r26t8a_lead_nest_bound hd1 hchi hf p q X z hz
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hpw : pairWeight 0 (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) = 1 := by
      simp [pairWeight]
    rw [hpw]
    have hqk : q ≤ k := by omega
    have hbin : ∀ i ∈ Finset.range (q + 1), (q.choose i : ℝ) ≤ 2 ^ k := fun i _ => by
      have := (Nat.choose_le_two_pow q i).trans (Nat.pow_le_pow_right two_pos hqk)
      exact_mod_cast this
    have hbin0 : ∀ i : ℕ, (0 : ℝ) ≤ (q.choose i : ℝ) := fun i => Nat.cast_nonneg _
    have hq1 : ((q : ℝ) + 1) ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hqk
    have hAj : ∀ j, 1 ≤ j → j ≤ k + 4 → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A := hTb
    have hCA : 0 ≤ ((k : ℝ) + 1) * 2 ^ k * Ck * (2 * ((k : ℝ) + 1) ^ 4 + 12 * ((k : ℝ) + 1) ^ 2) * A := by positivity
    by_cases h1 : ‖z‖ ≤ 1
    · have hmin : min 1 ‖z‖ = ‖z‖ := min_eq_right h1
      rw [hmin]
      have hE : -(criticalS d - 2 + (q : ℝ)) = -criticalS d - 2 + 4 - (q : ℝ) := by ring
      simp only [pow_zero, mul_one, hE]
      set E : ℝ := ‖z‖ ^ (-criticalS d - 2 + 4 - (q : ℝ)) with hEdef
      have hE0 : 0 ≤ E := Real.rpow_nonneg hzn.le _
      calc ‖mixedJet p q (r26t8a_lead f) X z‖ ≤ _ := h0
        _ ≤ ∑ i ∈ Finset.range (q + 1), 2 ^ k * Ck * (2 * A * ((k : ℝ) + 1) ^ 4) * E := by
            refine Finset.sum_le_sum (fun i hi => ?_)
            have hiq : i ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
            exact r26t8a_term_small hzn h1 (criticalS d) i q k hiq hqk hA hCk0 (hbin0 i) (norm_nonneg _)
              (norm_nonneg _) (hbin i hi) (hCk i (by omega) z hz)
              (r26t8a_nest_Q_small hf hAj chi hchi p (q - i) (by omega) X z h1)
        _ = ((q : ℝ) + 1) * (2 ^ k * Ck * (2 * A * ((k : ℝ) + 1) ^ 4) * E) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        _ ≤ ((k : ℝ) + 1) * (2 ^ k * Ck * (2 * A * ((k : ℝ) + 1) ^ 4) * E) :=
            mul_le_mul_of_nonneg_right hq1 (by positivity)
        _ ≤ ((k : ℝ) + 1) * 2 ^ k * Ck * (2 * ((k : ℝ) + 1) ^ 4 + 12 * ((k : ℝ) + 1) ^ 2) * A * (1 + E) := by
            have : 0 ≤ ((k : ℝ) + 1) * 2 ^ k * Ck * (12 * ((k : ℝ) + 1) ^ 2) * A * E := by positivity
            nlinarith [mul_nonneg hCA hE0, this]
    · push Not at h1
      have hmin : min 1 ‖z‖ = 1 := min_eq_left h1.le
      rw [hmin]
      simp only [Real.one_rpow, Real.log_one, abs_zero, add_zero, pow_zero, mul_one]
      calc ‖mixedJet p q (r26t8a_lead f) X z‖ ≤ _ := h0
        _ ≤ ∑ i ∈ Finset.range (q + 1), 2 ^ k * Ck * (12 * A * ((k : ℝ) + 1) ^ 2) := by
            refine Finset.sum_le_sum (fun i hi => ?_)
            have hiq : i ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
            exact r26t8a_term_large h1.le hs.le i q k hiq hqk hA hCk0 (hbin0 i) (norm_nonneg _)
              (norm_nonneg _) (hbin i hi) (hCk i (by omega) z hz)
              (r26t8a_nest_Q_large hf hAj p (q - i) (by omega) X z)
        _ = ((q : ℝ) + 1) * (2 ^ k * Ck * (12 * A * ((k : ℝ) + 1) ^ 2)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
        _ ≤ ((k : ℝ) + 1) * (2 ^ k * Ck * (12 * A * ((k : ℝ) + 1) ^ 2)) :=
            mul_le_mul_of_nonneg_right hq1 (by positivity)
        _ ≤ ((k : ℝ) + 1) * 2 ^ k * Ck * (2 * ((k : ℝ) + 1) ^ 4 + 12 * ((k : ℝ) + 1) ^ 2) * A * (1 + 1) := by
            have : 0 ≤ ((k : ℝ) + 1) * 2 ^ k * Ck * (2 * ((k : ℝ) + 1) ^ 4) * A := by positivity
            nlinarith [this, hCA]

end HRS.MS.R26T8A
