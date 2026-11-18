import HRS.MS.Fp81S21WeightedGenNL5

/-! Pointwise agreement of every source jet for a weighted cutoff family. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.Ul HRS.MS.ProClosureS111

/-- Compact cutoffs have a common weighted-jet majorant and their source jets
are eventually exactly equal to the original source jets at each point. -/
theorem fp81s21_b3_cutoff_source_jets (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) (u : ℝ) (f : Euc p.d → ℝ)
    (hf : IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ h : ℕ → Euc p.d → ℝ,
      (∀ n, ContDiff ℝ (fp81s21_b3_q p + 2) (h n) ∧ HasCompactSupport (h n)) ∧
      (∀ n x, ‖weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n) x‖ ≤
        K * ‖weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f x‖) ∧
      ∀ x, ∀ᶠ n in atTop, ∀ (j : Fin p.d) (m : ℕ),
        iteratedFDeriv ℝ m (fp81s21_b3_source R u (h n) j) x =
          iteratedFDeriv ℝ m (fp81s21_b3_source R u f j) x := by
  obtain ⟨K, hK, h, hreg, hbound, hlocal⟩ :=
    weighted_cutoff_family (Pw := fp81s21_b3_P p) hf.1
  refine ⟨K, hK, h, hreg, hbound, ?_⟩
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : ‖x‖ < (n : ℝ) + 1 := by
    have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have heq : h n =ᶠ[𝓝 x] f := hlocal n x hn'
  intro j m
  have hs : fp81s21_b3_source R u (h n) j =ᶠ[𝓝 x]
      fp81s21_b3_source R u f j := by
    filter_upwards [heq.gradient] with y hy
    simp only [fp81s21_b3_source, hy]
  exact (Filter.EventuallyEq.iteratedFDeriv ℝ hs m).self_of_nhds

/-- The same cutoff family has convergent input energy and eventual source-jet
agreement, as well as a pointwise weighted-jet majorant. -/
theorem fp81s21_b3_cutoff_source_energy (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) (u : ℝ) (f : Euc p.d → ℝ)
    (hf : IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ h : ℕ → Euc p.d → ℝ,
      (∀ n, IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n) ∧
        HasCompactSupport (h n)) ∧
      (∀ n x, ‖weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n) x‖ ≤
        K * ‖weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f x‖) ∧
      (∀ x, ∀ᶠ n in atTop, ∀ (j : Fin p.d) (m : ℕ),
        iteratedFDeriv ℝ m (fp81s21_b3_source R u (h n) j) x =
          iteratedFDeriv ℝ m (fp81s21_b3_source R u f j) x) ∧
      Tendsto (fun n => weightedSobolevE (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n))
        atTop (𝓝 (weightedSobolevE (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f)) := by
  obtain ⟨K, hK, h, hreg, hb, hlocal⟩ :=
    weighted_cutoff_family (Pw := fp81s21_b3_P p) hf.1
  have htest : ∀ n, IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n) :=
    fun n => fp81s21_b3_compact_input_test p (h n) (hreg n).1 (hreg n).2
  have hl : ∀ x, ∀ᶠ n in atTop, h n =ᶠ[𝓝 x] f := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : ‖x‖ < (n : ℝ) + 1 := by
      have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact hlocal n x hn'
  have ht : ∀ x, Tendsto (fun n => weightedJets (fp81s21_b3_q p + 2)
      (fp81s21_b3_P p) (h n) x) atTop
      (𝓝 (weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f x)) := by
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [hl x] with n hn
    ext a
    change jbracket x ^ (-fp81s21_b3_P p) * partialDeriv a.2 f x =
      jbracket x ^ (-fp81s21_b3_P p) * partialDeriv a.2 (h n) x
    congr 1
    unfold partialDeriv
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hn a.1).self_of_nhds]
  have hmem : MemLp (weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f) 2 volume :=
    (weightedJets_memLp_iff hf.1).2 hf.2
  have hL2 : Tendsto (fun n => eLpNorm
      (weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n) -
        weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f) 2 volume)
        atTop (𝓝 0) :=
    L2_norm_tendsto_of_dominated_pointwise volume
      (fun n => weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n))
      (weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f)
      (fun n => (weightedJets_continuous (hreg n).1).stronglyMeasurable)
      (weightedJets_continuous hf.1).stronglyMeasurable hmem
      (show 0 ≤ K + 1 by linarith)
      (fun n x => (norm_sub_le _ _).trans (by
        have hh := hb n x
        nlinarith [norm_nonneg (weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f x)])) ht
  refine ⟨K, hK, h, (fun n => ⟨htest n, (hreg n).2⟩), hb, ?_,
    fp81s21_b3_weighted_energy_tendsto h f htest hf hL2⟩
  intro x
  filter_upwards [hl x] with n hn
  intro j m
  have hs : fp81s21_b3_source R u (h n) j =ᶠ[𝓝 x]
      fp81s21_b3_source R u f j := by
    filter_upwards [hn.gradient] with y hy
    simp only [fp81s21_b3_source, hy]
  exact (Filter.EventuallyEq.iteratedFDeriv ℝ hs m).self_of_nhds

#print axioms HRS.Fp81.S21.fp81s21_b3_cutoff_source_energy
#print axioms HRS.Fp81.S21.fp81s21_b3_cutoff_source_jets
end HRS.Fp81.S21
