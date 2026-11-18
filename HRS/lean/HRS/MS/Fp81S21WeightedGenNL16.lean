import HRS.MS.Fp81S21WeightedGenNL15

/-! Closure of the nonlocal weighted-test estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.Ul HRS.MS.ProClosureS111
local notation "J" => iteratedFDeriv ℝ

/-- The all-test nonlocal contract follows from the three generic local-limit
lemmas and the compact estimate, retaining its trajectory-uniform constant. -/
theorem fp81s21_b3_nonlocal_all_tests
    (p : Parameters) (B c : ℝ) (hB0 : 0 ≤ B) (hc : 0 < c)
    (hA : ∀ {fn : ℕ → Euc p.d → ℝ} {g : Euc p.d → ℝ}
      {T : ∀ m : ℕ, Euc p.d → (Euc p.d [×m]→L[ℝ] ℝ)},
      (∀ n, ContDiff ℝ (fp81s21_b3_q p) (fn n)) →
      (∀ m ≤ (fp81s21_b3_q p), TendstoLocallyUniformly (fun n => J m (fn n)) (T m) atTop) →
      (∀ x, Tendsto (fun n => fn n x) atTop (𝓝 (g x))) →
      ContDiff ℝ (fp81s21_b3_q p) g ∧ ∀ m ≤ (fp81s21_b3_q p), J m g = T m)
    (hconv : ∀ j : Fin p.d, ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      {gn : ℕ → Euc p.d → F} {g : Euc p.d → F},
      (∀ n, Continuous (gn n)) → Continuous g → (∀ n, Integrable (gn n)) → Integrable g →
      TendstoLocallyUniformly gn g atTop →
      Tendsto (fun n => eLpNorm (gn n - g) 1 volume) atTop (𝓝 0) →
      TendstoLocallyUniformly (fun n => ultK (u2_kap p.d p.s j) (gn n))
        (ultK (u2_kap p.d p.s j) g) atTop)
    (hD : ∀ {gn : ℕ → Euc p.d → ℝ} {g : Euc p.d → ℝ} {H : Euc p.d → ℝ},
      (∀ n, ContDiff ℝ ((fp81s21_b3_q p) + 1) (gn n)) → ContDiff ℝ ((fp81s21_b3_q p) + 1) g →
      Continuous H → Integrable H → (∀ x, 0 ≤ H x) →
      (∀ n m, m ≤ (fp81s21_b3_q p) + 1 → ∀ x, ‖J m (gn n) x‖ ≤ H x) →
      (∀ m, m ≤ (fp81s21_b3_q p) + 1 → ∀ x, ‖J m g x‖ ≤ H x) →
      (∀ x, ∀ᶠ n in atTop, ∀ m ≤ (fp81s21_b3_q p), J m (gn n) x = J m g x) →
      ∀ m ≤ (fp81s21_b3_q p), TendstoLocallyUniformly (fun n => J m (gn n)) (J m g) atTop ∧
        Tendsto (fun n => eLpNorm (J m (gn n) - J m g) 1 volume) atTop (𝓝 0)) :
    fp81s21_b3_nonlocal_all_tests_contract p B c := by
  obtain ⟨A, hA0, hbase⟩ := fp81s21_b3_all_test_of_output_jets p B c hB0 hc
  unfold fp81s21_b3_nonlocal_all_tests_contract
  refine ⟨A, hA0, ?_⟩
  intro δ R hdata u hu f hf
  obtain ⟨K, hK, h, hreg, hb, heq, henergy⟩ :=
    fp81s21_b3_cutoff_source_energy p R u f hf
  obtain ⟨hcd, hjets⟩ := fp81s21_b3_output_jets_of_cutoff_source_energy
    R u f K h hB0 hc hdata hu hf hK hreg hb heq hA hconv hD
  exact hbase R hdata u hu f hf h hreg henergy hcd hjets

#print axioms HRS.Fp81.S21.fp81s21_b3_nonlocal_all_tests
end HRS.Fp81.S21
