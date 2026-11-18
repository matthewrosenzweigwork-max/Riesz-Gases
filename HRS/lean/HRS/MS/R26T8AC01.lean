import HRS.MS.R26T8AC01d
import HRS.MS.S82P2Sum4

/-!
# S8.2 observed-time layer, packet T8A.C01: fractional pinned partitions and the uniform density bound
Statement exactly as in the Pro packet.  `N0 = ⌈4 C0²⌉ + 2` makes `|h N| ≤ C0 deltaN N ≤ 1`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.R26T8A
open HRS.MS.Phase2S82

theorem r26t8a_fractional_density (d : ℕ) (hd : 2 ≤ d) (a beta C0 : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ N0 : ℕ, ∀ rho : Euc d → ℝ, HRS.Whole.IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ h : ℕ → Euc d → ℝ, WeakReferenceSetup d a beta rho q h C0 →
      ∀ N n p : ℕ, N0 ≤ N → 2 ≤ N → 1 ≤ n → n + p ≤ N → p ≤ 4 →
      ∀ pins : Fin p → Euc d, ∀ weights : Fin p → ℝ,
      (∀ j, 0 ≤ weights j ∧ weights j ≤ beta / N) →
      IsProbabilityMeasure (r26t8a_fractionalLaw q h (HRS.Whole.withDensityReal rho) beta N n pins weights) ∧
      ∀ i : Fin n, ∀ᵐ x ∂HRS.Whole.withDensityReal rho,
        r26t8a_density (HRS.Whole.withDensityReal rho)
          (r26t8a_fractionalLaw q h (HRS.Whole.withDensityReal rho) beta N n pins weights) i x ≤ 8 := by
  refine ⟨⌈4 * C0 ^ 2⌉₊ + 2, fun rho hrho h hW N n p hN0 hN2 hn hnp hp pins weights hw => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hC0 : 0 < C0 := hW.positive
  have hNr : 4 * C0 ^ 2 ≤ (N : ℝ) := by
    have h1 : 4 * C0 ^ 2 ≤ (⌈4 * C0 ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈4 * C0 ^ 2⌉₊ + 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN0
    push_cast at h2
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hh1 : ∀ x, |h N x| ≤ 1 := fun x => by
    refine (hW.hbound N hN2 x).trans ?_
    have hd0 : 0 ≤ Phase2S82.deltaN N := by
      unfold Phase2S82.deltaN Phase2S82.logN
      refine div_nonneg (Real.log_nonneg ?_) hNpos.le
      have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      have := Real.add_one_le_exp (1 : ℝ)
      nlinarith
    have hsq := HRS.MS.S82P2.s82p2_deltaN_sq_le (N := N) (by omega)
    have h3 : (C0 * Phase2S82.deltaN N) ^ 2 ≤ 1 := by
      calc (C0 * Phase2S82.deltaN N) ^ 2 = C0 ^ 2 * Phase2S82.deltaN N ^ 2 := by ring
        _ ≤ C0 ^ 2 * (4 / N) := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
        _ ≤ 1 := by
          rw [← mul_div_assoc, div_le_one hNpos]
          nlinarith
    nlinarith [mul_nonneg hC0.le hd0]
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hrho.2.1
  have hmain := fun i : Fin (m + 1) => r26t8a_c01_fixedN (p := p) (m := m) hd ha hbeta hrho hW N hN2 hh1
    hnp pins weights hw i
  refine ⟨(hmain 0).1, fun i => ?_⟩
  have := (hmain i).1
  exact HRS.MS.S82R.s82r_rnDeriv_le (by norm_num) (hmain i).2

end HRS.MS.R26T8A
