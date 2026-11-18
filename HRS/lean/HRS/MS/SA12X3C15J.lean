import HRS.MS.SA12X3C15I
import HRS.MS.SA12BuildC12

/-!
# S.A.12 C15 (SA12X3), part J: the flowed unit-cell mass is bounded by the cell supremum (C12)
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12x3_term_le_jetSq (m : ℕ) (w F : Euc d → ℝ) {j : ℕ} (hj : j ≤ m) (idx : Fin j → Fin d) :
    ∫ x, (w x * partialDeriv idx F x) ^ 2 ≤ jetSq m w F := by
  unfold jetSq
  have hnn : ∀ (j : ℕ) (idx : Fin j → Fin d), 0 ≤ ∫ x, (w x * partialDeriv idx F x) ^ 2 :=
    fun j idx => integral_nonneg fun x => sq_nonneg _
  have hc1 : (1 : ℝ) ≤ (Nat.choose m j : ℝ) := by
    have : 1 ≤ Nat.choose m j := Nat.choose_pos hj
    exact_mod_cast this
  have h1 : ∫ x, (w x * partialDeriv idx F x) ^ 2 ≤ ∑ idx' : Fin j → Fin d, ∫ x, (w x * partialDeriv idx' F x) ^ 2 :=
    Finset.single_le_sum (f := fun idx' : Fin j → Fin d => ∫ x, (w x * partialDeriv idx' F x) ^ 2)
      (fun idx' _ => hnn j idx') (Finset.mem_univ idx)
  have h0 : 0 ≤ ∑ idx' : Fin j → Fin d, ∫ x, (w x * partialDeriv idx' F x) ^ 2 :=
    Finset.sum_nonneg fun idx' _ => hnn j idx'
  have h2 : ∑ idx' : Fin j → Fin d, ∫ x, (w x * partialDeriv idx' F x) ^ 2 ≤
      (Nat.choose m j : ℝ) * ∑ idx' : Fin j → Fin d, ∫ x, (w x * partialDeriv idx' F x) ^ 2 := by nlinarith
  have h3 : (Nat.choose m j : ℝ) * ∑ idx' : Fin j → Fin d, ∫ x, (w x * partialDeriv idx' F x) ^ 2 ≤
      ∑ j' ∈ Finset.range (m + 1), (Nat.choose m j' : ℝ) * ∑ idx' : Fin j' → Fin d,
        ∫ x, (w x * partialDeriv idx' F x) ^ 2 :=
    Finset.single_le_sum (f := fun j' => (Nat.choose m j' : ℝ) * ∑ idx' : Fin j' → Fin d,
      ∫ x, (w x * partialDeriv idx' F x) ^ 2)
      (fun j' _ => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun idx' _ => hnn j' idx'))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  linarith

theorem sa12x3_cellMass_le (hd : 1 ≤ d) (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ Nm : ℝ, 0 ≤ Nm ∧ ∀ (Ψ : ℝ → Euc d → Euc d) (τ : ℝ), Function.Bijective (Ψ τ) → Continuous (Ψ τ) →
      Continuous (Function.invFun (Ψ τ)) → ∀ F : Euc d → ℝ, ContDiff ℝ ∞ F →
      (∀ (z : Fin d → ℤ) {j : ℕ} (idx : Fin j → Fin d),
        Integrable (fun x => (advCutoff χ Ψ τ (cellPt d z) x * partialDeriv idx F x) ^ 2)) →
      ∀ S : ℝ, (∀ z : Fin d → ℤ, cellEnergy m χ Ψ τ (cellPt d z) F ≤ S) →
      ∀ z' : Fin d → ℤ, cellMass m Ψ τ z' F ≤ Nm * S := by
  obtain ⟨N, C, hN, hC, hcov⟩ := fine_cell_cover hd χ hχ
  set S0 : ℝ := ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ j with hS0
  have hS00 : 0 ≤ S0 := Finset.sum_nonneg fun j _ => by positivity
  refine ⟨S0 * N, by positivity, fun Ψ τ hbij hc hci F hF hint S hS z' => ?_⟩
  have hS0' : 0 ≤ S := (sa12x2_cellEnergy_nonneg m χ Ψ τ (cellPt d 0) F).trans (hS 0)
  have hterm : ∀ {j : ℕ}, j ≤ m → ∀ idx : Fin j → Fin d,
      ∫ x in flowCell Ψ τ z', (partialDeriv idx F x) ^ 2 ≤ N * S := by
    intro j hj idx
    have hg : Measurable (partialDeriv idx F) := (sa12z3_pd_contDiff_inf hF idx).continuous.measurable
    have h1 := (hcov Ψ τ hbij hc hci (partialDeriv idx F) hg).1 z'
    have h2 : ∀ z : Fin d → ℤ, ∫⁻ x, ENNReal.ofReal ((advCutoff χ Ψ τ (cellPt d z) x * partialDeriv idx F x) ^ 2) ≤
        ENNReal.ofReal S := by
      intro z
      rw [← ofReal_integral_eq_lintegral_ofReal (hint z idx) (Filter.Eventually.of_forall fun x => sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal
        (((sa12x3_term_le_jetSq m (advCutoff χ Ψ τ (cellPt d z)) F hj idx)).trans (hS z))
    have h3 : ∫⁻ x in flowCell Ψ τ z', ENNReal.ofReal ((partialDeriv idx F x) ^ 2) ≤ ENNReal.ofReal (N * S) := by
      refine h1.trans ?_
      rw [ENNReal.ofReal_mul hN]
      have := iSup_le h2
      gcongr
    have h4 : ENNReal.ofReal (∫ x in flowCell Ψ τ z', (partialDeriv idx F x) ^ 2) ≤
        ∫⁻ x in flowCell Ψ τ z', ENNReal.ofReal ((partialDeriv idx F x) ^ 2) := by
      by_cases hi : IntegrableOn (fun x => (partialDeriv idx F x) ^ 2) (flowCell Ψ τ z')
      · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => sq_nonneg _)]
      · rw [integral_undef hi]; simp
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h4.trans h3)
  unfold cellMass
  calc _ ≤ ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ _idx : Fin j → Fin d, N * S := by
        refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun idx _ =>
          hterm (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) idx) (Nat.cast_nonneg _)
    _ = S0 * N * S := by
        rw [hS0, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [mul_assoc]

end HRS.MH.AdjointRd.Phase2SA12Construction
