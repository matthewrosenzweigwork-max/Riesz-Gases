import HRS.MS.SA12X3C7C15
import HRS.MS.SA12X3C7C11

/-!
# S.A.12 C7 (SA12X3), part C16 (7C): the far term `L²` bound by cell masses (T7 transported to the fine lattice)
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Construction
  HRS.MH.AdjointRdP

variable {d : ℕ}

/-- The `L²` inequality of `screened_far_periodic_gen` for one coset, in the form used here. -/
def sa12x3_T7Ineq (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (χ χh : Euc d → ℝ) (L : ℝ) (γ μ : Euc d → ℝ) (n' : ℕ)
    (e : Euc d) (Λ Ct : ℝ) (K : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0) : Prop :=
  ∀ (κv : Fin (n' + 1) → Fin d) (ψ : Euc d → ℝ), Measurable ψ → (∀ (x : Euc d) (k : Fin d → ℤ), ψ (x + L • latticePt k) = ψ x) →
    ∀ q : Fin d → ℤ,
      (eLpNorm (fun x => advCutoff χ Ψ τ (latticePt q + e) x *
          ∫ y in {y | y - Ψ τ (latticePt q + e) ∈ centeredBox d L},
            iteratedFDeriv ℝ (n' + 1) γ (x - y) (fun l => EuclideanSpace.single (κv l) (1 : ℝ)) *
              ((1 - advCutoff χh Ψ τ (latticePt q + e) y) *
                (partialDeriv (fun i : Fin 0 => i.elim0 : Fin 0 → Fin d) μ y * ψ y))) 2 volume) ^ 2 ≤
        ENNReal.ofReal (Ct * Λ ^ 2) * ∑' z', (K q z' : ℝ≥0∞) *
          (eLpNorm ((flowCellAt Ψ τ (latticePt z' + e)).indicator ψ) 2 volume) ^ 2

theorem sa12x3_far_K_ex (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (Λ Cb T : ℝ)
    (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ (Ct Lt : ℝ), 0 ≤ Ct ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d), IsAdvectingDrift m Cb T b →
      IsNegDriftFlow T b Ψ → ∀ (L : ℝ) (γ : Euc d → ℝ), 1 ≤ L → Lt ≤ L →
      HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ → ∀ μ : Euc d → ℝ, ContDiff ℝ ∞ μ →
      (∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x) →
      (∀ j ≤ m + 3, ∀ x : Euc d, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j μ x‖ ≤ Λ) →
      ∀ τ ∈ Icc (0 : ℝ) T, ∀ e : Euc d, ‖e‖ ≤ Real.sqrt d →
        ∃ K : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0,
          (∀ q, ∑' y, (K q y : ℝ≥0∞) ≤ ENNReal.ofReal Ct) ∧
          (∀ y, ∑' q, ENNReal.ofReal (cellWeight d q) * (K q y : ℝ≥0∞) ≤
            ENNReal.ofReal Ct * ENNReal.ofReal (cellWeight d y)) ∧
          ∀ n' : Fin (m + 1), sa12x3_T7Ineq Ψ τ χ χh L γ μ (n' : ℕ) e Λ Ct K := by
  choose C0 L0 hT7 using fun n' : Fin (m + 1) => screened_far_periodic_gen hd hs0 hsd m Λ Cb T (Real.sqrt d)
    ((n' : ℕ) + 1) ⟨by omega, by have := n'.isLt; omega⟩ χ χh hχ
  refine ⟨∑ n' : Fin (m + 1), max (C0 n') 0, ∑ n' : Fin (m + 1), |L0 n'|,
    Finset.sum_nonneg fun n' _ => le_max_right _ _, ?_⟩
  intro b Ψ hb hΨ L γ hL1 hLt hγ μ hμ hμp hμd τ hτ e he
  have hL0 : ∀ n', L0 n' ≤ L := fun n' => le_trans (le_abs_self _)
    (le_trans (Finset.single_le_sum (f := fun n' : Fin (m + 1) => |L0 n'|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ n')) hLt)
  have hex := fun n' : Fin (m + 1) => hT7 n' b Ψ hb hΨ L γ hL1 (hL0 n') hγ μ hμ hμp hμd τ hτ e he
  choose Kc hKc using hex
  refine ⟨fun q y => ∑ n', Kc n' q y, ?_, ?_, ?_⟩
  · intro q
    exact sa12x3_Ksum_row (fun n' y => Kc n' q y) C0 fun n' =>
      (le_iSup (fun z => ∑' z', (Kc n' z z' : ℝ≥0∞)) q).trans (hKc n').1
  · intro y
    exact sa12x3_Ksum_col Kc C0 y fun n' => (hKc n').2.1 y
  · intro n' κv ψ hψm hψp q
    have h1 := (hKc n').2.2 0 (by omega) (fun i : Fin 0 => i.elim0) κv ψ hψm hψp q
    refine h1.trans ?_
    have hC : C0 n' ≤ ∑ n'' : Fin (m + 1), max (C0 n'') 0 :=
      (le_max_left _ _).trans (Finset.single_le_sum (f := fun n'' : Fin (m + 1) => max (C0 n'') 0)
        (fun _ _ => le_max_right _ _) (Finset.mem_univ n'))
    gcongr with z'
    exact Finset.single_le_sum (f := fun n'' : Fin (m + 1) => Kc n'' q z')
        (fun _ _ => zero_le) (Finset.mem_univ n')

end HRS.MH.AdjointRd.Phase2SA12Near
