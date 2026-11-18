import HRS.MS.SA12C3
import HRS.MS.SA12X3C9F

/-!
# S.A.12(c), packet E7.06 (part 2): the box energy functionals

`boxEnergy m L u = ∑_{j ≤ m} C(m,j) ∑_{idx} ∫_{Q_L} (∂^idx u)²` (ordered indices, binomial weights),
`boxDissip`, `boxJetPair`; periodicity of jets; comparison of `∫_{Q_L} Y` with the box energy.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12Near HRS.MS.UniqT3

variable {d : ℕ}

/-- The box energy `E_{m,L}(u) = ∑_{j ≤ m} C(m,j) ∑_{idx ∈ [d]^j} ∫_{[0,L)^d} (∂^idx u)²`. -/
def boxEnergy (m : ℕ) (L : ℝ) (u : Euc d → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) *
    ∑ idx : Fin j → Fin d, ∫ x in periodBox d L, (partialDeriv idx u x) ^ 2

/-- The box dissipation `∑_{j ≤ m} C(m,j) ∑_{idx} ∑_i ∫_{[0,L)^d} (∂_i ∂^idx u)²`. -/
def boxDissip (m : ℕ) (L : ℝ) (u : Euc d → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, ∑ i : Fin d,
    ∫ x in periodBox d L, (partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) u x) ^ 2

/-- The mixed box pairing `∑_{j ≤ m} C(m,j) ∑_{idx} ∫_{[0,L)^d} ∂^idx u ∂^idx v`. -/
def boxJetPair (m : ℕ) (L : ℝ) (u v : Euc d → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) *
    ∑ idx : Fin j → Fin d, ∫ x in periodBox d L, partialDeriv idx u x * partialDeriv idx v x

/-- All jets of a periodic function are periodic. -/
theorem sa12c_pd_periodic {L : ℝ} {u : Euc d → ℝ}
    (hu : ∀ (x : Euc d) (k : Fin d → ℤ), u (x + L • latticePt k) = u x) {n : ℕ} (idx : Fin n → Fin d)
    (x : Euc d) (k : Fin d → ℤ) :
    partialDeriv idx u (x + L • latticePt k) = partialDeriv idx u x := by
  have hfun : (fun y' => u (y' + L • latticePt (d := d) k)) = u := funext fun y' => hu y' k
  have h2 := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := u) n (L • latticePt (d := d) k) x
  rw [hfun] at h2
  unfold partialDeriv
  rw [h2]

theorem sa12c_pd_cont {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) {n : ℕ} (idx : Fin n → Fin d) :
    Continuous (partialDeriv idx u) :=
  (sa12z3_pd_contDiff_inf hu idx).continuous

theorem sa12c_Y_cont {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) (m : ℕ) : Continuous (sa12z3_Y m u) := by
  unfold sa12z3_Y
  exact continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun γ _ => (sa12c_pd_cont hu γ).pow 2

theorem boxEnergy_nonneg (m : ℕ) (L : ℝ) (u : Euc d → ℝ) : 0 ≤ boxEnergy m L u :=
  Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun idx _ =>
    setIntegral_nonneg (sa12c20_box_meas L) fun x _ => sq_nonneg _)

/-- `∫_{Q_L} Y ≤` box energy (binomial coefficients are `≥ 1`). -/
theorem sa12c_intY_le_boxEnergy {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) (m : ℕ) (L : ℝ) :
    ∫ x in periodBox d L, sa12z3_Y m u x ≤ boxEnergy m L u := by
  have hint : ∀ r (γ : Fin r → Fin d), IntegrableOn (fun x => partialDeriv γ u x ^ 2) (periodBox d L) :=
    fun r γ => sa12v_integrableOn_box L ((sa12c_pd_cont hu γ).pow 2)
  unfold sa12z3_Y boxEnergy
  rw [integral_finset_sum _ fun r _ => integrable_finset_sum _ fun γ _ => hint r γ]
  refine Finset.sum_le_sum fun r hr => ?_
  rw [integral_finset_sum _ fun γ _ => hint r γ]
  have h1 : (1 : ℝ) ≤ (Nat.choose m r : ℝ) := by
    have := Nat.choose_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr))
    exact_mod_cast this
  have h0 : 0 ≤ ∑ γ : Fin r → Fin d, ∫ x in periodBox d L, partialDeriv γ u x ^ 2 :=
    Finset.sum_nonneg fun γ _ => setIntegral_nonneg (sa12c20_box_meas L) fun x _ => sq_nonneg _
  nlinarith

/-- `∑_{j ≤ m} C(m,j) d^j = (d+1)^m`. -/
theorem sa12c_choose_card (d m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ j = ((d : ℝ) + 1) ^ m := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]

end HRS.MH.AdjointRd.Phase2SA12C
