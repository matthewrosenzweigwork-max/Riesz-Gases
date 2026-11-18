import HRS.MS.SA12C9

/-!
# S.A.12(c), packet E7.06 (part 8): the box energy rate, summed over ordered jets

`∑_{j ≤ m} C(m,j) ∑_{idx} ∫_{Q_L} 2 ∂^αF ∂^α(νΔF + b·∇F + G)
   ≤ -2ν D_{m,L}(F) + (d+1)^m K E_{m,L}(F) + 2 ⟨F, G⟩_{m,L}`
for periodic `F`, `b`, with `K = sa12cK d m Cb`.
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12Near HRS.MS.UniqT3
open HRS.MH.AdjointRd.Phase2SA12

variable {d : ℕ}

theorem boxDissip_nonneg (m : ℕ) (L : ℝ) (u : Euc d → ℝ) : 0 ≤ boxDissip m L u :=
  Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun idx _ =>
    Finset.sum_nonneg fun i _ => setIntegral_nonneg (sa12c20_box_meas L) fun x _ => sq_nonneg _)

theorem sa12c_box_rate_le {m : ℕ} {L : ℝ} (hL : 0 < L)
    {F G : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hFp : ∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x)
    {b : Euc d → Euc d} {Cb : ℝ} (hbC : ContDiff ℝ (m + 1) b)
    (hbp : ∀ (x : Euc d) (k : Fin d → ℤ), b (x + L • latticePt k) = b x)
    (hbb : ∀ k, 1 ≤ k → k ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ k b x‖ ≤ Cb) (ν : ℝ) :
    (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
      ∫ x in periodBox d L, 2 * (partialDeriv idx F x * partialDeriv idx
        (fun y => ν * Laplacian.laplacian F y + inner ℝ (b y) (gradient F y) + G y) x)) ≤
      -(2 * ν * boxDissip m L F) + (((d : ℝ) + 1) ^ m * sa12cK d m Cb) * boxEnergy m L F +
        2 * boxJetPair m L F G := by
  have hCb0 : 0 ≤ Cb := (norm_nonneg _).trans (hbb 1 le_rfl (by omega) 0)
  set Yi : ℝ := ∫ x in periodBox d L, sa12z3_Y m F x with hYi
  set K : ℝ := sa12cK d m Cb with hK
  have hK0 : 0 ≤ K := sa12cK_nonneg d m hCb0
  have hYE : Yi ≤ boxEnergy m L F := sa12c_intY_le_boxEnergy hF m L
  have hstep : ∀ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
      ∫ x in periodBox d L, 2 * (partialDeriv idx F x * partialDeriv idx
        (fun y => ν * Laplacian.laplacian F y + inner ℝ (b y) (gradient F y) + G y) x) ≤
      (Nat.choose m j : ℝ) * (-(2 * ν * ∑ idx : Fin j → Fin d, ∑ i : Fin d,
          ∫ x in periodBox d L, (partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2) +
        (d : ℝ) ^ j * (K * Yi) +
        2 * ∑ idx : Fin j → Fin d, ∫ x in periodBox d L, partialDeriv idx F x * partialDeriv idx G x) := by
    intro j hj
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have h1 : ∀ idx : Fin j → Fin d, ∫ x in periodBox d L, 2 * (partialDeriv idx F x * partialDeriv idx
        (fun y => ν * Laplacian.laplacian F y + inner ℝ (b y) (gradient F y) + G y) x) ≤
        -(2 * ν * ∑ i : Fin d, ∫ x in periodBox d L,
          (partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2) + K * Yi +
        ∫ x in periodBox d L, 2 * (partialDeriv idx F x * partialDeriv idx G x) :=
      fun idx => sa12c_rate_idx hjm hL hF hG hFp hbC hbp hbb ν idx
    refine (Finset.sum_le_sum fun idx _ => h1 idx).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow]
    have h2 : ∀ idx : Fin j → Fin d, ∫ x in periodBox d L, 2 * (partialDeriv idx F x * partialDeriv idx G x) =
        2 * ∫ x in periodBox d L, partialDeriv idx F x * partialDeriv idx G x :=
      fun idx => integral_const_mul _ _
    simp_rw [h2]
    rw [← Finset.mul_sum]
  refine (Finset.sum_le_sum hstep).trans ?_
  have hsplit : ∀ j : ℕ, (Nat.choose m j : ℝ) * (-(2 * ν * ∑ idx : Fin j → Fin d, ∑ i : Fin d,
          ∫ x in periodBox d L, (partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2) +
        (d : ℝ) ^ j * (K * Yi) +
        2 * ∑ idx : Fin j → Fin d, ∫ x in periodBox d L, partialDeriv idx F x * partialDeriv idx G x) =
      -(2 * ν * ((Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, ∑ i : Fin d,
          ∫ x in periodBox d L, (partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2)) +
      (Nat.choose m j : ℝ) * (d : ℝ) ^ j * (K * Yi) +
      2 * ((Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
          ∫ x in periodBox d L, partialDeriv idx F x * partialDeriv idx G x) := fun j => by ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.sum_mul, sa12c_choose_card d m]
  have hD : ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, ∑ i : Fin d,
          ∫ x in periodBox d L, (partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2 =
      boxDissip m L F := rfl
  have hP : ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
          ∫ x in periodBox d L, partialDeriv idx F x * partialDeriv idx G x = boxJetPair m L F G := rfl
  rw [hD, hP]
  have hpos : 0 ≤ ((d : ℝ) + 1) ^ m := by positivity
  have := mul_le_mul_of_nonneg_left hYE (mul_nonneg hpos hK0)
  nlinarith [this]

end HRS.MH.AdjointRd.Phase2SA12C
