import HRS.MS.SA12Z3NearN7

/-!
# S.A.12 R36 (SA12X2), part D: dissipation-weighted cover (κ > 0 analogue of `sa12z3_e_le`)

`∫ W · Yd ≤ ∑_{k∈E} cellDissip`, where `W = ∑_{k∈E} χ_{z+k}²` and `Yd = ∑_{j≤m} ∑_{idx} ∑_i (∂^{snoc idx i} F)²`
(the order-`(m+1)` jets of `F`, i.e. the dissipation level).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x2_dissip_cover (m : ℕ) {E : Finset (Fin d → ℤ)} {χ : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d}
    {τ : ℝ} {z : Fin d → ℤ} {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F)
    (hω : ∀ k ∈ E, Continuous (advCutoff χ Ψ τ (cellPt d (z + k))) ∧
      HasCompactSupport (advCutoff χ Ψ τ (cellPt d (z + k)))) :
    ∫ x, sa12z3_W E χ Ψ τ z x * (∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ∑ i : Fin d,
        partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x ^ 2) ≤
      ∑ k ∈ E, cellDissip m χ Ψ τ (cellPt d (z + k)) F := by
  -- integrability of a single weighted square
  have hint : ∀ k ∈ E, ∀ (j : ℕ) (idx : Fin j → Fin d) (i : Fin d),
      Integrable (fun x => (advCutoff χ Ψ τ (cellPt d (z + k)) x *
        partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2) volume := by
    intro k hk j idx i
    have hc := (hω k hk).1
    have hcs := (hω k hk).2
    have hpd : Continuous (partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F) :=
      (sa12z3_pd_contDiff_inf hF _).continuous
    exact Continuous.integrable_of_hasCompactSupport (f := fun x => (advCutoff χ Ψ τ (cellPt d (z + k)) x *
      partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2) ((hc.mul hpd).pow 2)
      ((hcs.mul_right (f' := partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F)).comp_left
        (g := fun t : ℝ => t ^ 2) (by simp))
  -- pointwise: the weight is a sum over the cells
  have hpt : ∀ x, sa12z3_W E χ Ψ τ z x * (∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ∑ i : Fin d,
      partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x ^ 2) =
      ∑ k ∈ E, ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ∑ i : Fin d,
        (advCutoff χ Ψ τ (cellPt d (z + k)) x * partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2 := by
    intro x
    unfold sa12z3_W
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- the integral splits over cells and tuples
  have hnest : ∀ k ∈ E, ∫ x, ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ∑ i : Fin d,
      (advCutoff χ Ψ τ (cellPt d (z + k)) x * partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2 =
      ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ∑ i : Fin d,
        ∫ x, (advCutoff χ Ψ τ (cellPt d (z + k)) x * partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2 := by
    intro k hk
    rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun idx _ =>
      integrable_finset_sum _ fun i _ => hint k hk j idx i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finset_sum _ fun idx _ => integrable_finset_sum _ fun i _ => hint k hk j idx i]
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [integral_finset_sum _ fun i _ => hint k hk j idx i]
  -- each cell: the binomial weights dominate
  have hcell : ∀ k ∈ E, ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ∑ i : Fin d,
      ∫ x, (advCutoff χ Ψ τ (cellPt d (z + k)) x * partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2 ≤
      cellDissip m χ Ψ τ (cellPt d (z + k)) F := by
    intro k hk
    unfold cellDissip dissipSq
    refine Finset.sum_le_sum fun j hj => ?_
    have hc : (1 : ℝ) ≤ (m.choose j : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    have hnn : 0 ≤ ∑ idx : Fin j → Fin d, ∑ i : Fin d,
        ∫ x, (advCutoff χ Ψ τ (cellPt d (z + k)) x * partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2 :=
      Finset.sum_nonneg fun idx _ => Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
    exact le_mul_of_one_le_left hnn hc
  -- assemble
  have hsplit : ∫ x, sa12z3_W E χ Ψ τ z x * (∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ∑ i : Fin d,
      partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x ^ 2) =
      ∑ k ∈ E, ∫ x, ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ∑ i : Fin d,
        (advCutoff χ Ψ τ (cellPt d (z + k)) x * partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x) ^ 2 := by
    rw [← integral_finset_sum]
    · exact integral_congr_ae (Eventually.of_forall hpt)
    · intro k hk
      exact integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun idx _ =>
        integrable_finset_sum _ fun i _ => hint k hk j idx i
  rw [hsplit]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [hnest k hk]
  exact hcell k hk

end HRS.MH.AdjointRd.Phase2SA12Near
