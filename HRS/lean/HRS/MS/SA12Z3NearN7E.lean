import HRS.MS.SA12Z3NearN7D
import HRS.MS.SA12BuildC12
import HRS.MS.SA12CellR35

/-!
# S.A.12 N7 (SA12Z3), part E: the neighbour set and the cell weight

* `sa12z3_E_exists`: a finite `E` with `CoversBall8 E`;
* `sa12z3_W`: `W = ∑_{k ∈ E} (χ_{z+k}^τ)²`; `W ≥ 1` wherever `‖Ψ_τ^{-1} x - c_z‖ ≤ 8`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem sa12z3_E_exists (hd : 1 ≤ d) : ∃ E : Finset (Fin d → ℤ), CoversBall8 E := by
  have hfin := HRS.MH.AdjointRd.Phase2SA12Construction.sa12c12_finite_cells hd (9 : ℝ)
  refine ⟨hfin.toFinset, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := HRS.MS.UniqC3.exists_cellPt_near hd x
  refine Set.mem_iUnion₂.2 ⟨k, ?_, ?_⟩
  · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    have h1 : ‖x‖ ≤ 8 := by simpa using hx
    have h2 : ‖cellPt d k‖ ≤ ‖x‖ + ‖x - cellPt d k‖ := by
      calc ‖cellPt d k‖ = ‖x - (x - cellPt d k)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - cellPt d k‖ := norm_sub_le _ _
    linarith
  · rw [mem_closedBall, dist_eq_norm]
    linarith

theorem sa12z3_cellPt_add (z k : Fin d → ℤ) : cellPt d (z + k) = cellPt d z + cellPt d k := by
  ext i
  simp [cellPt, latticePt, mul_add]

/-- The weight. -/
def sa12z3_W (E : Finset (Fin d → ℤ)) (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ)
    (z : Fin d → ℤ) (x : Euc d) : ℝ :=
  ∑ k ∈ E, advCutoff χ Ψ τ (cellPt d (z + k)) x ^ 2

theorem sa12z3_W_nonneg (E : Finset (Fin d → ℤ)) (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ)
    (z : Fin d → ℤ) (x : Euc d) : 0 ≤ sa12z3_W E χ Ψ τ z x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sa12z3_W_ge_one {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) {E : Finset (Fin d → ℤ)}
    (hE : CoversBall8 E) (Ψ : ℝ → Euc d → Euc d) (τ : ℝ) (z : Fin d → ℤ) (x : Euc d)
    (h8 : ‖Function.invFun (Ψ τ) x - cellPt d z‖ ≤ 8) : 1 ≤ sa12z3_W E χ Ψ τ z x := by
  have hmem : Function.invFun (Ψ τ) x - cellPt d z ∈ closedBall (0 : Euc d) 8 := by simpa using h8
  obtain ⟨k, hk, hkb⟩ := Set.mem_iUnion₂.1 (hE hmem)
  have hk1 : ‖Function.invFun (Ψ τ) x - cellPt d z - cellPt d k‖ ≤ 1 := by
    rw [mem_closedBall, dist_eq_norm] at hkb; exact hkb
  have hχ1 : advCutoff χ Ψ τ (cellPt d (z + k)) x = 1 := by
    unfold advCutoff
    rw [sa12z3_cellPt_add, ← sub_sub]
    exact hχ.1.2.2.2.2 _ (by simpa using hk1)
  unfold sa12z3_W
  calc (1 : ℝ) = advCutoff χ Ψ τ (cellPt d (z + k)) x ^ 2 := by rw [hχ1]; norm_num
    _ ≤ _ := Finset.single_le_sum (f := fun k => advCutoff χ Ψ τ (cellPt d (z + k)) x ^ 2)
      (fun _ _ => sq_nonneg _) hk

/-- Where the cutoff `χ` is nonzero the preimage point is within `2`. -/
theorem sa12z3_adv_ne_norm_lt {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) (Ψ : ℝ → Euc d → Euc d)
    (τ : ℝ) (z' : Euc d) {x : Euc d} (hx : advCutoff χ Ψ τ z' x ≠ 0) :
    ‖Function.invFun (Ψ τ) x - z'‖ < 2 := by
  have h : χ (Function.invFun (Ψ τ) x - z') ≠ 0 := hx
  have hts : Function.invFun (Ψ τ) x - z' ∈ tsupport χ := subset_tsupport _ h
  have := hχ.1.2.2.1 hts
  simpa using this

theorem sa12z3_advh_ne_norm_lt {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) (Ψ : ℝ → Euc d → Euc d)
    (τ : ℝ) (z' : Euc d) {x : Euc d} (hx : advCutoff χh Ψ τ z' x ≠ 0) :
    ‖Function.invFun (Ψ τ) x - z'‖ < 8 := by
  have h : χh (Function.invFun (Ψ τ) x - z') ≠ 0 := hx
  have hts : Function.invFun (Ψ τ) x - z' ∈ tsupport χh := subset_tsupport _ h
  have := hχ.2.2.2.1 hts
  simpa using this

/-- `χ_{z'}^τ` vanishes where `χ̂_{z'}^τ` does. -/
theorem sa12z3_adv_support_le {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) (Ψ : ℝ → Euc d → Euc d)
    (τ : ℝ) (z' : Euc d) :
    Function.support (advCutoff χ Ψ τ z') ⊆ Function.support (advCutoff χh Ψ τ z') := by
  intro x hx
  have h1 := sa12z3_adv_ne_norm_lt hχ Ψ τ z' hx
  have h2 : χh (Function.invFun (Ψ τ) x - z') = 1 :=
    hχ.2.2.2.2.2 _ (by rw [mem_closedBall, dist_zero_right]; linarith)
  show χh (Function.invFun (Ψ τ) x - z') ≠ 0
  rw [h2]; exact one_ne_zero

end HRS.MH.AdjointRd.Phase2SA12Near
