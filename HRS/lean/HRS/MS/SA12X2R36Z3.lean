import HRS.MS.SA12X2R36Z2

/-!
# S.A.12 R36 (SA12X2), part Z3: energy-level cover bound

If `f² ≤ K·Y` pointwise (`Y` = jets of order `≤ m`, `sa12z3_Y`) and `W ≥ 1` on `{f ≠ 0}`, then
`∫ f² ≤ K ∑_{k∈E} cellEnergy`. (No dissipation enters.)
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x2_cover_energy_Y (m : ℕ) {E : Finset (Fin d → ℤ)} {χ : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d}
    {τ : ℝ} {z : Fin d → ℤ} {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F)
    (hω : ∀ k ∈ E, Continuous (advCutoff χ Ψ τ (cellPt d (z + k))) ∧
      HasCompactSupport (advCutoff χ Ψ τ (cellPt d (z + k))))
    {K : ℝ} (hK0 : 0 ≤ K) {f : Euc d → ℝ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hfK : ∀ x, f x ^ 2 ≤ K * sa12z3_Y m F x)
    (hfW : ∀ x, f x ≠ 0 → 1 ≤ sa12z3_W E χ Ψ τ z x) :
    ∫ x, f x ^ 2 ≤ K * ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F := by
  have hWnn : ∀ x, 0 ≤ sa12z3_W E χ Ψ τ z x := fun x => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hYnn : ∀ x, 0 ≤ sa12z3_Y m F x := fun x =>
    Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun γ _ => sq_nonneg _
  have hWc : Continuous (sa12z3_W E χ Ψ τ z) := by
    unfold sa12z3_W
    exact continuous_finset_sum _ fun k hk => ((hω k hk).1).pow 2
  have hWcs : HasCompactSupport (sa12z3_W E χ Ψ τ z) := by
    refine HasCompactSupport.intro (K := ⋃ k ∈ E, tsupport (advCutoff χ Ψ τ (cellPt d (z + k))))
      (Finset.isCompact_biUnion E fun k hk => (hω k hk).2.isCompact) ?_
    intro x hx
    unfold sa12z3_W
    refine Finset.sum_eq_zero fun k hk => ?_
    have hxk : x ∉ tsupport (advCutoff χ Ψ τ (cellPt d (z + k))) :=
      fun h => hx (Set.mem_iUnion₂.2 ⟨k, hk, h⟩)
    rw [image_eq_zero_of_notMem_tsupport hxk]
    simp
  have hpdc : ∀ (n : ℕ) (idx : Fin n → Fin d), Continuous (partialDeriv idx F) := fun n idx =>
    (sa12z3_pd_contDiff_inf hF idx).continuous
  have hYc : Continuous (sa12z3_Y m F) := by
    unfold sa12z3_Y
    exact continuous_finset_sum _ fun r _ => continuous_finset_sum _ fun γ _ => ((hpdc r γ).pow 2)
  have hpt : ∀ x, f x ^ 2 ≤ K * (sa12z3_W E χ Ψ τ z x * sa12z3_Y m F x) := by
    intro x
    by_cases hf0 : f x = 0
    · rw [hf0]
      have := mul_nonneg hK0 (mul_nonneg (hWnn x) (hYnn x))
      simpa using this
    · have h1 := hfW x hf0
      calc f x ^ 2 ≤ K * sa12z3_Y m F x := hfK x
        _ ≤ K * (sa12z3_W E χ Ψ τ z x * sa12z3_Y m F x) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (hYnn x) h1) hK0
  have hIWY : Integrable (fun x => sa12z3_W E χ Ψ τ z x * sa12z3_Y m F x) :=
    (hWc.mul hYc).integrable_of_hasCompactSupport hWcs.mul_right
  have hIf : Integrable (fun x => f x ^ 2) := by
    have hc2 : HasCompactSupport (fun x => f x ^ 2) := hfs.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact Continuous.integrable_of_hasCompactSupport (f := fun x => f x ^ 2) (hfc.pow 2) hc2
  have hstep : ∫ x, f x ^ 2 ≤ ∫ x, K * (sa12z3_W E χ Ψ τ z x * sa12z3_Y m F x) :=
    integral_mono hIf (hIWY.const_mul K) hpt
  rw [integral_const_mul] at hstep
  exact hstep.trans (mul_le_mul_of_nonneg_left (sa12z3_e_le m hF hω) hK0)

end HRS.MH.AdjointRd.Phase2SA12Near
