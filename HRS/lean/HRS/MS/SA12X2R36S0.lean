import HRS.MS.SA12X2R36Z3

/-!
# S.A.12 R36 (SA12X3), part S0: general cover bound

If `f² ≤ K₁ Y + K₂ Yd` pointwise (`Y` = jets of order `≤ m`, `Yd` = the order-`(m+1)` snoc jets, the dissipation
level) and `W ≥ 1` on `{f ≠ 0}`, then `∫ f² ≤ K₁ ∑ cellEnergy + K₂ ∑ cellDissip`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd

variable {d : ℕ}

/-- The dissipation-level jets. -/
def sa12x2_Yd (m : ℕ) (F : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ∑ i : Fin d,
    partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x ^ 2

theorem sa12x2_Yd_nonneg (m : ℕ) (F : Euc d → ℝ) (x : Euc d) : 0 ≤ sa12x2_Yd m F x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sa12x2_Z_le (m : ℕ) (F : Euc d → ℝ) (x : Euc d) :
    HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m F x ≤ sa12z3_Y m F x + sa12x2_Yd m F x := by
  have hsplit : HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m F x = sa12z3_Y m F x +
      ∑ γ : Fin (m + 1) → Fin d, partialDeriv γ F x ^ 2 := by
    unfold HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z sa12z3_Y
    rw [Finset.sum_range_succ]
  have hP : ∑ γ : Fin (m + 1) → Fin d, partialDeriv γ F x ^ 2 =
      ∑ idx : Fin m → Fin d, ∑ i : Fin d, partialDeriv (Fin.snoc idx i : Fin (m + 1) → Fin d) F x ^ 2 :=
    HRS.MH.AdjointRd.Phase2SA12.sa12_sum_snoc d m (fun γ => partialDeriv γ F x ^ 2)
  have hPle : ∑ idx : Fin m → Fin d, ∑ i : Fin d, partialDeriv (Fin.snoc idx i : Fin (m + 1) → Fin d) F x ^ 2 ≤
      sa12x2_Yd m F x := by
    have := Finset.single_le_sum (f := fun j => ∑ idx : Fin j → Fin d, ∑ i : Fin d,
        partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x ^ 2)
      (fun j _ => Finset.sum_nonneg fun idx _ => Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_self m))
    simpa [sa12x2_Yd] using this
  rw [hsplit, hP]
  linarith

theorem sa12x2_cover_gen (m : ℕ) {E : Finset (Fin d → ℤ)} {χ : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d}
    {τ : ℝ} {z : Fin d → ℤ} {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F)
    (hω : ∀ k ∈ E, Continuous (advCutoff χ Ψ τ (cellPt d (z + k))) ∧
      HasCompactSupport (advCutoff χ Ψ τ (cellPt d (z + k))))
    {K1 K2 : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) {f : Euc d → ℝ} (hfc : Continuous f)
    (hfs : HasCompactSupport f)
    (hfK : ∀ x, f x ^ 2 ≤ K1 * sa12z3_Y m F x + K2 * sa12x2_Yd m F x)
    (hfW : ∀ x, f x ≠ 0 → 1 ≤ sa12z3_W E χ Ψ τ z x) :
    ∫ x, f x ^ 2 ≤ K1 * (∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F) +
      K2 * ∑ k ∈ E, cellDissip m χ Ψ τ (cellPt d (z + k)) F := by
  have hWnn : ∀ x, 0 ≤ sa12z3_W E χ Ψ τ z x := fun x => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hYnn : ∀ x, 0 ≤ sa12z3_Y m F x := sa12z3_Y_nonneg m F
  have hYdnn : ∀ x, 0 ≤ sa12x2_Yd m F x := sa12x2_Yd_nonneg m F
  have hWc : Continuous (sa12z3_W E χ Ψ τ z) := by
    unfold sa12z3_W
    exact continuous_finsetSum _ fun k hk => ((hω k hk).1).pow 2
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
    exact continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun γ _ => ((hpdc r γ).pow 2)
  have hYdc : Continuous (sa12x2_Yd m F) := by
    unfold sa12x2_Yd
    exact continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun γ _ =>
      continuous_finsetSum _ fun i _ => ((hpdc (r + 1) _).pow 2)
  have hpt : ∀ x, f x ^ 2 ≤ K1 * (sa12z3_W E χ Ψ τ z x * sa12z3_Y m F x) +
      K2 * (sa12z3_W E χ Ψ τ z x * sa12x2_Yd m F x) := by
    intro x
    by_cases hf0 : f x = 0
    · rw [hf0]
      have h1 := mul_nonneg hK1 (mul_nonneg (hWnn x) (hYnn x))
      have h2 := mul_nonneg hK2 (mul_nonneg (hWnn x) (hYdnn x))
      simpa using add_nonneg h1 h2
    · have h1 := hfW x hf0
      calc f x ^ 2 ≤ K1 * sa12z3_Y m F x + K2 * sa12x2_Yd m F x := hfK x
        _ ≤ _ := by
          have e1 : sa12z3_Y m F x ≤ sa12z3_W E χ Ψ τ z x * sa12z3_Y m F x :=
            le_mul_of_one_le_left (hYnn x) h1
          have e2 : sa12x2_Yd m F x ≤ sa12z3_W E χ Ψ τ z x * sa12x2_Yd m F x :=
            le_mul_of_one_le_left (hYdnn x) h1
          nlinarith [mul_le_mul_of_nonneg_left e1 hK1, mul_le_mul_of_nonneg_left e2 hK2]
  have hIWY : Integrable (fun x => sa12z3_W E χ Ψ τ z x * sa12z3_Y m F x) :=
    (hWc.mul hYc).integrable_of_hasCompactSupport hWcs.mul_right
  have hIWYd : Integrable (fun x => sa12z3_W E χ Ψ τ z x * sa12x2_Yd m F x) :=
    (hWc.mul hYdc).integrable_of_hasCompactSupport hWcs.mul_right
  have hIf : Integrable (fun x => f x ^ 2) := by
    have hc2 : HasCompactSupport (fun x => f x ^ 2) := hfs.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact Continuous.integrable_of_hasCompactSupport (f := fun x => f x ^ 2) (hfc.pow 2) hc2
  have hstep : ∫ x, f x ^ 2 ≤ ∫ x, (K1 * (sa12z3_W E χ Ψ τ z x * sa12z3_Y m F x) +
      K2 * (sa12z3_W E χ Ψ τ z x * sa12x2_Yd m F x)) :=
    integral_mono hIf ((hIWY.const_mul K1).add (hIWYd.const_mul K2)) hpt
  rw [integral_add (hIWY.const_mul K1) (hIWYd.const_mul K2), integral_const_mul, integral_const_mul] at hstep
  refine hstep.trans (add_le_add (mul_le_mul_of_nonneg_left (sa12z3_e_le m hF hω) hK1)
    (mul_le_mul_of_nonneg_left ?_ hK2))
  exact sa12x2_dissip_cover m hF hω

end HRS.MH.AdjointRd.Phase2SA12Near
