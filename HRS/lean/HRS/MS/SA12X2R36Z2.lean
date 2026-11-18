import HRS.MS.SA12X2R36Z1
import HRS.MS.SA12X2R36D
import HRS.MS.SA12CellR33

/-!
# S.A.12 R36 (SA12X2), part Z2: cover-weighted bound of `∫ f²` by cell energies and dissipations

If `f² ≤ K·Z` pointwise and `W ≥ 1` on `{f ≠ 0}` (cover weight `W = ∑_{k∈E} χ_{z+k}²`), then
`∫ f² ≤ K (∑_{k∈E} cellEnergy + ∑_{k∈E} cellDissip)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x2_cover_energy (m : ℕ) {E : Finset (Fin d → ℤ)} {χ : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d}
    {τ : ℝ} {z : Fin d → ℤ} {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F)
    (hω : ∀ k ∈ E, Continuous (advCutoff χ Ψ τ (cellPt d (z + k))) ∧
      HasCompactSupport (advCutoff χ Ψ τ (cellPt d (z + k))))
    {K : ℝ} (hK0 : 0 ≤ K) {f : Euc d → ℝ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hfK : ∀ x, f x ^ 2 ≤ K * HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m F x)
    (hfW : ∀ x, f x ≠ 0 → 1 ≤ sa12z3_W E χ Ψ τ z x) :
    ∫ x, f x ^ 2 ≤ K * ((∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F) +
      ∑ k ∈ E, cellDissip m χ Ψ τ (cellPt d (z + k)) F) := by
  have hWnn : ∀ x, 0 ≤ sa12z3_W E χ Ψ τ z x := fun x =>
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hZnn : ∀ x, 0 ≤ HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m F x :=
    fun x => HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z_nonneg m F x
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
  -- the pieces of Z
  have hYc : Continuous (sa12z3_Y m F) := by
    unfold sa12z3_Y
    exact continuous_finset_sum _ fun r _ => continuous_finset_sum _ fun γ _ => ((hpdc r γ).pow 2)
  have hZc : Continuous (HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m F) := by
    unfold HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z
    exact continuous_finset_sum _ fun l _ => continuous_finset_sum _ fun γ _ => ((hpdc l γ).pow 2)
  have hYdc : Continuous (fun x => ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ∑ i : Fin d,
      partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x ^ 2) :=
    continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun idx _ =>
      continuous_finset_sum _ fun i _ => ((hpdc (j + 1) _).pow 2)
  -- pointwise: f² ≤ K · W · Z
  have hpt1 : ∀ x, f x ^ 2 ≤ K * (sa12z3_W E χ Ψ τ z x * HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m F x) := by
    intro x
    by_cases hf0 : f x = 0
    · rw [hf0]
      have := mul_nonneg hK0 (mul_nonneg (hWnn x) (hZnn x))
      simpa using this
    · have h1 := hfW x hf0
      calc f x ^ 2 ≤ K * HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m F x := hfK x
        _ ≤ K * (sa12z3_W E χ Ψ τ z x * HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m F x) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (hZnn x) h1) hK0
  -- Z = Y + P_{m+1} ≤ Y + Yd
  have hZle : ∀ x, HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m F x ≤ sa12z3_Y m F x +
      ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ∑ i : Fin d,
        partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x ^ 2 := by
    intro x
    have hsplit : HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m F x = sa12z3_Y m F x +
        ∑ γ : Fin (m + 1) → Fin d, partialDeriv γ F x ^ 2 := by
      unfold HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z sa12z3_Y
      rw [Finset.sum_range_succ]
    have hP : ∑ γ : Fin (m + 1) → Fin d, partialDeriv γ F x ^ 2 =
        ∑ idx : Fin m → Fin d, ∑ i : Fin d, partialDeriv (Fin.snoc idx i : Fin (m + 1) → Fin d) F x ^ 2 :=
      HRS.MH.AdjointRd.Phase2SA12.sa12_sum_snoc d m (fun γ => partialDeriv γ F x ^ 2)
    have hPle : ∑ idx : Fin m → Fin d, ∑ i : Fin d, partialDeriv (Fin.snoc idx i : Fin (m + 1) → Fin d) F x ^ 2 ≤
        ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ∑ i : Fin d,
          partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x ^ 2 := by
      have := Finset.single_le_sum (f := fun j => ∑ idx : Fin j → Fin d, ∑ i : Fin d,
          partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x ^ 2)
        (fun j _ => Finset.sum_nonneg fun idx _ => Finset.sum_nonneg fun i _ => sq_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_self m))
      simpa using this
    rw [hsplit, hP]
    linarith
  -- integrability
  have hWY_cs : HasCompactSupport (fun x => sa12z3_W E χ Ψ τ z x * sa12z3_Y m F x) :=
    hWcs.mul_right
  have hWZ_cs : HasCompactSupport (fun x => sa12z3_W E χ Ψ τ z x *
      HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m F x) := hWcs.mul_right
  have hWYd_cs : HasCompactSupport (fun x => sa12z3_W E χ Ψ τ z x *
      ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ∑ i : Fin d,
        partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x ^ 2) := hWcs.mul_right
  have hIWY : Integrable (fun x => sa12z3_W E χ Ψ τ z x * sa12z3_Y m F x) :=
    (hWc.mul hYc).integrable_of_hasCompactSupport hWY_cs
  have hIWYd : Integrable (fun x => sa12z3_W E χ Ψ τ z x *
      ∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ∑ i : Fin d,
        partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x ^ 2) :=
    (hWc.mul hYdc).integrable_of_hasCompactSupport hWYd_cs
  have hIWZ : Integrable (fun x => sa12z3_W E χ Ψ τ z x *
      HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m F x) :=
    (hWc.mul hZc).integrable_of_hasCompactSupport hWZ_cs
  have hIf : Integrable (fun x => f x ^ 2) := by
    have hc2 : HasCompactSupport (fun x => f x ^ 2) := hfs.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
    exact Continuous.integrable_of_hasCompactSupport (f := fun x => f x ^ 2) (hfc.pow 2) hc2
  -- ∫ f² ≤ K ∫ W Z ≤ K (∫ W Y + ∫ W Yd)
  have hstep1 : ∫ x, f x ^ 2 ≤ ∫ x, K * (sa12z3_W E χ Ψ τ z x *
      HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m F x) :=
    integral_mono hIf (hIWZ.const_mul K) hpt1
  have hstep2 : ∫ x, sa12z3_W E χ Ψ τ z x * HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m F x ≤
      (∫ x, sa12z3_W E χ Ψ τ z x * sa12z3_Y m F x) +
        ∫ x, sa12z3_W E χ Ψ τ z x * (∑ j ∈ Finset.range (m + 1), ∑ idx : Fin j → Fin d, ∑ i : Fin d,
          partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) F x ^ 2) := by
    rw [← integral_add hIWY hIWYd]
    refine integral_mono hIWZ (hIWY.add hIWYd) fun x => ?_
    have h1 := hZle x
    have h2 := mul_le_mul_of_nonneg_left h1 (hWnn x)
    linarith
  have he := sa12z3_e_le m hF hω
  have hd := sa12x2_dissip_cover m hF hω
  rw [integral_const_mul] at hstep1
  calc ∫ x, f x ^ 2 ≤ K * ∫ x, sa12z3_W E χ Ψ τ z x * HRS.MH.AdjointRd.Phase2SA12.sa12x2_Z m F x :=
        hstep1
    _ ≤ K * ((∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F) +
          ∑ k ∈ E, cellDissip m χ Ψ τ (cellPt d (z + k)) F) :=
        mul_le_mul_of_nonneg_left (hstep2.trans (add_le_add he hd)) hK0

end HRS.MH.AdjointRd.Phase2SA12Near
