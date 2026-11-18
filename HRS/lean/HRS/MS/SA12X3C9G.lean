import HRS.MS.SA12X3C9F

/-!
# S.A.12 C9 (SA12X3): `cell_local_operator`
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem cell_local_operator (hd : 1 ≤ d) (m : ℕ) (Cb T νbar : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ (E : Finset (Fin d → ℤ)) (A : ℝ), 0 ≤ A ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ → ∀ ν : ℝ, 0 ≤ ν → ν ≤ νbar →
      ∀ (G : ℝ → Euc d → ℝ) (t : ℝ), t ∈ Icc (0 : ℝ) T → ∀ F : ℝ → Euc d → ℝ, IsClassicalSol m ν b G t F →
      (∀ τ ∈ Icc (0 : ℝ) t, BddJets m (F τ)) → ∀ τ ∈ Icc (0 : ℝ) t, ∀ z : Fin d → ℤ,
        cellRate m χ Ψ τ (cellPt d z) ν (b τ) (F τ) (G τ) ≤
          -ν * cellDissip m χ Ψ τ (cellPt d z) (F τ) +
            A * ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) (F τ) +
            2 * jetPair m (advCutoff χ Ψ τ (cellPt d z)) (F τ) (G τ) := by
  obtain ⟨E, hE⟩ := sa12z3_E_exists hd
  obtain ⟨B, R, hB, hR1, hf⟩ := advected_cutoff_jets d hd m Cb T χ χh hχ
  set S0 : ℝ := ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ j with hS0
  have hS00 : 0 ≤ S0 := Finset.sum_nonneg fun j _ => by positivity
  set Cb' : ℝ := max Cb 0 with hCb'
  set νb : ℝ := max νbar 0 with hνb
  set K0 : ℝ := 4 * νb * d * B ^ 2 + d * Cb' + 1 + ((d : ℝ) * (Cb' * 2 ^ m)) ^ 2 * sa12z3_cT d m with hK0
  have hK00 : 0 ≤ K0 := by
    have := sa12z3_cT_nonneg d m
    positivity
  refine ⟨E, K0 * S0, by positivity, ?_⟩
  intro b Ψ hb hΨ ν hν hνν G t ht F hF hbdd τ hτ z
  have hτT : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans ht.2⟩
  set c0 : Euc d := cellPt d z with hc0
  have hcut := hf b Ψ hb hΨ τ hτT c0
  have hωk : ∀ k ∈ E, Continuous (advCutoff χ Ψ τ (cellPt d (z + k))) ∧
      HasCompactSupport (advCutoff χ Ψ τ (cellPt d (z + k))) := fun k _ =>
    ⟨(hf b Ψ hb hΨ τ hτT _).1.1.continuous,
      sa12x2_advCutoff_hasCompactSupport (hτT.1.trans hτT.2) hb hΨ hτT hχ.1.2.1 _⟩
  have hw1c : ContDiff ℝ 1 (advCutoff χ Ψ τ c0) := hcut.1.1.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
  have hwcs : HasCompactSupport (advCutoff χ Ψ τ c0) :=
    sa12x2_advCutoff_hasCompactSupport (hτT.1.trans hτT.2) hb hΨ hτT hχ.1.2.1 c0
  have hwb : ∀ x, |advCutoff χ Ψ τ c0 x| ≤ 1 := by
    intro x
    have h : advCutoff χ Ψ τ c0 x ∈ Icc (0 : ℝ) 1 := hχ.1.2.2.2.1 _
    exact abs_le.2 ⟨by linarith [h.1], h.2⟩
  have hWc : Continuous (sa12z3_W E χ Ψ τ z) := by
    unfold sa12z3_W
    exact continuous_finsetSum _ fun k hk => ((hωk k hk).1).pow 2
  have hwW : ∀ x ∈ tsupport (advCutoff χ Ψ τ c0), 1 ≤ sa12z3_W E χ Ψ τ z x := by
    have hcl : IsClosed {x | 1 ≤ sa12z3_W E χ Ψ τ z x} := isClosed_le continuous_const hWc
    refine fun x hx => (closure_minimal ?_ hcl : tsupport (advCutoff χ Ψ τ c0) ⊆ _) hx
    intro y hy
    have := sa12z3_adv_ne_norm_lt hχ Ψ τ c0 hy
    exact sa12z3_W_ge_one hχ hE Ψ τ z y (by linarith)
  have hB1 : ∀ x, ‖fderiv ℝ (advCutoff χ Ψ τ c0) x‖ ≤ B := fun x => by
    rw [← norm_iteratedFDeriv_one]
    exact (hcut.2.1 1 (by omega) x).1
  have hbC : ContDiff ℝ (m + 1) (b τ) := hb.smooth τ hτT
  have hbb : ∀ k, 1 ≤ k → k ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ k (b τ) x‖ ≤ Cb' := fun k hk1 hkm x =>
    (hb.deriv_bdd τ hτT k hk1 hkm x).trans (le_max_left _ _)
  have hFs := (hF.smooth τ hτ).1
  have hGs := (hF.smooth τ hτ).2
  have hper : ∀ j ≤ m, ∀ idx : Fin j → Fin d,
      ∫ x, (2 * advCutoff χ Ψ τ c0 x ^ 2 * (partialDeriv idx (F τ) x * partialDeriv idx
        (fun y => ν * Laplacian.laplacian (F τ) y + inner ℝ (b τ y) (gradient (F τ) y) + G τ y) x) +
        2 * advCutoff χ Ψ τ c0 x * inner ℝ (b τ x) (gradient (advCutoff χ Ψ τ c0) x) *
          partialDeriv idx (F τ) x ^ 2) ≤
      -(ν * ∑ i : Fin d, ∫ x, (advCutoff χ Ψ τ c0 x * partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) (F τ) x) ^ 2) +
        K0 * ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) (F τ) +
        ∫ x, 2 * advCutoff χ Ψ τ c0 x ^ 2 * (partialDeriv idx (F τ) x * partialDeriv idx (G τ) x) := by
    intro j hj idx
    have h := sa12x3_rate_idx (hn := hj) hFs hGs hωk hw1c hwcs hwb hwW hB1 hbC hbb ν hν idx
    refine h.trans ?_
    have hEn0 : 0 ≤ ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) (F τ) :=
      Finset.sum_nonneg fun k _ => sa12x2_cellEnergy_nonneg m χ Ψ τ _ _
    have hcoef : 4 * ν * d * B ^ 2 + d * Cb' + 1 + ((d : ℝ) * (Cb' * 2 ^ m)) ^ 2 * sa12z3_cT d m ≤ K0 := by
      have : 4 * ν * d * B ^ 2 ≤ 4 * νb * d * B ^ 2 := by
        have : ν ≤ νb := hνν.trans (le_max_left _ _)
        gcongr
      linarith
    have := mul_le_mul_of_nonneg_right hcoef hEn0
    linarith
  set En : ℝ := ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) (F τ) with hEn
  clear_value En
  unfold cellRate
  have hle : ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
      ∫ x, (2 * advCutoff χ Ψ τ c0 x ^ 2 * (partialDeriv idx (F τ) x * partialDeriv idx
        (fun y => ν * Laplacian.laplacian (F τ) y + inner ℝ (b τ y) (gradient (F τ) y) + G τ y) x) +
        2 * advCutoff χ Ψ τ c0 x * inner ℝ (b τ x) (gradient (advCutoff χ Ψ τ c0) x) *
          partialDeriv idx (F τ) x ^ 2) ≤
      ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
        (-(ν * ∑ i : Fin d, ∫ x, (advCutoff χ Ψ τ c0 x * partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) (F τ) x) ^ 2) +
          K0 * En + ∫ x, 2 * advCutoff χ Ψ τ c0 x ^ 2 * (partialDeriv idx (F τ) x * partialDeriv idx (G τ) x)) :=
    Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun idx _ => hper j (Nat.lt_succ_iff.mp (Finset.mem_range.1 hj)) idx) (Nat.cast_nonneg _)
  refine hle.trans (le_of_eq ?_)
  unfold cellDissip dissipSq jetPair
  simp only [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_neg_distrib, mul_neg, ← Finset.mul_sum]
  have e1 : ∀ j ∈ Finset.range (m + 1), ∀ idx : Fin j → Fin d,
      ∫ x, 2 * advCutoff χ Ψ τ c0 x ^ 2 * (partialDeriv idx (F τ) x * partialDeriv idx (G τ) x) =
      2 * ∫ x, advCutoff χ Ψ τ c0 x ^ 2 * (partialDeriv idx (F τ) x * partialDeriv idx (G τ) x) := fun j _ idx => by
    rw [← integral_const_mul]; refine integral_congr_ae (Eventually.of_forall fun x => ?_); simp only; ring
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · rw [neg_mul]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · rw [hS0, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.sum_congr rfl (fun idx _ => e1 j hj idx), ← Finset.mul_sum]
    ring

end HRS.MH.AdjointRd.Phase2SA12Construction
