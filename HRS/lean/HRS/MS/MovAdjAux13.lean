import HRS.MS.MovAdjAux12

/-!
# S6.7 (packet P3, part 2): pointwise bounds for `ψ ∈ Σ^M` and for `x_iψ`

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

`s67_psi_bounds`: for `M > d/2 + j + 5` there is `K` (depending on `d, j, M` only) such that every continuous `ψ ∈ Σ^M` with `x_iψ ∈ L²`
is `C^{j+4}` with `‖D^kψ‖_∞ ≤ K ‖ψ‖_{Σ^M}` (`k ≤ j+4`), and `x_iψ ∈ C^{j+3}` with `‖D^k(x_iψ)‖_∞ ≤ K‖ψ‖_{Σ^M}` (`k ≤ j+3`).
(Sobolev embedding `mn_sobolev_emb_gen` for `ψ ∈ Σ^M` and for `x_iψ ∈ Σ^{M-1}`, the latter by the ladder `s67_xmul_osc`.)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.Mov63

variable {d : ℕ}

theorem s67_psi_bounds (j M : ℕ) (hM : (d : ℝ) / 2 + j + 5 < M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ : Euc d → ℝ, Continuous ψ → MemOsc (M : ℝ) ψ →
      (∀ i : Fin d, MemLp (fun x => x i * ψ x) 2 (volume : Measure (Euc d))) →
      ContDiff ℝ ((j + 4 : ℕ) : WithTop ℕ∞) ψ ∧
        (∀ k ≤ j + 4, ∀ x, ‖iteratedFDeriv ℝ k ψ x‖ ≤ K * oscNorm (M : ℝ) ψ) ∧
        ∀ i : Fin d, ContDiff ℝ ((j + 3 : ℕ) : WithTop ℕ∞) (fun x => x i * ψ x) ∧
          ∀ k ≤ j + 3, ∀ x, ‖iteratedFDeriv ℝ k (fun x => x i * ψ x) x‖ ≤ K * oscNorm (M : ℝ) ψ := by
  have hM0 : M ≠ 0 := by
    rintro rfl
    have : (0 : ℝ) ≤ (d : ℝ) / 2 + j := by positivity
    simp at hM; linarith
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hcast : ((M' + 1 : ℕ) : ℝ) = (M' : ℝ) + 1 := by push_cast; ring
  have h1 : ((j + 4 : ℕ) : ℝ) + (d : ℝ) / 2 < ((M' + 1 : ℕ) : ℝ) := by push_cast at hM ⊢; linarith
  have h2 : ((j + 3 : ℕ) : ℝ) + (d : ℝ) / 2 < (M' : ℝ) := by push_cast at hM ⊢; linarith
  obtain ⟨Cs, hCs0, hCs⟩ := mn_sobolev_emb_gen (d := d) (j + 4) (M' + 1) h1
  obtain ⟨Cs', hCs'0, hCs'⟩ := mn_sobolev_emb_gen (d := d) (j + 3) M' h2
  set κ : ℝ := Real.sqrt (2 ^ |(M' : ℝ) + 1|) with hκ
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  refine ⟨Cs + Cs' * κ, by positivity, fun ψ hψc hψ hx => ?_⟩
  have hN0 : 0 ≤ oscNorm ((M' + 1 : ℕ) : ℝ) ψ := Real.sqrt_nonneg _
  obtain ⟨g, hg, hae, hb⟩ := hCs ψ hψ
  have hψg : ψ = g := mn_ae_eq_cont hψc hg.continuous hae
  subst hψg
  refine ⟨hg, fun k hk x => (hb k hk x).trans ?_, fun i => ?_⟩
  · exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hCs'0 hκ0]) hN0
  have hψ' : MemOsc ((M' : ℝ) + 1) ψ := by rw [← hcast]; exact hψ
  obtain ⟨hxm, hxn⟩ := s67_xmul_osc i (M' : ℝ) hψ' (hx i)
  have hxc : Continuous (fun x : Euc d => x i * ψ x) :=
    ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous).mul hψc
  obtain ⟨g', hg', hae', hb'⟩ := hCs' (fun x => x i * ψ x) hxm
  have hxg : (fun x : Euc d => x i * ψ x) = g' := mn_ae_eq_cont hxc hg'.continuous hae'
  rw [hxg]
  refine ⟨hg', fun k hk x => (hb' k hk x).trans ?_⟩
  have hnorm : oscNorm (M' : ℝ) (fun x => x i * ψ x) ≤ κ * oscNorm ((M' + 1 : ℕ) : ℝ) ψ := by
    rw [hcast]; exact hxn
  calc Cs' * oscNorm (M' : ℝ) (fun x => x i * ψ x) ≤ Cs' * (κ * oscNorm ((M' + 1 : ℕ) : ℝ) ψ) :=
        mul_le_mul_of_nonneg_left hnorm hCs'0
    _ ≤ (Cs + Cs' * κ) * oscNorm ((M' + 1 : ℕ) : ℝ) ψ := by nlinarith [mul_nonneg hCs0 hN0]

end HRS.MS.MovAdj
