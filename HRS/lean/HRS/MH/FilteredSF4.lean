import HRS.MH.FilteredSF4Aux2

/-!
# Packet SF4 `sf4_bVec_contDiff` (regularity of `y ↦ b_{y,j}` for `γ > d/2 + n + 1`)

Statement copied verbatim from `HRS/MH/FilteredSpec.lean` (namespace `HRS.MH.Filtered` there, `HRS.MH.FilteredP` here).
Route: dyadic shells `S_s` of the lattice, `SF2` (shell cardinality), `SF3` (Pythagoras for a finite orthogonal block),
`gfb3_norm_iter_term` (scalar derivative bound), `contDiff_tsum` on the shell sums `G_s`, and regrouping of
`gfb3_bVec_hasSum` by `HasSum.tsum_fiberwise`.  See `FilteredSF4Aux1.lean` for the exponent bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators

namespace HRS.MH.FilteredP

open HRS HRS.Uniform HRS.Uniform.Q54c HRS.GF

variable {d : ℕ}

theorem sf4_bVec_contDiff (n : ℕ) {γ : ℝ} (hγ : (d : ℝ) / 2 + n + 1 < γ) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧ ∀ j : Fin d,
      ContDiff ℝ n (fun y : Euc d => bVec γ j (Torus.mk y)) ∧
      ∀ i : ℕ, i ≤ n → ∀ y : Euc d,
        ‖iteratedFDeriv ℝ i (fun y : Euc d => bVec γ j (Torus.mk y)) y‖ ≤ K i := by
  classical
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hγ' : (d : ℝ) / 2 + 1 < γ := by linarith
  have ha : (d : ℝ) / 2 < γ - 1 - n := by linarith
  obtain ⟨C, hC0, hC⟩ := sf2_shell_card (d := d) ((d : ℝ) / 2 + (γ - 1 - n)) (by linarith)
  set M : ℝ := Real.sqrt (2 * C * (2 : ℝ) ^ ((d : ℝ) / 2 + (γ - 1 - n))) with hM
  set ρ : ℝ := Real.sqrt ((2 : ℝ) ^ ((d : ℝ) / 2 - (γ - 1 - n))) with hρ
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ < 1 := by
    rw [hρ, Real.sqrt_lt' one_pos, one_pow]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hsum : Summable (fun s : ℕ => M * ρ ^ s) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left M
  refine ⟨fun _ => ∑' s : ℕ, M * ρ ^ s, fun _ => tsum_nonneg fun s => by positivity, fun j => ?_⟩
  set G : ℕ → Euc d → NegSobolev d γ := fun s z =>
    ∑ k ∈ (sf4_shell_finite hC s).1.toFinset, gfb3_term γ j k z with hG
  have hGs : ∀ s, ContDiff ℝ n (G s) := fun s =>
    ContDiff.sum fun k _ => gfb3_contDiff_term γ j k n
  have hGb : ∀ (i : ℕ) (s : ℕ) (y : Euc d), i ≤ n → ‖iteratedFDeriv ℝ i (G s) y‖ ≤ M * ρ ^ s :=
    fun i s y hi => sf4_block_bound n hγ hC j s i hi y
  have heq : (fun y : Euc d => bVec γ j (Torus.mk y)) = fun y => ∑' s, G s y := by
    funext y
    have h := (gfb3_bVec_hasSum hγ' j y).tsum_fiberwise sf4_shell
    have hfib : ∀ s : ℕ, ∑' b : (sf4_shell ⁻¹' {s} : Set (NonzeroLattice d)), gfb3_term γ j b y = G s y := by
      intro s
      have hset : (sf4_shell ⁻¹' {s} : Set (NonzeroLattice d)) =
          ↑((sf4_shell_finite hC s).1.toFinset) := by
        ext k; simp
      rw [tsum_congr_set_coe (fun b => gfb3_term γ j b y) hset]
      exact Finset.tsum_subtype' ((sf4_shell_finite hC s).1.toFinset) (fun b => gfb3_term γ j b y)
    simp only [hfib] at h
    exact h.tsum_eq.symm
  have hcd : ContDiff ℝ n (fun y : Euc d => bVec γ j (Torus.mk y)) := by
    rw [heq]
    exact contDiff_tsum (v := fun _ s => M * ρ ^ s) hGs (fun _ _ => hsum)
      (fun i s y hi => hGb i s y (by exact_mod_cast hi))
  refine ⟨hcd, fun i hi y => ?_⟩
  rw [heq, iteratedFDeriv_tsum_apply (v := fun _ s => M * ρ ^ s) (N := n) hGs
    (fun _ _ => hsum) (fun i s y hi => hGb i s y (by exact_mod_cast hi)) (by exact_mod_cast hi)]
  have hsn : Summable fun s => ‖iteratedFDeriv ℝ i (G s) y‖ :=
    hsum.of_nonneg_of_le (fun s => norm_nonneg _) (fun s => hGb i s y hi)
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum (fun s => hGb i s y hi) hsum)

end HRS.MH.FilteredP
