import HRS.MS.S82P2Grad1

/-!
# S8.2 observed-time layer, packet T8A.A04: exact gradient and Laplacian of an ordered pair statistic

For `Q` symmetric and `C²` off the diagonal and a collision-free configuration `X`:
`∇_i Φ_Q(X) = 2 N^{-3/2} ∑_{j ≠ i} ∇_x Q(X_i, X_j)` and
`∑_i Δ_i Φ_Q(X) = N^{-3/2} ∑_i ∑_{j ≠ i} (Δ_x Q(·, X_j)(X_i) + Δ Q(X_i, ·)(X_j))`.
Both follow from the exact decomposition `s82p2_phi_formula` of the pair statistic in one coordinate.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole

theorem r26t8a_a04_cd {d : ℕ} {Q : Euc d → Euc d → ℝ}
    (hQ : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2})
    {x z : Euc d} (hxz : x ≠ z) : ContDiffAt ℝ 2 (fun y => Q y z) x := by
  have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have h1 : ContDiffAt ℝ 2 (Function.uncurry Q) (x, z) := hQ.contDiffAt (hopen.mem_nhds hxz)
  exact h1.comp x (contDiffAt_id.prodMk contDiffAt_const)

theorem r26t8a_a04_lap_sum {d : ℕ} {ι : Type*} (s : Finset ι) (g : ι → Euc d → ℝ) (x : Euc d)
    (hg : ∀ k ∈ s, ContDiffAt ℝ 2 (g k) x) :
    Laplacian.laplacian (fun y => ∑ k ∈ s, g k y) x = ∑ k ∈ s, Laplacian.laplacian (g k) x := by
  classical
  revert hg
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hg
    have h1 := hg a (Finset.mem_insert_self _ _)
    have h2 : ContDiffAt ℝ 2 (fun y => ∑ k ∈ s, g k y) x :=
      ContDiffAt.sum fun k hk => hg k (Finset.mem_insert_of_mem hk)
    simp only [Finset.sum_insert ha]
    rw [← ih fun k hk => hg k (Finset.mem_insert_of_mem hk)]
    exact h1.laplacian_add h2

theorem r26t8a_a04_sum_erase {m : ℕ} (i : Fin (m + 1)) (f : Fin (m + 1) → ℝ) :
    ∑ j ∈ Finset.univ.erase i, f j = ∑ k : Fin m, f (i.succAbove k) := by
  have h1 := Fin.sum_univ_succAbove f i
  have h2 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
  linarith

theorem r26t8a_a04_lap_phi {d m : ℕ} {Q : Euc d → Euc d → ℝ}
    (hQ : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2})
    (hsym : ∀ x y, Q x y = Q y x) (X : EucConfig d (m + 1)) (i : Fin (m + 1))
    (hX : ∀ j, j ≠ i → X j ≠ X i) :
    Laplacian.laplacian (fun y => HRS.MS.Phase2S82.pairStatistic (N := m + 1) Q (Function.update X i y)) (X i) =
      2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) *
        ∑ j ∈ Finset.univ.erase i, Laplacian.laplacian (fun x => Q x (X j)) (X i) := by
  set c0 : ℝ := HRS.MS.Phase2S82.pairStatistic (N := m + 1) Q
    (i.insertNth (X i) (fun k => X (i.succAbove k)) : EucConfig d (m + 1)) with hc0
  set cN : ℝ := ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) with hcN
  have cd : ∀ k : Fin m, ContDiffAt ℝ 2 (fun y => Q y (X (i.succAbove k))) (X i) := fun k =>
    r26t8a_a04_cd hQ (fun h => hX _ (Fin.succAbove_ne i k) h.symm)
  have hform : (fun y => HRS.MS.Phase2S82.pairStatistic (N := m + 1) Q (Function.update X i y)) =
      fun y => c0 + 2 * cN * ∑ k : Fin m, (Q y (X (i.succAbove k)) -
        Q (X i) (X (i.succAbove k))) := by
    funext y
    exact HRS.MS.S82P2.s82p2_phi_formula hsym i X y
  have hS : Laplacian.laplacian (fun y => ∑ k : Fin m, (Q y (X (i.succAbove k)) -
        Q (X i) (X (i.succAbove k)))) (X i) =
      ∑ k : Fin m, Laplacian.laplacian (fun y => Q y (X (i.succAbove k))) (X i) := by
    rw [r26t8a_a04_lap_sum Finset.univ (fun k y => Q y (X (i.succAbove k)) -
      Q (X i) (X (i.succAbove k))) (X i) (fun k _ => (cd k).sub contDiffAt_const)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h2 : Laplacian.laplacian (fun y => Q y (X (i.succAbove k)) - Q (X i) (X (i.succAbove k))) (X i) =
        Laplacian.laplacian (fun y => Q y (X (i.succAbove k))) (X i) -
          Laplacian.laplacian (fun _ : Euc d => Q (X i) (X (i.succAbove k))) (X i) :=
      (cd k).laplacian_sub (contDiffAt_const (c := Q (X i) (X (i.succAbove k))))
    rw [h2]
    simp
  have hSd : ContDiffAt ℝ 2 (fun y => ∑ k : Fin m, (Q y (X (i.succAbove k)) -
        Q (X i) (X (i.succAbove k)))) (X i) :=
    ContDiffAt.sum fun k _ => (cd k).sub contDiffAt_const
  rw [hform]
  have h1 : (fun y => c0 + 2 * cN * ∑ k : Fin m, (Q y (X (i.succAbove k)) -
        Q (X i) (X (i.succAbove k)))) =
      (fun _ => c0) + (2 * cN) • (fun y => ∑ k : Fin m, (Q y (X (i.succAbove k)) -
        Q (X i) (X (i.succAbove k)))) := rfl
  have hSd' : ContDiffAt ℝ 2 ((2 * cN) • (fun y => ∑ k : Fin m, (Q y (X (i.succAbove k)) -
        Q (X i) (X (i.succAbove k))))) (X i) := hSd.const_smul (2 * cN)
  have hA := contDiffAt_const (c := c0) (E := Euc d) (x := X i) |>.laplacian_add hSd'
  have hB := InnerProductSpace.laplacian_smul (2 * cN) hSd
  rw [h1, hA, hB, hS, r26t8a_a04_sum_erase i
      (fun j => Laplacian.laplacian (fun x => Q x (X j)) (X i))]
  simp

end HRS.MS.R26T8A

end
