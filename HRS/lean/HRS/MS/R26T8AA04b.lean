import HRS.MS.R26T8AA04

/-!
# S8.2 observed-time layer, packet T8A.A04 (main): exact gradient and Laplacian of an ordered pair statistic
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole

theorem r26t8a_a04_sum_erase_gen {M : Type*} [AddCommGroup M] {m : ℕ} (i : Fin (m + 1))
    (f : Fin (m + 1) → M) :
    ∑ j ∈ Finset.univ.erase i, f j = ∑ k : Fin m, f (i.succAbove k) := by
  have h1 := Fin.sum_univ_succAbove f i
  have h2 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i)
  exact add_left_cancel (h2.trans h1)

theorem r26t8a_a04_grad {d m : ℕ} {Q : Euc d → Euc d → ℝ}
    (hQ : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2})
    (hsym : ∀ x y, Q x y = Q y x) (X : EucConfig d (m + 1)) (i : Fin (m + 1))
    (hX : ∀ j, j ≠ i → X j ≠ X i) :
    HRS.MS.Phase2S82.configGrad (HRS.MS.Phase2S82.pairStatistic (N := m + 1) Q) X i =
      (2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) •
        ∑ j ∈ Finset.univ.erase i, HRS.MS.Phase2S82.pairGradX Q (X i) (X j) := by
  rw [r26t8a_a04_sum_erase_gen i (fun j => HRS.MS.Phase2S82.pairGradX Q (X i) (X j))]
  have hk : ∀ k : Fin m, HasGradientAt (fun y => Q y (X (i.succAbove k)))
      (HRS.MS.Phase2S82.pairGradX Q (X i) (X (i.succAbove k))) (X i) := fun k =>
    (((r26t8a_a04_cd hQ (fun h => hX _ (Fin.succAbove_ne i k) h.symm)).differentiableAt
      (by norm_num))).hasGradientAt
  set c0 : ℝ := HRS.MS.Phase2S82.pairStatistic (N := m + 1) Q
    (i.insertNth (X i) (fun k => X (i.succAbove k)) : EucConfig d (m + 1)) with hc0
  set cN : ℝ := ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) with hcN
  have hform : (fun y => HRS.MS.Phase2S82.pairStatistic (N := m + 1) Q (Function.update X i y)) =
      fun y => c0 + 2 * cN * ∑ k : Fin m, (Q y (X (i.succAbove k)) -
        Q (X i) (X (i.succAbove k))) := by
    funext y
    exact HRS.MS.S82P2.s82p2_phi_formula hsym i X y
  have hsub : ∀ k : Fin m, HasGradientAt
      (fun y => Q y (X (i.succAbove k)) - Q (X i) (X (i.succAbove k)))
      (HRS.MS.Phase2S82.pairGradX Q (X i) (X (i.succAbove k))) (X i) := fun k => by
    have := (hasGradientAt_iff_hasFDerivAt.1 (hk k)).sub_const (Q (X i) (X (i.succAbove k)))
    exact hasGradientAt_iff_hasFDerivAt.2 this
  have hsum : HasGradientAt (fun y => c0 + 2 * cN * ∑ k : Fin m, (Q y (X (i.succAbove k)) -
        Q (X i) (X (i.succAbove k))))
      ((2 * cN) • ∑ k : Fin m, HRS.MS.Phase2S82.pairGradX Q (X i) (X (i.succAbove k))) (X i) := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have h1 : HasFDerivAt (fun y => ∑ k : Fin m, (Q y (X (i.succAbove k)) -
        Q (X i) (X (i.succAbove k))))
        (∑ k : Fin m, (InnerProductSpace.toDual ℝ (Euc d))
          (HRS.MS.Phase2S82.pairGradX Q (X i) (X (i.succAbove k)))) (X i) :=
      HasFDerivAt.fun_sum fun k _ => hasGradientAt_iff_hasFDerivAt.1 (hsub k)
    have h2 := (h1.const_mul (2 * cN)).const_add c0
    rw [map_smul, map_sum]
    convert h2 using 1
  show gradient (fun y => HRS.MS.Phase2S82.pairStatistic (N := m + 1) Q (Function.update X i y)) (X i) = _
  rw [hform]
  exact hsum.gradient

theorem r26t8a_pair_generator_differentiation {d N : ℕ}
    (Q : Euc d → Euc d → ℝ) (hQ : ContDiffOn ℝ 2 (Function.uncurry Q) {p | p.1≠p.2})
    (hsym : ∀ x y, Q x y=Q y x) (X : EucConfig d N) (hX : X∉eucCollisionSet d N) :
    (∀ i, HRS.MS.Phase2S82.configGrad (HRS.MS.Phase2S82.pairStatistic Q) X i =
      (2*(N:ℝ)^(-(3/2:ℝ))) • ∑ j∈Finset.univ.erase i, HRS.MS.Phase2S82.pairGradX Q (X i) (X j)) ∧
    (∑ i, Laplacian.laplacian (fun y => HRS.MS.Phase2S82.pairStatistic Q (Function.update X i y)) (X i)) =
      (N:ℝ)^(-(3/2:ℝ)) * ∑ i, ∑ j∈Finset.univ.erase i,
        (Laplacian.laplacian (fun x => Q x (X j)) (X i)+
          Laplacian.laplacian (Q (X i)) (X j)) := by
  cases N with
  | zero => exact ⟨fun i => i.elim0, by simp⟩
  | succ m =>
    have hne : ∀ i j : Fin (m + 1), j ≠ i → X j ≠ X i := fun i j hji hEq => hX ⟨j, i, hji, hEq⟩
    refine ⟨fun i => r26t8a_a04_grad hQ hsym X i (hne i), ?_⟩
    simp only [r26t8a_a04_lap_phi hQ hsym X _ (hne _)]
    obtain ⟨G, hG⟩ : ∃ G : Fin (m + 1) → Fin (m + 1) → ℝ, ∀ i j,
        Laplacian.laplacian (fun x => Q x (X j)) (X i) = G i j := ⟨_, fun _ _ => rfl⟩
    have hH : ∀ i j, Laplacian.laplacian (Q (X i)) (X j) = G j i := by
      intro i j
      have : Q (X i) = fun x => Q x (X i) := funext fun x => hsym _ _
      rw [this, hG]
    simp only [hG, hH]
    have hsw : ∑ i, ∑ j ∈ Finset.univ.erase i, G j i = ∑ i, ∑ j ∈ Finset.univ.erase i, G i j := by
      refine (Finset.sum_comm' (s := (Finset.univ : Finset (Fin (m + 1)))) (t := fun i => Finset.univ.erase i)
        (t' := (Finset.univ : Finset (Fin (m + 1)))) (s' := fun j => Finset.univ.erase j)
        (f := fun i j => G j i) ?_)
      intro x y
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      tauto
    have e : ∑ i, ∑ j ∈ Finset.univ.erase i, (G i j + G j i) =
        ∑ i, ∑ j ∈ Finset.univ.erase i, G i j + ∑ i, ∑ j ∈ Finset.univ.erase i, G j i := by
      simp only [Finset.sum_add_distrib]
    rw [e, hsw, ← Finset.mul_sum]
    ring

end HRS.MS.R26T8A

end
