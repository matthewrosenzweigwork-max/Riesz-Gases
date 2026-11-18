import HRS.MS.SA16Y10Nd2

/-!
# S.A.16 (SA16Y10) Nd3: `sa16y10_node_diff_sub`

For regular densities `μ₁, μ₂` (level `m+3`, size `Λ`) with `‖D^κ(μ₁-μ₂)‖ ≤ δ (1+|x|)^{-(d+3)}` (`κ ≤ m+2`):
`‖(G(mol N μ₁) - G(mol N μ₂)) ∘ ι²‖ ≤ K δ`, `G = sa16so_G d m p s M`, `K` independent of `N, μ_a, Λ, δ`.
-/

set_option autoImplicit false

noncomputable section
open scoped ContDiff
open Filter

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA MeasureTheory Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem sa16y10_node_diff_sub (d m : ℕ) (hd : 2 ≤ d) (s p MB Λ : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs2 : s ≤ (d : ℝ) - 2) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) →
      ∀ μ₁ μ₂ : Euc d → ℝ, IsRegularDensityW (m + 3) Λ μ₁ → IsRegularDensityW (m + 3) Λ μ₂ →
      ∀ δ : ℝ, 0 ≤ δ →
      (∀ κ ≤ m + 2, ∀ x, ‖iteratedFDeriv ℝ κ (fun y => μ₁ y - μ₂ y) x‖ ≤ δ * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) →
      ∀ N : ℕ,
        ‖(sa16so_G d m p s M (sa16q_mol N μ₁) - sa16so_G d m p s M (sa16q_mol N μ₂)).comp
            (sa16sz_iota2 d m p)‖ ≤ K * δ := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨CG, CG1, hCG, hCG1, hnl⟩ := sa16y4_nl_pair d m hd1 s p MB Λ hs0 hs2 hfar
  obtain ⟨K0, hK0, hN⟩ := sa16y10_nl_diff_sub d m s p MB hs0 hs2 hfar
  refine ⟨K0 * ((d : ℝ) ^ (m + 2) * 2 ^ (d + 3)), by positivity, fun M hM μ₁ μ₂ h1 h2 δ hδ hdec N => ?_⟩
  obtain ⟨T1a, T0a, -, -, -, hrep0a, -⟩ := hnl M hM μ₁ h1 N
  obtain ⟨T1b, T0b, -, -, -, hrep0b, -⟩ := hnl M hM μ₂ h2 N
  have hGa : sa16so_G d m p s M (sa16q_mol N μ₁) = T0a := sa16so_G_eq hrep0a
  have hGb : sa16so_G d m p s M (sa16q_mol N μ₂) = T0b := sa16so_G_eq hrep0b
  obtain ⟨hSBa, -⟩ := sa16y4_mol_data3 hd1 h1 N
  obtain ⟨hSBb, -⟩ := sa16y4_mol_data3 hd1 h2 N
  obtain ⟨hC1, hb1⟩ := (sa16q_reg_data h1).1.continuous, sa16q_reg_abs h1
  obtain ⟨hC2, hb2⟩ := (sa16q_reg_data h2).1.continuous, sa16q_reg_abs h2
  -- the difference coefficient
  set g : Euc d → ℝ := fun y => μ₁ y - μ₂ y with hg
  have hmol : sa16q_mol N g = fun y => sa16q_mol N μ₁ y - sa16q_mol N μ₂ y :=
    sa16y10_mol_sub N hC1 hC2 hb1 hb2
  have hgc : ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) g :=
    ((sa16q_reg_data h1).1.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 3))).sub
      ((sa16q_reg_data h2).1.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 3)))
  have hgbd : ∀ y, |g y| ≤ max Λ 0 + max Λ 0 := fun y =>
    (abs_sub _ _).trans (add_le_add (hb1 y) (hb2 y))
  have hSBg : sa16q_SB (sa16q_mol N g) :=
    sa16q_mol_SB N (hC1.sub hC2) hgbd
  have hdec' := sa16y10_mol_weight hd1 N hgc hdec
  obtain ⟨T, hTn, hTrep⟩ := hN M hM (sa16q_mol N g) hSBg ((d : ℝ) ^ (m + 2) * 2 ^ (d + 3) * δ) (by positivity) hdec'
  -- operator of the difference on `W^m`
  have hSubA : SA16SubOp d m p s M (sa16q_mol N μ₁) T0a := hrep0a
  have hSubB : SA16SubOp d m p s M (fun y => (-1 : ℝ) * sa16q_mol N μ₂ y) ((-1 : ℝ) • T0b) :=
    sa16y4_subop_smul hd hs0 hs2 M (-1) (sa16q_SB_C1 hSBb) hrep0b
  have hSubAB := sa16y4_subop_add hd hs0 hs2 M (sa16q_SB_C1 hSBa) (sa16q_SB_C1 (sa16y10_SB_smul hSBb (-1))) hSubA hSubB
  have hfun : (fun y => sa16q_mol N μ₁ y + (-1 : ℝ) * sa16q_mol N μ₂ y) = sa16q_mol N g := by
    rw [hmol]; funext y; ring
  rw [hfun] at hSubAB
  have hdiff : sa16so_G d m p s M (sa16q_mol N μ₁) - sa16so_G d m p s M (sa16q_mol N μ₂) = T0a + (-1 : ℝ) • T0b := by
    rw [hGa, hGb]; ext1 G
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, sub_eq_add_neg]
    congr 1
    exact (neg_one_smul ℝ _).symm
  have heq : (sa16so_G d m p s M (sa16q_mol N μ₁) - sa16so_G d m p s M (sa16q_mol N μ₂)).comp (sa16sz_iota2 d m p) = T := by
    rw [hdiff]
    refine sa16so_clm_ext fun φ => sa16r_wrep_inj d m p _ _ ?_
    have e1 := hSubAB φ
    have e2 := hTrep φ
    simp only [ContinuousLinearMap.comp_apply, sa16sz_iota2_Jcc]
    exact e1.trans e2.symm
  rw [heq]
  exact hTn.trans (le_of_eq (by ring))

end HRS.Whole.AppendixA.Phase2SA16R

end
