import HRS.MS.SA16Y9Tl3

/-!
# S.A.16 (SA16Y9) Gc3: level-`m` dissipation of `NInt` at `s = d-1`

`sa16y9_crit_low`: for regular nonnegative `μ`, the interpolated operator `NInt d m N` satisfies `SA16IsoOp` and the dissipation inequality at level `m`
with the constant of `hHd` (copy of the corresponding part of `sa16y5_approx3`).  (`sa16y9_N_compat` of Gc2 is reused.)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q HRS.Whole.AppendixA.Phase2SA16V2

section Gc3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 3200000 in
theorem sa16y9_crit_low (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s = (d : ℝ) - 1)
    (hfar : (d : ℝ) < p * (s + 1)) (m : ℕ) (MB Λ : ℝ)
    (MCls : Matrix (Fin d) (Fin d) ℝ → Prop)
    (hHd : ∀ Wd : ℝ, 0 ≤ Wd → ∃ cN : ℝ, 0 ≤ cN ∧ ∀ {M : Matrix (Fin d) (Fin d) ℝ}, MCls M →
      (∀ i j, |M i j| ≤ MB) → ∀ {μ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) →
      sa16z_Cb 2 Wd μ → sa16y5_Dec (m + 2) Wd μ → ∀ (N' : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p),
        SA16IsoOp d (m + 1) p s M μ N' → ∀ G : WmpSpace d (m + 1 + 1) p,
          fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(sa16r_iota d m p (N' G))) ≤
            cN * jetEnergy d m p (sa16sz_iota2 d m p G)) :
    ∃ cN : ℝ, 0 ≤ cN ∧ ∀ (M : Matrix (Fin d) (Fin d) ℝ), MCls M → (∀ i j, |M i j| ≤ MB) →
      ∀ (t : ℝ), 0 < t → ∀ (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      (∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ r)) → (∀ r ∈ Icc (0 : ℝ) t, ∀ x, 0 ≤ μ r x) →
      ∀ N : ℕ, 1 ≤ N → ∀ σ ∈ Icc (0 : ℝ) t,
        SA16IsoOp d (m + 1) p s M (sa16y5_aInt d N t μ σ) (sa16y5_NInt d m N p s M t μ σ) ∧
        ∀ G : WmpSpace d (m + 1 + 1) p,
          fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(sa16r_iota d m p (sa16y5_NInt d m N p s M t μ σ G))) ≤
            cN * jetEnergy d m p (sa16sz_iota2 d m p G) := by
  obtain ⟨Wd, hWd0, hdd⟩ := sa16y5_density_data hd m Λ
  obtain ⟨Cg, hCg0, hGex⟩ := sa16y6c_G_smooth d (m + 1) hd s p MB Wd hs0 hs1 hfar hWd0
  obtain ⟨cN, hcN0, hdissM⟩ := hHd Wd hWd0
  refine ⟨cN, hcN0, fun M hMC hM t ht μ hμ hpos N hN σ hσ => ?_⟩
  have hnode : ∀ i ∈ Finset.range (N + 1), t - (i : ℝ) * t / N ∈ Icc (0 : ℝ) t := fun i hi => sa16y4_node_mem hN ht hi
  have hddi : ∀ i ∈ Finset.range (N + 1), _ := fun i hi => hdd _ (hμ _ (hnode i hi))
  have hop : ∀ i ∈ Finset.range (N + 1),
      SA16IsoOp d (m + 1) p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))
        (sa16y5_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))) ∧
      ‖sa16y5_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))‖ ≤ Cg ∧
      ∀ G : WmpSpace d (m + 1 + 1) p,
        fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G)
          (-(sa16r_iota d m p (sa16y5_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N))) G))) ≤
          cN * jetEnergy d m p (sa16sz_iota2 d m p G) := by
    intro i hi
    obtain ⟨hSB, hDec, -, -, hnn⟩ := (hddi i hi).2 N
    obtain ⟨T, hT, hTs⟩ := hGex M hM _ hSB (fun κ hκ x => hDec κ (by omega) x)
    have hTs' : SA16IsoOp d (m + 1) p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N))) T := hTs
    rw [sa16y5_Gop_eq hTs']
    exact ⟨hTs', hT, fun G => hdissM hMC hM hSB (hnn (hpos _ (hnode i hi)))
      (sa16y5_Dec_Cb hWd0 (sa16y5_Dec_mono (by omega) hDec)) (sa16y5_Dec_mono (by omega) hDec) T hTs G⟩
  have hw0 : ∀ σ : ℝ, ∀ i ∈ Finset.range (N + 1), 0 ≤ sa16y4_hat N t i σ := fun σ i _ => sa16y4_hat_nonneg N t i σ
  have hw1 : ∀ σ ∈ Icc (0 : ℝ) t, ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ = 1 := fun σ hσ =>
    sa16y4_hat_sum hN ht hσ
  have hNiso : ∀ σ ∈ Icc (0 : ℝ) t, sa16y4_Good (sa16y5_aInt d N t μ σ) ∧ SA16IsoOp d (m + 1) p s M
      (sa16y5_aInt d N t μ σ) (sa16y5_NInt d m N p s M t μ σ) := by
    intro σ hσ
    exact sa16y6c_isoop_sum hd hs0 hs1 _ (fun i => sa16y4_hat N t i σ)
      (fun i => sa16q_mol N (μ (t - (i : ℝ) * t / N)))
      (fun i => sa16y5_Gop d m p s _ (sa16q_mol N (μ (t - (i : ℝ) * t / N)))) (Finset.range (N + 1))
      (fun i hi => ((hddi i hi).2 N).2.2.1) (fun i hi => (hop i hi).1)
  have hNdiss : ∀ σ ∈ Icc (0 : ℝ) t, ∀ G : WmpSpace d (m + 1 + 1) p,
      fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(sa16r_iota d m p (sa16y5_NInt d m N p s M t μ σ G))) ≤
        cN * jetEnergy d m p (sa16sz_iota2 d m p G) := by
    intro σ hσ G
    have e : -(sa16r_iota d m p (sa16y5_NInt d m N p s M t μ σ G)) = ∑ i ∈ Finset.range (N + 1),
        sa16y4_hat N t i σ • (-(sa16r_iota d m p (sa16y5_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N))) G))) := by
      unfold sa16y5_NInt
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul,
        Finset.smul_sum, smul_neg, Finset.sum_neg_distrib]
    rw [e, map_sum]
    simp only [map_smul, smul_eq_mul]
    calc ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G)
          (-(sa16r_iota d m p (sa16y5_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N))) G)))
        ≤ ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ *
            (cN * jetEnergy d m p (sa16sz_iota2 d m p G)) :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ((hop i hi).2.2 G) (hw0 σ i hi)
      _ = cN * jetEnergy d m p (sa16sz_iota2 d m p G) := by
          rw [← Finset.sum_mul, hw1 σ hσ, one_mul]
  have hNiso' : SA16IsoOp d (m + 1) p s M (sa16y5_aInt d N t μ σ) (sa16y5_NInt d m N p s M t μ σ) :=
    (hNiso σ hσ).2
  refine ⟨hNiso', fun G => ?_⟩
  exact (hNdiss σ hσ G)

end Gc3

end HRS.Whole.AppendixA.Phase2SA16R
