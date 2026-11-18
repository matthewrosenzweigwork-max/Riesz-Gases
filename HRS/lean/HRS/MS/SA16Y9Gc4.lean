import HRS.MS.SA16Y9Tl4

/-!
# S.A.16 (SA16Y9) Gc4: level-`m` dissipation of the fractional `NInt` and level compatibility of the fractional operators

`sa16y9_frac_low`: for regular nonnegative `μ`, `sa16y5f_NInt d m N` satisfies `SA16FOp` and the dissipation inequality at level `m` with the constant of
`Sa16FracEx` (copy of the corresponding part of `sa16y5f_approx3`).  `sa16y9_fN_compat`: `ι²_m N^{(m+2)} = N^{(m)} ι²_{m+2}` for two `SA16FOp` operators of the same density.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q HRS.Whole.AppendixA.Phase2SA16V2

section Gc4
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y9_fN_compat {m : ℕ} {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ρ : EuclideanSpace ℝ (Fin d) → ℝ}
    {N1 : WmpSpace d (m + 2 + 1 + 1) p →L[ℝ] WmpSpace d (m + 2) p}
    {N0 : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p}
    (h1 : SA16FOp d (m + 2) p s M ρ N1) (h0 : SA16FOp d m p s M ρ N0) :
    (sa16sz_iota2 d m p).comp N1 = N0.comp (sa16sz_iota2 d (m + 2) p) := by
  refine sa16so_clm_ext fun φ => sa16r_wrep_inj d m p _ _ ?_
  simp only [ContinuousLinearMap.comp_apply]
  rw [sa16sz_iota2_Jcc]
  filter_upwards [sa16y9_wrep_iota2 (p := p) m (N1 (sa16r_Jcc d (m + 2 + 1 + 1) p φ)), h1 φ, h0 φ] with x e1 e2 e3
  rw [e1, e2, e3]

set_option maxHeartbeats 3200000 in
theorem sa16y9_frac_low (hd : 1 ≤ d) (s : ℝ) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s) (m : ℕ) (MB Λ : ℝ)
    (MCls : Matrix (Fin d) (Fin d) ℝ → Prop) (hFex : Sa16FracEx d s p MB MCls m) :
    ∃ cN : ℝ, 0 ≤ cN ∧ ∀ (M : Matrix (Fin d) (Fin d) ℝ), MCls M → (∀ i j, |M i j| ≤ MB) →
      ∀ (t : ℝ), 0 < t → ∀ (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      (∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ r)) → (∀ r ∈ Icc (0 : ℝ) t, ∀ x, 0 ≤ μ r x) →
      ∀ N : ℕ, 1 ≤ N → ∀ σ ∈ Icc (0 : ℝ) t,
        SA16FOp d m p s M (sa16y5_aInt d N t μ σ) (sa16y5f_NInt d m N p s M t μ σ) ∧
        ∀ G : WmpSpace d (m + 1 + 1) p,
          fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(sa16y5f_NInt d m N p s M t μ σ G)) ≤
            cN * jetEnergy d m p (sa16sz_iota2 d m p G) := by
  have hs0 : 0 < s := by
    have : (0 : ℝ) ≤ (d : ℝ) - 1 := by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
                                       linarith
    linarith
  obtain ⟨Wd, hWd0, hdd⟩ := sa16y5_density_data hd m Λ
  obtain ⟨Cg, cN, hCg0, hcN0, hFexM⟩ := hFex Wd hWd0
  refine ⟨cN, hcN0, fun M hMC hM t ht μ hμ hpos N hN σ hσ => ?_⟩
  have hnode : ∀ i ∈ Finset.range (N + 1), t - (i : ℝ) * t / N ∈ Icc (0 : ℝ) t := fun i hi => sa16y4_node_mem hN ht hi
  have hddi : ∀ i ∈ Finset.range (N + 1), _ := fun i hi => hdd _ (hμ _ (hnode i hi))
  have hop : ∀ i ∈ Finset.range (N + 1),
      SA16FOp d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))
        (sa16y5f_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))) ∧
      ‖sa16y5f_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))‖ ≤ Cg ∧
      (∀ G : WmpSpace d (m + 1 + 1) p,
        fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G)
          (-(sa16y5f_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N))) G)) ≤
          cN * jetEnergy d m p (sa16sz_iota2 d m p G)) := by
    intro i hi
    obtain ⟨hSB, hDec, -, -, hnn⟩ := (hddi i hi).2 N
    obtain ⟨T, hTs, hT, hTd⟩ := hFexM hMC hM hSB (hnn (hpos _ (hnode i hi)))
      (sa16y5_Dec_Cb hWd0 hDec)
    rw [sa16y5f_Gop_eq hTs]
    exact ⟨hTs, hT, hTd⟩
  have hw0 : ∀ σ : ℝ, ∀ i ∈ Finset.range (N + 1), 0 ≤ sa16y4_hat N t i σ := fun σ i _ => sa16y4_hat_nonneg N t i σ
  have hw1 : ∀ σ ∈ Icc (0 : ℝ) t, ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ = 1 := fun σ hσ =>
    sa16y4_hat_sum hN ht hσ
  have hNiso : ∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (sa16y5_aInt d N t μ σ) ∧ SA16FOp d m p s M
      (sa16y5_aInt d N t μ σ) (sa16y5f_NInt d m N p s M t μ σ) := by
    intro σ hσ
    exact sa16y5f_fop_sum hd hs0 hsd _ (fun i => sa16y4_hat N t i σ)
      (fun i => sa16q_mol N (μ (t - (i : ℝ) * t / N)))
      (fun i => sa16y5f_Gop d m p s _ (sa16q_mol N (μ (t - (i : ℝ) * t / N)))) (Finset.range (N + 1))
      (fun i hi => ((hddi i hi).2 N).1.1) (fun i hi => (hop i hi).1)
  have hNdiss : ∀ σ ∈ Icc (0 : ℝ) t, ∀ G : WmpSpace d (m + 1 + 1) p,
      fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(sa16y5f_NInt d m N p s M t μ σ G)) ≤
        cN * jetEnergy d m p (sa16sz_iota2 d m p G) := by
    intro σ hσ G
    have e : -(sa16y5f_NInt d m N p s M t μ σ G) = ∑ i ∈ Finset.range (N + 1),
        sa16y4_hat N t i σ • (-(sa16y5f_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N))) G)) := by
      unfold sa16y5f_NInt
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul,
        Finset.smul_sum, smul_neg, Finset.sum_neg_distrib]
    rw [e, map_sum]
    simp only [map_smul, smul_eq_mul]
    calc ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G)
          (-(sa16y5f_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N))) G))
        ≤ ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ *
            (cN * jetEnergy d m p (sa16sz_iota2 d m p G)) :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ((hop i hi).2.2 G) (hw0 σ i hi)
      _ = cN * jetEnergy d m p (sa16sz_iota2 d m p G) := by
          rw [← Finset.sum_mul, hw1 σ hσ, one_mul]
  refine ⟨(hNiso σ hσ).2, fun G => hNdiss σ hσ G⟩

end Gc4

end HRS.Whole.AppendixA.Phase2SA16R
