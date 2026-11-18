import HRS.MS.SA16Y5Ap2f
import HRS.MS.SA16Y5Dn1
import HRS.MS.SA16Y5Ap3

/-!
# S.A.16 (SA16Y5) Ap3f: approximate solutions with `N`-uniform level-`m` energy bound, fractional order `d-1 < s < d` (B9)

Fractional analogue of `sa16y5_approx3`: the nonlocal operator at each node is an abstract `N : W^{m+2} → W^m` (`hFex`: existence with `SA16FOp`, norm and dissipativity),
interpolated linearly in time (`sa16y5f_NInt`); the Volterra equation is solved by `sa16y5f_mild` (heat-composed kernel `‖Qh (νs) N‖ ≤ C s^{-γ}`, `γ = (s+2-d)/2`) and the energy by `sa16y5f_energy`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q HRS.Whole.AppendixA.Phase2SA16V2

section Ap3f
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 6400000 in
theorem sa16y5f_approx3 (d m : ℕ) (hd : 1 ≤ d) (s p Λ A L MB : ℝ) [Fact (2 ≤ p)]
    (hs1 : (d : ℝ) - 1 < s) (hsd : s < d) (hA0 : 0 ≤ A) (hL0 : 0 ≤ L) (hMB : 0 ≤ MB)
    (MCls : Matrix (Fin d) (Fin d) ℝ → Prop)
    (hFex : ∀ Wd : ℝ, 0 ≤ Wd → ∃ Cg cN : ℝ, 0 ≤ Cg ∧ 0 ≤ cN ∧ ∀ {M : Matrix (Fin d) (Fin d) ℝ}, MCls M →
      (∀ i j, |M i j| ≤ MB) → ∀ {μ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) →
      sa16z_Cb (m + 3) Wd μ → ∃ N : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p,
        SA16FOp d m p s M μ N ∧ ‖N‖ ≤ Cg ∧ ∀ G : WmpSpace d (m + 1 + 1) p,
          fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(N G)) ≤
            cN * jetEnergy d m p (sa16sz_iota2 d m p G)) :
    ∃ (cE CN B Cg : ℝ) (B' : ℕ → ℝ), 0 < CN ∧ 0 ≤ B ∧ 0 ≤ Cg ∧
      ∀ (M : Matrix (Fin d) (Fin d) ℝ), MCls M → (∀ i j, |M i j| ≤ MB) →
      ∀ (t : ℝ) (ht : 0 < t)
        (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ r))
        (hpos : ∀ r ∈ Icc (0 : ℝ) t, ∀ x, 0 ≤ μ r x)
        (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (hb : ∀ r ∈ Icc (0 : ℝ) t, ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) (b r) ∧ ‖b r 0‖ ≤ A ∧
          ∀ j, 1 ≤ j → j ≤ m + 2 → ∀ x, ‖iteratedFDeriv ℝ j (b r) x‖ ≤ L),
      ∀ (N : ℕ), 1 ≤ N → ∀ (ν : ℝ), 0 < ν → ∀ (φ : WmpSpace d (m + 1 + 1) p),
      ∃ u : ℝ → WmpSpace d (m + 1 + 1) p, ContinuousOn u (Icc 0 t) ∧
        (∀ τ ∈ Icc (0 : ℝ) t, u τ = sa16r_f0 d (m + 1) p ν φ τ +
          voltOp (fun τ σ => sa16y5f_kernel d m p ν (fun r => sa16so_B d (m + 1) p (sa16y4_bcInt d N t b r))
            (sa16y5f_NInt d m N p s M t μ) σ (τ - σ)) u τ) ∧
        (∀ τ ∈ Icc (0 : ℝ) t, ‖sa16sz_iota2 d m p (u τ)‖ ≤ CN * ‖sa16sz_iota2 d m p φ‖ * Real.exp (cE * τ)) ∧
        (∀ σ ∈ Icc (0 : ℝ) t, SA16DerCoef (m + 1) B (sa16y4_bcInt d N t b σ)) ∧
        (∀ σ ∈ Icc (0 : ℝ) t, SA16BddCoef (m + 1) (B' N) (sa16y4_bcInt d N t b σ)) ∧
        (∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (sa16y5_aInt d N t μ σ) ∧ SA16FOp d m p s M
          (sa16y5_aInt d N t μ σ) (sa16y5f_NInt d m N p s M t μ σ)) ∧
        (∀ σ ∈ Icc (0 : ℝ) t, ‖sa16y5f_NInt d m N p s M t μ σ‖ ≤ Cg) ∧
        (∀ x, ContinuousOn (fun σ => sa16so_B d (m + 1) p (sa16y4_bcInt d N t b σ) x) (Icc 0 t)) ∧
        (∀ x, ContinuousOn (fun σ => sa16y5f_NInt d m N p s M t μ σ x) (Icc 0 t)) ∧
        (∃ CNs : ℝ, ∀ σ ∈ Icc (0 : ℝ) t, ∀ s' ∈ Ioc (0 : ℝ) t,
          ‖sa16y5_Qh d m p (ν * s') (sa16y5f_NInt d m N p s M t μ σ)‖ ≤ CNs * s' ^ (-((s + 2 - d) / 2))) ∧
        (∀ σ ∈ Icc (0 : ℝ) t, ∀ a : ℝ, 0 < a → ∀ x : WmpSpace d (m + 1 + 1) p,
          sa16r_iota d (m + 1) p (sa16y5_Qh d m p a (sa16y5f_NInt d m N p s M t μ σ) x) =
            sa16r_Gam d m p a (sa16y5f_NInt d m N p s M t μ σ x)) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  have hs0 : 0 < s := by
    have : (0 : ℝ) ≤ (d : ℝ) - 1 := by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
                                       linarith
    linarith
  have hsd1 : (d : ℝ) < s + 1 := by linarith
  obtain ⟨B, hB0, B', hFam⟩ := sa16y4_trunc_mol_coef d m hA0 hL0
  obtain ⟨Wd, hWd0, hdd⟩ := sa16y5_density_data hd m Λ
  obtain ⟨Cg, cN, hCg0, hcN0, hFexM⟩ := hFex Wd hWd0
  obtain ⟨Cq, hCq0, hCq⟩ := sa16y5_Qh_bound (p := p) hd hs0 hsd hsd1 m MB Wd hMB hWd0
  obtain ⟨CN, hCN, hnorm⟩ := sa16y3_norm_of_energy (d := d) (p := p) m
  set γ : ℝ := (s + 2 - d) / 2 with hγ
  have hγ1 : 1 / 2 ≤ γ := by rw [hγ]; linarith
  have hγ2 : γ < 1 := by rw [hγ]; linarith
  refine ⟨(p * sa16sz_cTr d m p B + cN) / p, CN, B, Cg, B', hCN, hB0, hCg0,
    fun M hMC hM t ht μ hμ hpos b hb N hN ν hν φ => ?_⟩
  -- node data
  have hcoef : ∀ i ∈ Finset.range (N + 1),
      SA16DerCoef (m + 1) B (fun j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) ∧
        SA16BddCoef (m + 1) (B' N) (fun j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) := by
    intro i hi
    obtain ⟨hbs, hb0, hbL⟩ := hb _ (sa16y4_node_mem hN ht hi)
    have hbs1 : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (b (t - (i : ℝ) * t / N)) :=
      hbs.of_le (by exact_mod_cast Nat.le_succ _)
    have hcomp := fun j => sa16y4_comp_bounds (k := m + 1) (by omega) hbs1 hb0
      (fun k hk1 hkk x => hbL k hk1 (by omega) x) j
    exact hFam N _ (fun j => (hcomp j).1) (fun j y => (hcomp j).2.1 y) (fun j k hk1 hkk x => (hcomp j).2.2 k hk1 hkk x)
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
  have hbcD : ∀ σ ∈ Icc (0 : ℝ) t, SA16DerCoef (m + 1) B (sa16y4_bcInt d N t b σ) := fun σ hσ =>
    sa16y4_derCoef_convex (Finset.range (N + 1)) (fun i => sa16y4_hat N t i σ) (hw0 σ) (hw1 σ hσ)
      (c := fun i j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) fun i hi => (hcoef i hi).1
  have hbcB : ∀ σ ∈ Icc (0 : ℝ) t, SA16BddCoef (m + 1) (B' N) (sa16y4_bcInt d N t b σ) := fun σ hσ =>
    sa16y4_bddCoef_convex (Finset.range (N + 1)) (fun i => sa16y4_hat N t i σ) (hw0 σ) (hw1 σ hσ)
      (c := fun i j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) fun i hi => (hcoef i hi).2
  -- the interpolated operator
  have hNbd : ∀ σ ∈ Icc (0 : ℝ) t, ‖sa16y5f_NInt d m N p s M t μ σ‖ ≤ Cg := by
    intro σ hσ
    refine ContinuousLinearMap.opNorm_le_bound _ hCg0 fun y => ?_
    have h1 : ‖(sa16y5f_NInt d m N p s M t μ σ) y‖ ≤ ∑ i ∈ Finset.range (N + 1),
        ‖sa16y4_hat N t i σ • (sa16y5f_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))) y‖ := by
      unfold sa16y5f_NInt
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      exact norm_sum_le _ _
    refine h1.trans ?_
    calc ∑ i ∈ Finset.range (N + 1), ‖sa16y4_hat N t i σ • (sa16y5f_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))) y‖
        ≤ ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * (Cg * ‖y‖) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 σ i hi)]
          exact mul_le_mul_of_nonneg_left (((sa16y5f_Gop d m p s M _).le_opNorm y).trans
            (mul_le_mul_of_nonneg_right (hop i hi).2.1 (norm_nonneg _))) (hw0 σ i hi)
      _ = Cg * ‖y‖ := by rw [← Finset.sum_mul, hw1 σ hσ, one_mul]
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
  have hB'0 : 0 ≤ B' N := (hbcB 0 ⟨le_rfl, ht.le⟩).nonneg
  have hBb : ∀ σ ∈ Icc (0 : ℝ) t, ‖sa16so_B d (m + 1) p (sa16y4_bcInt d N t b σ)‖ ≤ sa16so_cB d (m + 1) (B' N) :=
    fun σ hσ => sa16so_B_norm (p := p) (hbcB σ hσ)
  have hBc : ∀ x, ContinuousOn (fun σ => sa16so_B d (m + 1) p (sa16y4_bcInt d N t b σ) x) (Icc 0 t) := by
    intro x
    have hform : ∀ σ ∈ Icc (0 : ℝ) t, sa16so_B d (m + 1) p (sa16y4_bcInt d N t b σ) x =
        ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ •
          sa16so_B d (m + 1) p (fun j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) x := by
      intro σ hσ
      have hbc_eq : sa16y4_bcInt d N t b σ = fun j x => ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ *
          sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j) x := rfl
      rw [hbc_eq, sa16y4_B_convex (Finset.range (N + 1)) (fun i => sa16y4_hat N t i σ) (hw0 σ) (hw1 σ hσ)
        (c := fun i j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) fun i hi => (hcoef i hi).2]
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    refine ContinuousOn.congr (f := fun σ => ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ •
        sa16so_B d (m + 1) p (fun j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) x) ?_ hform
    exact (continuous_finsetSum _ fun i _ => (sa16y4_hat_continuous N t i).smul continuous_const).continuousOn
  have hNc : ∀ x, ContinuousOn (fun σ => sa16y5f_NInt d m N p s M t μ σ x) (Icc 0 t) := by
    intro x
    have hform : ∀ σ, sa16y5f_NInt d m N p s M t μ σ x = ∑ i ∈ Finset.range (N + 1),
        sa16y4_hat N t i σ • sa16y5f_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N))) x := by
      intro σ
      unfold sa16y5f_NInt
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    simp_rw [hform]
    exact (continuous_finsetSum _ fun i _ => (sa16y4_hat_continuous N t i).smul continuous_const).continuousOn
  -- the sharp heat-composed bound
  set A0 : ℝ := max 1 (ν * t) with hA0def
  have hA01 : 1 ≤ A0 := le_max_left _ _
  set Cq' : ℝ := max Cq ((sa16r_cG d (1 / 2)) ^ 2 * Cg * A0 ^ γ) with hCq'
  have hCq'0 : 0 ≤ Cq' := (hCq0).trans (le_max_left _ _)
  have hnodeQ : ∀ i ∈ Finset.range (N + 1), ∀ a : ℝ, 0 < a → a ≤ A0 →
      ‖sa16y5_Qh d m p a (sa16y5f_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N))))‖ ≤ Cq' * a ^ (-γ) := by
    intro i hi a ha haA
    obtain ⟨hSB, hDec, -, -, hnn⟩ := (hddi i hi).2 N
    refine sa16y5_Qh_all (p := p) (γ := γ) (C := Cq) (Cg := Cg) (A0 := A0) (by linarith) hA01 hCq0 hCg0 _
      (hop i hi).2.1 (fun a ha ha1 => ?_) a ha haA
    exact hCq M hM hSB.1 (fun κ hκ y => sa16y5_Dec_Cb hWd0 hDec κ hκ y) _ (hop i hi).1 ha ha1
  have hsharp : ∀ σ ∈ Icc (0 : ℝ) t, ∀ s' ∈ Ioc (0 : ℝ) t,
      ‖sa16y5_Qh d m p (ν * s') (sa16y5f_NInt d m N p s M t μ σ)‖ ≤ (Cq' * ν ^ (-γ)) * s' ^ (-γ) := by
    intro σ hσ s' hs'
    have ha : 0 < ν * s' := mul_pos hν hs'.1
    have haA : ν * s' ≤ A0 := (mul_le_mul_of_nonneg_left hs'.2 hν.le).trans (le_max_right _ _)
    unfold sa16y5f_NInt
    rw [sa16y5_Qh_lin]
    have hbd0 : 0 ≤ (Cq' * ν ^ (-γ)) * s' ^ (-γ) :=
      mul_nonneg (mul_nonneg hCq'0 (Real.rpow_nonneg hν.le _)) (Real.rpow_nonneg hs'.1.le _)
    refine ContinuousLinearMap.opNorm_le_bound _ hbd0 fun y => ?_
    have h1 : ‖(∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ • sa16y5_Qh d m p (ν * s')
        (sa16y5f_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N))))) y‖ ≤ ∑ i ∈ Finset.range (N + 1),
        ‖sa16y4_hat N t i σ • (sa16y5_Qh d m p (ν * s')
          (sa16y5f_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N))))) y‖ := by
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      exact norm_sum_le _ _
    refine h1.trans ?_
    calc ∑ i ∈ Finset.range (N + 1), ‖sa16y4_hat N t i σ • (sa16y5_Qh d m p (ν * s')
          (sa16y5f_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N))))) y‖
        ≤ ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * ((Cq' * ν ^ (-γ)) * s' ^ (-γ) * ‖y‖) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 σ i hi)]
          refine mul_le_mul_of_nonneg_left ?_ (hw0 σ i hi)
          refine ((sa16y5_Qh d m p (ν * s') _).le_opNorm y).trans ?_
          have := hnodeQ i hi _ ha haA
          rw [Real.mul_rpow hν.le hs'.1.le] at this
          calc _ ≤ (Cq' * ((ν) ^ (-γ) * s' ^ (-γ))) * ‖y‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
            _ = _ := by ring
      _ = (Cq' * ν ^ (-γ)) * s' ^ (-γ) * ‖y‖ := by rw [← Finset.sum_mul, hw1 σ hσ, one_mul]
  have hiota : ∀ σ ∈ Icc (0 : ℝ) t, ∀ a : ℝ, 0 < a → ∀ x : WmpSpace d (m + 1 + 1) p,
      sa16r_iota d (m + 1) p (sa16y5_Qh d m p a (sa16y5f_NInt d m N p s M t μ σ) x) =
        sa16r_Gam d m p a (sa16y5f_NInt d m N p s M t μ σ x) := fun σ hσ a ha x =>
    sa16y5_Qh_iota hd hs0 hsd hsd1 m ha M (hNiso σ hσ).1 _ (hNiso σ hσ).2 x
  obtain ⟨u, hu, hsol, -⟩ := sa16y5f_mild (p := p) (m := m) (ν := ν) (T := t) (BB := sa16so_cB d (m + 1) (B' N))
    (CN := Cq' * ν ^ (-γ)) (γ := γ) hν ht hγ1 hγ2
    (fun σ => sa16so_B d (m + 1) p (sa16y4_bcInt d N t b σ)) hBb hBc
    (sa16y5f_NInt d m N p s M t μ) hNc hsharp φ
  have hen := sa16y5f_energy (p := p) (m := m) (ν := ν) (T := t) (B := B) (B' := B' N)
    (BB := sa16so_cB d (m + 1) (B' N)) (BN := Cg) (CN := Cq' * ν ^ (-γ)) (cNl := cN) (γ := γ) hν ht hγ1 hγ2
    (sa16y4_bcInt d N t b) hbcD hbcB (fun σ => sa16so_B d (m + 1) p (sa16y4_bcInt d N t b σ)) (fun σ => rfl)
    hBb hBc (sa16y5f_NInt d m N p s M t μ) hNbd hNc hsharp hiota hNdiss φ hu hsol
  refine ⟨u, hu, hsol, fun τ hτ => ?_, hbcD, hbcB, hNiso, hNbd, hBc, hNc, ⟨Cq' * ν ^ (-γ), hsharp⟩, hiota⟩
  have := hnorm (sa16sz_iota2 d m p (u τ)) (sa16sz_iota2 d m p φ)
    ((p * sa16sz_cTr d m p B + cN) * τ) (hen τ hτ)
  refine this.trans (le_of_eq ?_)
  congr 2
  field_simp

end Ap3f

end HRS.Whole.AppendixA.Phase2SA16R
