import HRS.MS.SA16Y5Ap2

/-!
# S.A.16 (SA16Y5) Ap3: the approximate solutions with `N`-uniform level-`m` energy bound (order-one iso nonlocal term)

`sa16y5_approx3`: for a matrix class `MCls` with an abstract dissipativity `hHd` (iso: `M = -lam I`; Hilbert: `M = -lam I + A`), `d-2 < s < d-1`, `d < p(s+1)` there are constants `cE, CN, B, Cg` (independent of `N`, `t`, `μ`, `ν`, `φ`) such that for
every regular nonnegative density family, truncated drifts `b`, `N ≥ 1`, `ν > 0` and datum `φ ∈ W^{m+2,p}` the mild solution `u` of
`K = B_{bc^N} - NInt^N` exists and `‖ι² u(τ)‖ ≤ CN ‖ι² φ‖ e^{cE τ}`; `NInt σ` is the order-one operator of the interpolated density.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q HRS.Whole.AppendixA.Phase2SA16V2

section Ap3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 3200000 in
theorem sa16y5_approx3 (d m : ℕ) (hd : 1 ≤ d) (s p Λ A L MB : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs1 : s < (d : ℝ) - 1) (hθ0 : 0 < s + 2 - d) (hfar : (d : ℝ) < p * (s + 1))
    (hA0 : 0 ≤ A) (hL0 : 0 ≤ L) (MCls : Matrix (Fin d) (Fin d) ℝ → Prop)
    (hHd : ∀ Wd : ℝ, 0 ≤ Wd → ∃ cN : ℝ, 0 ≤ cN ∧ ∀ {M : Matrix (Fin d) (Fin d) ℝ}, MCls M →
      (∀ i j, |M i j| ≤ MB) → ∀ {μ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) →
      sa16z_Cb 2 Wd μ → sa16y5_Dec (m + 2) Wd μ → ∀ (N' : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p),
        SA16IsoOp d (m + 1) p s M μ N' → ∀ G : WmpSpace d (m + 1 + 1) p,
          fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(sa16r_iota d m p (N' G))) ≤
            cN * jetEnergy d m p (sa16sz_iota2 d m p G)) :
    ∃ (cE CN B Cg : ℝ) (B' Bk : ℕ → ℝ), 0 < CN ∧ 0 ≤ B ∧ 0 ≤ Cg ∧
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
          voltOp (gainKer (sa16r_GamT d (m + 1) p ν)
            (sa16y5_Kint d m N p s M t μ b)) u τ) ∧
        (∀ τ ∈ Icc (0 : ℝ) t, ‖sa16sz_iota2 d m p (u τ)‖ ≤ CN * ‖sa16sz_iota2 d m p φ‖ * Real.exp (cE * τ)) ∧
        (∀ σ ∈ Icc (0 : ℝ) t, SA16DerCoef (m + 1) B (sa16y4_bcInt d N t b σ)) ∧
        (∀ σ ∈ Icc (0 : ℝ) t, SA16BddCoef (m + 1) (B' N) (sa16y4_bcInt d N t b σ)) ∧
        (∀ σ ∈ Icc (0 : ℝ) t, sa16y4_Good (sa16y5_aInt d N t μ σ) ∧ SA16IsoOp d (m + 1) p s M
          (sa16y5_aInt d N t μ σ) (sa16y5_NInt d m N p s M t μ σ)) ∧
        (∀ σ ∈ Icc (0 : ℝ) t, ‖sa16y5_Kint d m N p s M t μ b σ‖ ≤ Bk N) ∧
        0 ≤ Bk N ∧
        (∀ x, ContinuousOn (fun σ => sa16y5_Kint d m N p s M t μ b σ x)
          (Icc 0 t)) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  have hsd : s < d := by linarith
  obtain ⟨B, hB0, B', hFam⟩ := sa16y4_trunc_mol_coef d m hA0 hL0
  obtain ⟨Wd, hWd0, hdd⟩ := sa16y5_density_data hd m Λ
  obtain ⟨Cg, hCg0, hGex⟩ := sa16y5_G_smooth d (m + 1) hd s p MB Wd hs0 hs1 hfar hWd0
  obtain ⟨cN, hcN0, hdissM⟩ := hHd Wd hWd0
  obtain ⟨CN, hCN, hnorm⟩ := sa16y3_norm_of_energy (d := d) (p := p) m
  refine ⟨(p * sa16sz_cTr d m p B + cN) / p, CN, B, Cg,
    B', fun N => sa16so_cB d (m + 1) (B' N) + Cg, hCN, hB0, hCg0.le,
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
  have hbcD : ∀ σ ∈ Icc (0 : ℝ) t, SA16DerCoef (m + 1) B (sa16y4_bcInt d N t b σ) := fun σ hσ =>
    sa16y4_derCoef_convex (Finset.range (N + 1)) (fun i => sa16y4_hat N t i σ) (hw0 σ) (hw1 σ hσ)
      (c := fun i j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) fun i hi => (hcoef i hi).1
  have hbcB : ∀ σ ∈ Icc (0 : ℝ) t, SA16BddCoef (m + 1) (B' N) (sa16y4_bcInt d N t b σ) := fun σ hσ =>
    sa16y4_bddCoef_convex (Finset.range (N + 1)) (fun i => sa16y4_hat N t i σ) (hw0 σ) (hw1 σ hσ)
      (c := fun i j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) fun i hi => (hcoef i hi).2
  -- the interpolated operator
  have hNbd : ∀ σ ∈ Icc (0 : ℝ) t, ‖sa16y5_NInt d m N p s M t μ σ‖ ≤ Cg := by
    intro σ hσ
    refine ContinuousLinearMap.opNorm_le_bound _ hCg0.le fun y => ?_
    have h1 : ‖(sa16y5_NInt d m N p s M t μ σ) y‖ ≤ ∑ i ∈ Finset.range (N + 1),
        ‖sa16y4_hat N t i σ • (sa16y5_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))) y‖ := by
      unfold sa16y5_NInt
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      exact norm_sum_le _ _
    refine h1.trans ?_
    calc ∑ i ∈ Finset.range (N + 1), ‖sa16y4_hat N t i σ • (sa16y5_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))) y‖
        ≤ ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * (Cg * ‖y‖) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 σ i hi)]
          exact mul_le_mul_of_nonneg_left (((sa16y5_Gop d m p s M _).le_opNorm y).trans
            (mul_le_mul_of_nonneg_right (hop i hi).2.1 (norm_nonneg _))) (hw0 σ i hi)
      _ = Cg * ‖y‖ := by rw [← Finset.sum_mul, hw1 σ hσ, one_mul]
  have hNiso : ∀ σ ∈ Icc (0 : ℝ) t, sa16y4_Good (sa16y5_aInt d N t μ σ) ∧ SA16IsoOp d (m + 1) p s M
      (sa16y5_aInt d N t μ σ) (sa16y5_NInt d m N p s M t μ σ) := by
    intro σ hσ
    exact sa16y5_isoop_sum hd hs0 hs1 _ (fun i => sa16y4_hat N t i σ)
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
  have hB'0 : 0 ≤ B' N := (hbcB 0 ⟨le_rfl, ht.le⟩).nonneg
  set Bk : ℝ := sa16so_cB d (m + 1) (B' N) + Cg with hBk
  have hBk0 : 0 ≤ Bk := add_nonneg (sa16so_cB_nonneg d (m + 1) hB'0) hCg0.le
  have hKb : ∀ σ ∈ Icc (0 : ℝ) t, ‖sa16y5_Kint d m N p s M t μ b σ‖ ≤ Bk := by
    intro σ hσ
    unfold sa16y5_Kint
    have h1 : ‖sa16so_B d (m + 1) p (sa16y4_bcInt d N t b σ)‖ ≤ sa16so_cB d (m + 1) (B' N) :=
      sa16so_B_norm (p := p) (hbcB σ hσ)
    have h3 := norm_sub_le (sa16so_B d (m + 1) p (sa16y4_bcInt d N t b σ)) (sa16y5_NInt d m N p s M t μ σ)
    rw [hBk]
    linarith [hNbd σ hσ]
  have hKc : ∀ x, ContinuousOn (fun σ => sa16y5_Kint d m N p s M t μ b σ x) (Icc 0 t) := by
    intro x
    have hform : ∀ σ ∈ Icc (0 : ℝ) t, sa16y5_Kint d m N p s M t μ b σ x =
        ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ •
          (sa16so_B d (m + 1) p (fun j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) x -
            sa16y5_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N))) x) := by
      intro σ hσ
      unfold sa16y5_Kint
      have hbc_eq : sa16y4_bcInt d N t b σ = fun j x => ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ *
          sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j) x := rfl
      rw [hbc_eq, sa16y4_B_convex (Finset.range (N + 1)) (fun i => sa16y4_hat N t i σ) (hw0 σ) (hw1 σ hσ)
        (c := fun i j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) fun i hi => (hcoef i hi).2]
      simp only [sub_apply, sa16y5_NInt, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_sub, Finset.sum_sub_distrib]
    refine ContinuousOn.congr (f := fun σ => ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ •
        (sa16so_B d (m + 1) p (fun j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) x -
          sa16y5_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N))) x)) ?_ hform
    exact (continuous_finsetSum _ fun i _ => (sa16y4_hat_continuous N t i).smul continuous_const).continuousOn
  obtain ⟨u, hu, hsol, hen⟩ := sa16y5_mild_energy (p := p) (m := m) (ν := ν) (T := t) (B := B) (B' := B' N)
    (Bk := Bk) (cNl := cN) hν ht (sa16y4_bcInt d N t b) (fun σ hσ => hbcD σ hσ) (fun σ hσ => hbcB σ hσ)
    (sa16y5_NInt d m N p s M t μ) hNdiss (sa16y5_Kint d m N p s M t μ b) (fun σ => rfl) hKb hBk0 hKc φ
  refine ⟨u, hu, hsol, fun τ hτ => ?_, hbcD, hbcB, hNiso, hKb, hBk0, hKc⟩
  have := hnorm (sa16sz_iota2 d m p (u τ)) (sa16sz_iota2 d m p φ)
    ((p * sa16sz_cTr d m p B + cN) * τ) (hen τ hτ)
  refine this.trans (le_of_eq ?_)
  congr 2
  field_simp

end Ap3

end HRS.Whole.AppendixA.Phase2SA16R
