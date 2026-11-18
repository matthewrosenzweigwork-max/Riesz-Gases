import HRS.MS.SA16Y4Ap1
import HRS.MS.SA16Y4Ip2
import HRS.MS.SA16Y4Ip3

/-!
# S.A.16 (SA16Y4) Ap2: approximate solutions with time-interpolated coefficients (no continuity hypothesis)

The coefficients of the `N`-th approximation are the piecewise-linear interpolants in `σ` (nodes `σ_i = i t/N`, weights
`hat_i`) of the mollified truncated drift `χ_{N+1}(ρ_N ⋆ b_{t-σ_i})` and of the nonlocal operators `G[ρ_N ⋆ μ_{t-σ_i}]`.
Then `K_σ = ∑ hat_i(σ) K^{(i)}` on `[0,t]` is a finite combination of fixed bounded operators, so `hKc` holds for free
(`sa16y4_approx2` has no continuity hypothesis), while all constants (`B`, `CG`, `CN`, `cE`) stay independent of `N`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Ap2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- interpolated truncated mollified coefficients -/
def sa16y4_bcInt (d N : ℕ) (t : ℝ)
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (σ : ℝ) :
    Fin d → EuclideanSpace ℝ (Fin d) → ℝ :=
  fun j x => ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ *
    sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j) x

/-- interpolated nonlocal operator at level `ℓ` -/
def sa16y4_GInt (d ℓ N : ℕ) (p : ℝ) [Fact (2 ≤ p)] (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (σ : ℝ) : WmpSpace d ℓ p →L[ℝ] WmpSpace d ℓ p :=
  ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ • sa16so_G d ℓ p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))

/-- the interpolated Duhamel family -/
def sa16y4_Kint (d m N : ℕ) (p : ℝ) [Fact (2 ≤ p)] (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (σ : ℝ) : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p :=
  sa16so_B d (m + 1) p (sa16y4_bcInt d N t b σ) -
    (sa16y4_GInt d (m + 1) N p s M t μ σ).comp (sa16r_iota d (m + 1) p)

lemma sa16y4_node_mem {N : ℕ} {t : ℝ} (hN : 1 ≤ N) (ht : 0 < t) {i : ℕ} (hi : i ∈ Finset.range (N + 1)) :
    t - (i : ℝ) * t / N ∈ Icc (0 : ℝ) t := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hi' : (i : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have h1 : (i : ℝ) * t / N ≤ t := by
    rw [div_le_iff₀ hN0]; nlinarith
  have h2 : 0 ≤ (i : ℝ) * t / N := by positivity
  exact ⟨by linarith, by linarith⟩

set_option maxHeartbeats 3200000 in
theorem sa16y4_approx2 (d m : ℕ) (hd : 1 ≤ d) (s p MB Λ A L : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs2 : s ≤ (d : ℝ) - 2) (hfar : (d : ℝ) < p * (s + 1)) (hA0 : 0 ≤ A) (hL0 : 0 ≤ L) :
    ∃ (cE CN B CG : ℝ) (B' Bk : ℕ → ℝ), 0 < CN ∧ 0 ≤ B ∧ 0 ≤ CG ∧
      ∀ (t : ℝ) (ht : 0 < t) (M : Matrix (Fin d) (Fin d) ℝ) (hM : ∀ i j, |M i j| ≤ MB)
        (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ r))
        (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (hb : ∀ r ∈ Icc (0 : ℝ) t, ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) (b r) ∧ ‖b r 0‖ ≤ A ∧
          ∀ j, 1 ≤ j → j ≤ m + 2 → ∀ x, ‖iteratedFDeriv ℝ j (b r) x‖ ≤ L),
      ∀ (N : ℕ), 1 ≤ N → ∀ (ν : ℝ), 0 < ν → ∀ (φ : WmpSpace d (m + 1 + 1) p),
      ∃ u : ℝ → WmpSpace d (m + 1 + 1) p, ContinuousOn u (Icc 0 t) ∧
        (∀ τ ∈ Icc (0 : ℝ) t, u τ = sa16r_f0 d (m + 1) p ν φ τ +
          voltOp (gainKer (sa16r_GamT d (m + 1) p ν) (sa16y4_Kint d m N p s M t μ b)) u τ) ∧
        (∀ τ ∈ Icc (0 : ℝ) t, ‖sa16sz_iota2 d m p (u τ)‖ ≤ CN * ‖sa16sz_iota2 d m p φ‖ * Real.exp (cE * τ)) ∧
        (∀ σ ∈ Icc (0 : ℝ) t, SA16DerCoef (m + 1) B (sa16y4_bcInt d N t b σ)) ∧
        (∀ σ ∈ Icc (0 : ℝ) t, SA16BddCoef (m + 1) (B' N) (sa16y4_bcInt d N t b σ)) ∧
        (∀ σ ∈ Icc (0 : ℝ) t, ‖sa16y4_GInt d m N p s M t μ σ‖ ≤ CG) ∧
        (∀ σ ∈ Icc (0 : ℝ) t, (sa16r_iota d m p).comp (sa16y4_GInt d (m + 1) N p s M t μ σ) =
          (sa16y4_GInt d m N p s M t μ σ).comp (sa16r_iota d m p)) ∧
        (∀ σ ∈ Icc (0 : ℝ) t, ‖sa16y4_Kint d m N p s M t μ b σ‖ ≤ Bk N) ∧ 0 ≤ Bk N ∧
        (∀ x, ContinuousOn (fun σ => sa16y4_Kint d m N p s M t μ b σ x) (Icc 0 t)) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  obtain ⟨B, hB0, B', hFam⟩ := sa16y4_trunc_mol_coef d m hA0 hL0
  obtain ⟨CG, CG1, hCG, hCG1, hnl⟩ := sa16y4_nl_pair d m hd s p MB Λ hs0 hs2 hfar
  obtain ⟨CN, hCN, hnorm⟩ := sa16y3_norm_of_energy (d := d) (p := p) m
  refine ⟨(p * sa16sz_cTr d m p B + p * sa16y3_CJ d m p * CG) / p, CN, B, CG,
    B', fun N => sa16so_cB d (m + 1) (B' N) + CG1 * ‖sa16r_iota d (m + 1) p‖, hCN, hB0, hCG.le,
    fun t ht M hM μ hμ b hb N hN ν hν φ => ?_⟩
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
  have hnlr : ∀ i ∈ Finset.range (N + 1),
      ‖sa16so_G d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))‖ ≤ CG ∧
      ‖sa16so_G d (m + 1) p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))‖ ≤ CG1 ∧
        (sa16r_iota d m p).comp (sa16so_G d (m + 1) p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))) =
          (sa16so_G d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))).comp (sa16r_iota d m p) := by
    intro i hi
    obtain ⟨T1, T0, h0, h1, hc, hs0', hs1'⟩ := hnl M hM _ (hμ _ (sa16y4_node_mem hN ht hi)) N
    rw [sa16so_G_eq hs0', sa16so_G_eq hs1']
    exact ⟨h0, h1, hc⟩
  have hw0 : ∀ σ : ℝ, ∀ i ∈ Finset.range (N + 1), 0 ≤ sa16y4_hat N t i σ := fun σ i _ => sa16y4_hat_nonneg N t i σ
  have hw1 : ∀ σ ∈ Icc (0 : ℝ) t, ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ = 1 := fun σ hσ =>
    sa16y4_hat_sum hN ht hσ
  have hbcD : ∀ σ ∈ Icc (0 : ℝ) t, SA16DerCoef (m + 1) B (sa16y4_bcInt d N t b σ) := fun σ hσ =>
    sa16y4_derCoef_convex (Finset.range (N + 1)) (fun i => sa16y4_hat N t i σ) (hw0 σ) (hw1 σ hσ)
      (c := fun i j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) fun i hi => (hcoef i hi).1
  have hbcB : ∀ σ ∈ Icc (0 : ℝ) t, SA16BddCoef (m + 1) (B' N) (sa16y4_bcInt d N t b σ) := fun σ hσ =>
    sa16y4_bddCoef_convex (Finset.range (N + 1)) (fun i => sa16y4_hat N t i σ) (hw0 σ) (hw1 σ hσ)
      (c := fun i j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) fun i hi => (hcoef i hi).2
  -- operator data
  have hTbound : ∀ (ℓ : ℕ) (C : ℝ) (hC : 0 ≤ C), (∀ i ∈ Finset.range (N + 1),
      ‖sa16so_G d ℓ p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))‖ ≤ C) → ∀ σ ∈ Icc (0 : ℝ) t,
      ‖sa16y4_GInt d ℓ N p s M t μ σ‖ ≤ C := by
    intro ℓ C hC hG σ hσ
    refine ContinuousLinearMap.opNorm_le_bound _ hC fun y => ?_
    have h1 : ‖(sa16y4_GInt d ℓ N p s M t μ σ) y‖ ≤ ∑ i ∈ Finset.range (N + 1),
        ‖sa16y4_hat N t i σ • (sa16so_G d ℓ p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))) y‖ := by
      unfold sa16y4_GInt
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      exact norm_sum_le _ _
    refine h1.trans ?_
    calc ∑ i ∈ Finset.range (N + 1), ‖sa16y4_hat N t i σ • (sa16so_G d ℓ p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))) y‖
        ≤ ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * (C * ‖y‖) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 σ i hi)]
          exact mul_le_mul_of_nonneg_left (((sa16so_G d ℓ p s M _).le_opNorm y).trans
            (mul_le_mul_of_nonneg_right (hG i hi) (norm_nonneg _))) (hw0 σ i hi)
      _ = C * ‖y‖ := by rw [← Finset.sum_mul, hw1 σ hσ, one_mul]
  have hT0n : ∀ σ ∈ Icc (0 : ℝ) t, ‖sa16y4_GInt d m N p s M t μ σ‖ ≤ CG :=
    hTbound m CG hCG.le (fun i hi => (hnlr i hi).1)
  have hT1n : ∀ σ ∈ Icc (0 : ℝ) t, ‖sa16y4_GInt d (m + 1) N p s M t μ σ‖ ≤ CG1 :=
    hTbound (m + 1) CG1 hCG1.le (fun i hi => (hnlr i hi).2.1)
  have hcompn : ∀ σ ∈ Icc (0 : ℝ) t, (sa16r_iota d m p).comp (sa16y4_GInt d (m + 1) N p s M t μ σ) =
      (sa16y4_GInt d m N p s M t μ σ).comp (sa16r_iota d m p) := by
    intro σ hσ
    ext1 y
    simp only [ContinuousLinearMap.comp_apply, sa16y4_GInt, ContinuousLinearMap.sum_apply, map_sum, map_smul,
      ContinuousLinearMap.smul_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := congrArg (fun L => L y) (hnlr i hi).2.2
    simp only [ContinuousLinearMap.comp_apply] at this
    rw [this]
  have hB'0 : 0 ≤ B' N := (hbcB 0 ⟨le_rfl, ht.le⟩).nonneg
  set Bk : ℝ := sa16so_cB d (m + 1) (B' N) + CG1 * ‖sa16r_iota d (m + 1) p‖ with hBk
  have hBk0 : 0 ≤ Bk := add_nonneg (sa16so_cB_nonneg d (m + 1) hB'0)
    (mul_nonneg hCG1.le (ContinuousLinearMap.opNorm_nonneg _))
  have hKb : ∀ σ ∈ Icc (0 : ℝ) t, ‖sa16y4_Kint d m N p s M t μ b σ‖ ≤ Bk := by
    intro σ hσ
    unfold sa16y4_Kint
    set X := sa16so_B d (m + 1) p (sa16y4_bcInt d N t b σ) with hX
    set Y := (sa16y4_GInt d (m + 1) N p s M t μ σ).comp (sa16r_iota d (m + 1) p) with hY
    have h1 : ‖X‖ ≤ sa16so_cB d (m + 1) (B' N) := sa16so_B_norm (p := p) (hbcB σ hσ)
    have h2 : ‖Y‖ ≤ CG1 * ‖sa16r_iota d (m + 1) p‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hT1n σ hσ) (ContinuousLinearMap.opNorm_nonneg _))
    have h3 : ‖X - Y‖ ≤ ‖X‖ + ‖Y‖ := norm_sub_le X Y
    rw [hBk]
    linarith
  have hKc : ∀ x, ContinuousOn (fun σ => sa16y4_Kint d m N p s M t μ b σ x) (Icc 0 t) := by
    intro x
    have hform : ∀ σ ∈ Icc (0 : ℝ) t, sa16y4_Kint d m N p s M t μ b σ x =
        ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ •
          (sa16so_B d (m + 1) p (fun j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) x -
            sa16so_G d (m + 1) p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N))) (sa16r_iota d (m + 1) p x)) := by
      intro σ hσ
      unfold sa16y4_Kint
      have hbc_eq : sa16y4_bcInt d N t b σ = fun j x => ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ *
          sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j) x := rfl
      rw [hbc_eq, sa16y4_B_convex (Finset.range (N + 1)) (fun i => sa16y4_hat N t i σ) (hw0 σ) (hw1 σ hσ)
        (c := fun i j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) fun i hi => (hcoef i hi).2]
      simp only [sub_apply, ContinuousLinearMap.comp_apply, sa16y4_GInt, ContinuousLinearMap.sum_apply, map_sum,
        ContinuousLinearMap.smul_apply, smul_sub, Finset.sum_sub_distrib]
    refine ContinuousOn.congr (f := fun σ => ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ •
        (sa16so_B d (m + 1) p (fun j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) x -
          sa16so_G d (m + 1) p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N))) (sa16r_iota d (m + 1) p x))) ?_ hform
    exact (continuous_finsetSum _ fun i _ => (sa16y4_hat_continuous N t i).smul continuous_const).continuousOn
  obtain ⟨u, hu, hsol, hen⟩ := sa16y3_mild_energy (p := p) (m := m) (ν := ν) (T := t) (B := B) (B' := B' N)
    (Bk := Bk) (CG := CG) hν ht (sa16y4_bcInt d N t b) (fun σ hσ => hbcD σ hσ) (fun σ hσ => hbcB σ hσ)
    (sa16y4_GInt d (m + 1) N p s M t μ) (sa16y4_GInt d m N p s M t μ) hcompn hT0n
    (sa16y4_Kint d m N p s M t μ b) (fun σ => rfl) hKb hBk0 hKc φ
  refine ⟨u, hu, hsol, fun τ hτ => ?_, hbcD, hbcB, hT0n, hcompn, hKb, hBk0, hKc⟩
  have := hnorm (sa16sz_iota2 d m p (u τ)) (sa16sz_iota2 d m p φ)
    ((p * sa16sz_cTr d m p B + p * sa16y3_CJ d m p * CG) * τ) (hen τ hτ)
  refine this.trans (le_of_eq ?_)
  congr 2
  field_simp

end Ap2

end HRS.Whole.AppendixA.Phase2SA16R
