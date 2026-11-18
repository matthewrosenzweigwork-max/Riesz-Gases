import HRS.MS.SA16Y9Wi3

/-!
# S.A.16 (SA16Y9) Fm4: the approximation family `A0 : SA16ApproxF` of a fractional-regime datum, exposed

`sa16y9_frac_fam`: the first half of `sa16y5f_limit` (SA16Y5Fin5f) with the data lift `Φ` an input.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Fm4
variable {d : ℕ}

/-- the existence hypothesis `hFex` of `sa16y5f_approx3` as a predicate -/
def Sa16FracEx (d : ℕ) (s : ℝ) (p : ℝ) [Fact (2 ≤ p)] (MB : ℝ) (MCls : Matrix (Fin d) (Fin d) ℝ → Prop) (m : ℕ) : Prop :=
  ∀ Wd : ℝ, 0 ≤ Wd → ∃ Cg cN : ℝ, 0 ≤ Cg ∧ 0 ≤ cN ∧ ∀ {M : Matrix (Fin d) (Fin d) ℝ}, MCls M →
      (∀ i j, |M i j| ≤ MB) → ∀ {μ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) →
      sa16z_Cb (m + 3) Wd μ → ∃ N : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p,
        SA16FOp d m p s M μ N ∧ ‖N‖ ≤ Cg ∧ ∀ G : WmpSpace d (m + 1 + 1) p,
          fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(N G)) ≤
            cN * jetEnergy d m p (sa16sz_iota2 d m p G)

set_option maxHeartbeats 6400000 in
theorem sa16y9_frac_fam (hd : 1 ≤ d) (s : ℝ) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s)
    (m : ℕ) (hm : 1 ≤ m) (p : ℝ) [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (hMB : 0 ≤ MB)
    (MCls : Matrix (Fin d) (Fin d) ℝ → Prop) (hFex : Sa16FracEx d s p MB MCls m) :
    ∃ cE CN B : ℝ, 0 < CN ∧ 0 ≤ B ∧
      ∀ (D : WholeDyn d) (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → MCls D.M → ∀ t ∈ Ioc (0 : ℝ) T, ∀ Cφ : ℝ, 0 ≤ Cφ →
      ∀ Φ : ℕ → WmpSpace d (m + 1 + 1) p, (∀ n, ‖sa16sz_iota2 d m p (Φ n)‖ ≤ Cφ) →
      ∃ A0 : SA16ApproxF d m p t (CN * Cφ * Real.exp (|cE| * t)) ((s + 2 - d) / 2),
        (∀ n, A0.φ n = Φ n) ∧ (∀ n, A0.ν n = D.invβ + 1 / ((n : ℝ) + 1)) ∧
        (∀ n, A0.bc n = sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D (μ r))) ∧
        (∀ n, A0.N n = sa16y5f_NInt d m (n + 1) p s D.M t μ) ∧
        (∀ n, ∀ r ∈ Icc (0 : ℝ) t, ‖sa16sz_iota2 d m p (A0.u n r)‖ ≤
          CN * ‖sa16sz_iota2 d m p (Φ n)‖ * Real.exp (cE * r)) ∧
        (∀ n, ∀ σ ∈ Icc (0 : ℝ) t, SA16DerCoef (m + 1) B (A0.bc n σ)) ∧
        (∀ n, ∀ σ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (sa16y5_aInt d (n + 1) t μ σ) ∧
          SA16FOp d m p s D.M (sa16y5_aInt d (n + 1) t μ σ) (sa16y5f_NInt d m (n + 1) p s D.M t μ σ)) ∧
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ n, ∀ r ∈ Icc (0 : ℝ) t,
          ∀ y, |sa16r_ell d m p hψ (A0.N n r y)| ≤ Cn * ‖sa16sz_iota2 d m p y‖) ∧
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ cN R0 : ℝ, 0 ≤ cN ∧
          ∀ n, ∀ r ∈ Icc (0 : ℝ) t, ∀ x, |sa16so_divFun (A0.bc n r) ψ x| ≤
            cN * (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0).indicator (fun _ => (1 : ℝ)) x) ∧
        (∃ νb : ℝ, ∀ n, A0.ν n ≤ νb) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp1 : 1 ≤ p := by linarith
  have hs0 : 0 ≤ s := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨A, L, hA0, hL0, hbc⟩ := sa16y4_drift_const hd hs0 hsd m MB Λ ΛV G₀
  obtain ⟨cE, CN, B, Cg, B', hCN, hB0, hCg, happ⟩ :=
    sa16y5f_approx3 d m hd s p Λ A L MB hs1 hsd hA0 hL0 hMB MCls hFex
  obtain ⟨W, hW0, hdens⟩ := sa16y5_density_data hd m Λ
  refine ⟨cE, CN, B, hCN, hB0, fun D μ hD hMC t ht Cφ hCφ Φ hΦ => ?_⟩
  obtain ⟨hDs, -, -⟩ := hD.hs
  have hM0 : ∀ i j, |D.M i j| ≤ MB := hD.hM
  have hMB0 : 0 ≤ MB := (abs_nonneg _).trans (hM0 ⟨0, by omega⟩ ⟨0, by omega⟩)
  have htT : ∀ r ∈ Icc (0 : ℝ) t, r ∈ Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hμreg : ∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ r) := fun r hr =>
    sa16so_regDensity_of_MF hD.hμ.regular (htT r hr)
  have hpos : ∀ r ∈ Icc (0 : ℝ) t, ∀ x, 0 ≤ μ r x := fun r hr x => (hD.hμ.prob r (htT r hr)).nonneg x
  set b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun r => meanFieldDriftW D (μ r) with hbdef
  have hb : ∀ r ∈ Icc (0 : ℝ) t, ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) (b r) ∧ ‖b r 0‖ ≤ A ∧
      ∀ j, 1 ≤ j → j ≤ m + 2 → ∀ x, ‖iteratedFDeriv ℝ j (b r) x‖ ≤ L := fun r hr => hbc νbar T D μ hD r (htT r hr)
  have happ := happ D.M hMC hM0 t ht.1 μ hμreg hpos b hb
  have hνpos : ∀ n : ℕ, 0 < D.invβ + 1 / ((n : ℝ) + 1) := fun n => by
    have := hD.hν.1; positivity
  choose uu huu hsol hbound hDer hBdd hNiso hNb hBc hNc hsh hio using
    fun n : ℕ => happ (n + 1) (by omega) (D.invβ + 1 / ((n : ℝ) + 1)) (hνpos n) (Φ n)
  set Bm : ℝ := CN * Cφ * Real.exp (|cE| * t) with hBm
  have hbdn : ∀ n, ∀ r ∈ Icc (0 : ℝ) t, ‖sa16sz_iota2 d m p (uu n r)‖ ≤ Bm := by
    intro n r hr
    refine (hbound n r hr).trans ?_
    have h2 : Real.exp (cE * r) ≤ Real.exp (|cE| * t) := by
      refine Real.exp_le_exp.2 ?_
      calc cE * r ≤ |cE| * r := mul_le_mul_of_nonneg_right (le_abs_self _) hr.1
        _ ≤ |cE| * t := mul_le_mul_of_nonneg_left hr.2 (abs_nonneg _)
    rw [hBm]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hΦ n) hCN.le) h2 (Real.exp_pos _).le (by positivity)
  have hgrow : ∀ r ∈ Icc (0 : ℝ) t, ∀ j y, |b r y j| ≤ A + L * ‖y‖ := by
    intro r hr j y
    obtain ⟨hbs, hb0, hbL⟩ := hb r hr
    have hbs1 : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (b r) := hbs.of_le (by exact_mod_cast Nat.le_succ _)
    exact (sa16y4_comp_bounds (k := m + 1) (by omega) hbs1 hb0
      (fun k hk1 hkk x => hbL k hk1 (by omega) x) j).2.1 y
  have hdivb : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ cN R0 : ℝ, 0 ≤ cN ∧
      ∀ N : ℕ, 1 ≤ N → ∀ σ ∈ Icc (0 : ℝ) t, ∀ x, |sa16so_divFun (sa16y4_bcInt d N t b σ) ψ x| ≤
        cN * (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0).indicator (fun _ => (1 : ℝ)) x :=
    fun {ψ} hψ => sa16y4_bcInt_div_bound ht.1 hL0 hA0 b hgrow
      (fun N hN σ hσ => by
        have := hDer (N - 1) σ hσ
        rwa [Nat.sub_add_cancel hN] at this) hψ
  -- decay of the interpolated densities
  have haWall : ∀ N : ℕ, 1 ≤ N → ∀ σ ∈ Icc (0 : ℝ) t, ∀ x,
      |sa16y5_aInt d N t μ σ x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3)) := by
    intro N hN σ hσ x
    have hw0' : ∀ i ∈ Finset.range (N + 1), 0 ≤ sa16y4_hat N t i σ := fun i _ => sa16y4_hat_nonneg N t i σ
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.range (N + 1), |sa16y4_hat N t i σ * sa16q_mol N (μ (t - (i : ℝ) * t / N)) x|
        ≤ ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * (W * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [abs_mul, abs_of_nonneg (hw0' i hi)]
          exact mul_le_mul_of_nonneg_left
            (((hdens _ (hμreg _ (sa16y4_node_mem hN ht.1 hi))).2 N).2.2.2.1 x) (hw0' i hi)
      _ = W * (1 + ‖x‖) ^ (-((d : ℝ) + 3)) := by
          rw [← Finset.sum_mul, sa16y4_hat_sum hN ht.1 hσ, one_mul]
  -- uniform bound of the nonlocal pairing
  have hNl : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ n, ∀ r ∈ Icc (0 : ℝ) t,
      ∀ y, |sa16r_ell d m p hψ (sa16y5f_NInt d m (n + 1) p s D.M t μ r y)| ≤
        Cn * ‖sa16sz_iota2 d m p y‖ := by
    intro ψ hψ
    obtain ⟨cψ, Cb, hcψ0, hCb0, hκc, hprod, hmem⟩ := sa16y5_nl_data (p := p) hd hs0 hsd hW0 hψ
    refine ⟨(d : ℝ) * d * MB * cψ, by positivity, fun n r hr y => ?_⟩
    obtain ⟨hGood, hIso⟩ := hNiso n r hr
    have hc1 : Continuous (sa16y5_aInt d (n + 1) t μ r) := hGood.continuous
    have hmm := fun i => hmem _ hc1 (haWall (n + 1) (by omega) r hr) i
    rw [sa16y5f_nl_rep (p := p) hm hs0 hsd D.M (hGood.of_le (by exact_mod_cast le_top)) hψ (fun i => (hmm i).1) _ hIso y]
    exact sa16y5_Phi_bound hm D.M hM0 hcψ0 (fun i => (hmm i).1) (fun i => (hmm i).2)
      (fun i => (hc1.mul (hκc i)).aestronglyMeasurable) _
  obtain ⟨CNs, hCNs⟩ : ∃ CNs : ℕ → ℝ, ∀ n : ℕ, ∀ σ ∈ Icc (0 : ℝ) t, ∀ s' ∈ Ioc (0 : ℝ) t,
      ‖sa16y5_Qh d m p ((D.invβ + 1 / ((n : ℝ) + 1)) * s') (sa16y5f_NInt d m (n + 1) p s D.M t μ σ)‖ ≤
        CNs n * s' ^ (-((s + 2 - d) / 2)) := by
    choose CNs hCNs using hsh
    exact ⟨CNs, hCNs⟩
  let A0 : SA16ApproxF d m p t Bm ((s + 2 - d) / 2) :=
    { ν := fun n => D.invβ + 1 / ((n : ℝ) + 1), hν := hνpos,
      bc := fun n => sa16y4_bcInt d (n + 1) t b, B' := fun n => B' (n + 1),
      hbo := fun n r hr => hBdd n r hr,
      Bf := fun n r => sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t b r), hBf := fun n r => rfl,
      BB := fun n => sa16so_cB d (m + 1) (B' (n + 1)),
      hBb := fun n r hr => sa16so_B_norm (p := p) (hBdd n r hr), hBc := fun n x => hBc n x,
      N := fun n => sa16y5f_NInt d m (n + 1) p s D.M t μ, BN := fun _ => Cg,
      hNb := fun n r hr => hNb n r hr, hNc := fun n x => hNc n x,
      CN := CNs, hγ := by linarith, hγ1 := by linarith, hsharp := fun n r hr s' hs' => hCNs n r hr s' hs',
      hiota := fun n r hr a ha x => hio n r hr a ha x,
      φ := Φ, u := uu, hu := huu, hsol := hsol, hbd := hbdn }
  refine ⟨A0, fun n => rfl, fun n => rfl, fun n => rfl, fun n => rfl, fun n r hr => hbound n r hr,
    fun n σ hσ => hDer n σ hσ, fun n σ hσ => hNiso n σ hσ, fun {ψ} hψ => hNl hψ, fun {ψ} hψ => ?_, ?_⟩
  · obtain ⟨cN, R0, hcN, hh⟩ := hdivb hψ
    exact ⟨cN, R0, hcN, fun n r hr x => hh (n + 1) (by omega) r hr x⟩
  · exact ⟨D.invβ + 1, fun n => by
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
      show D.invβ + 1 / ((n : ℝ) + 1) ≤ D.invβ + 1
      linarith⟩

end Fm4

end HRS.Whole.AppendixA.Phase2SA16R
