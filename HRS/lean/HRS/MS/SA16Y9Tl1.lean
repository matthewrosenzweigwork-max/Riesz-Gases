import HRS.MS.SA16Y9Fm1

/-!
# S.A.16 (SA16Y9) Tl1: the weak identity of the limit of a sub-regime approximation family (stability, G2c, part 2)

`sa16y9_sub_tail`: the second half of `sa16y4_sub_limit` (Fin5) for the family `A0` of `sa16y9_sub_fam` along any subsequence `φs`
with `ι² u_{φs j}(τ) ⇀ G τ` (and the conditional limit identity `A0.LimId φs G`): the path `τ ↦ wrep (G τ)` satisfies the frozen
weak identity of `IsForwardSolutionRd`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Tl1
variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem sa16y9_sub_tail (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (p : ℝ)
    [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (hsub : s ≤ (d : ℝ) - 2 ∧ (d : ℝ) < p * (s + 1))
    (D : WholeDyn d) (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) {CG Bm : ℝ} (A0 : SA16Approx d m p t CG Bm)
    (hνe : ∀ n, A0.ν n = D.invβ + 1 / ((n : ℝ) + 1))
    (hbce : ∀ n, A0.bc n = sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D (μ r)))
    (hT0e : ∀ n, A0.T0 n = sa16y4_GInt d m (n + 1) p s D.M t μ)
    (φs : ℕ → ℕ) (hφs : StrictMono φs) (G : ℝ → WmpSpace d m p)
    (hGw : ∀ τ ∈ Icc (0 : ℝ) t, ∀ ℓ : StrongDual ℝ (WmpSpace d m p),
      Tendsto (fun j => ℓ (sa16sz_iota2 d m p (A0.u (φs j) τ))) atTop (𝓝 (ℓ (G τ))))
    (hΦlim : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ),
      Tendsto (fun n => sa16r_ell d (m + 1 + 1) p hψ (A0.φ n)) atTop (𝓝 (∫ x, φ x * ψ x)))
    (hlim : A0.LimId φs G) :
    ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ}, IsCcInfty ψ →
      (∀ τ ∈ Icc (0 : ℝ) t, ∫ x, (fun τ x => wrep d m p (G τ) x) τ x * ψ x = (∫ x, φ x * ψ x) +
        ∫ σ in Icc (0 : ℝ) τ, forwardWeakTerm (D.coeff μ) t (fun τ x => wrep d m p (G τ) x) ψ σ) ∧
      IntegrableOn (fun σ => forwardWeakTerm (D.coeff μ) t (fun τ x => wrep d m p (G τ) x) ψ σ) (Icc 0 t) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  obtain ⟨A, L, hA0, hL0, hbc⟩ := sa16y4_drift_const hd hs0 hsd m MB Λ ΛV G₀
  obtain ⟨W, hW0, hdens⟩ := sa16y4_density_data (p := p) hd m s MB Λ hs0 hsub.1 hsub.2
  obtain ⟨hDs, -, -⟩ := hD.hs
  have htT : ∀ r ∈ Icc (0 : ℝ) t, r ∈ Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hμreg : ∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ r) := fun r hr =>
    sa16so_regDensity_of_MF hD.hμ.regular (htT r hr)
  have hM : ∀ i j, |D.M i j| ≤ MB := hD.hM
  set b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun r => meanFieldDriftW D (μ r) with hbdef
  have hb : ∀ r ∈ Icc (0 : ℝ) t, ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) (b r) ∧ ‖b r 0‖ ≤ A ∧
      ∀ j, 1 ≤ j → j ≤ m + 2 → ∀ x, ‖iteratedFDeriv ℝ j (b r) x‖ ≤ L := fun r hr => hbc νbar T D μ hD r (htT r hr)
  intro ψ hψ
  have hd2 : 2 ≤ d := by
    have : (2 : ℝ) ≤ d := by linarith [hsub.1]
    exact_mod_cast this
  obtain ⟨hdpt, hmupt⟩ := sa16y4_drift_time hd hs0 hsd hD
  have hdpt' : ∀ x j, ContinuousOn (fun r => b r x j) (Icc (0 : ℝ) t) := fun x j => (hdpt x j).mono htT
  have hmupt' : ∀ y, ContinuousOn (fun r => μ r y) (Icc (0 : ℝ) t) := fun y => (hmupt y).mono htT
  have hbcont : ∀ r ∈ Icc (0 : ℝ) t, ∀ j, Continuous (fun y => b r y j) := fun r hr j =>
    ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.comp (hb r hr).1.continuous)
  have hblip : ∀ r ∈ Icc (0 : ℝ) t, ∀ (j : Fin d) (x y : EuclideanSpace ℝ (Fin d)), |b r x j - b r y j| ≤ L * ‖x - y‖ :=
    fun r hr j x y => sa16y4_comp_lip (k := m + 2) (by omega) (hb r hr).1 (fun z => (hb r hr).2.2 1 le_rfl (by omega) z) j x y
  obtain ⟨R1, hR1⟩ := hψ.2.isCompact.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  set R0 : ℝ := max R1 0 with hR0
  have hψ0 : ∀ x, R0 < ‖x‖ → ψ x = 0 := by
    intro x hx
    by_contra hne
    have : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) R1 := hR1 (subset_tsupport ψ hne)
    rw [mem_closedBall_zero_iff] at this
    exact absurd (lt_of_le_of_lt this (lt_of_le_of_lt (le_max_left _ _) hx)) (lt_irrefl _)
  have hflim : ∀ σ ∈ Icc (0 : ℝ) t, Tendsto (fun j => A0.f hψ (φs j) σ) atTop
      (𝓝 (forwardWeakTerm (D.coeff μ) t (fun τ x => wrep d m p (G τ) x) ψ σ)) := by
    intro σ hσ
    have hr : t - σ ∈ Icc (0 : ℝ) t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    have hNj : Tendsto (fun j => φs j + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp hφs.tendsto_atTop
    have hνl : Tendsto (fun j => A0.ν (φs j)) atTop (𝓝 D.invβ) := by
      have h := (tendsto_const_nhds (x := D.invβ)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφs.tendsto_atTop)
      simp_rw [hνe]
      simpa using h
    have hcl : ∀ k : Fin d, ContDiff ℝ 1 (fun y => b (t - σ) y k) := fun k =>
      ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff.comp
        ((hb (t - σ) hr).1.of_le (by exact_mod_cast (by omega : 1 ≤ m + 2))))
    have huni : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ k x, ‖x‖ ≤ R0 →
        |A0.bc (φs j) σ k x - b (t - σ) x k| ≤ ε := by
      intro ε hε
      have := hNj.eventually (sa16y4_bcInt_tendsto t L ht.1 hL0 b hbcont hblip hdpt' hσ R0 hε)
      filter_upwards [this] with j hj
      rw [hbce]
      exact hj
    have hnode : ∀ N : ℕ, 1 ≤ N → ∀ i ∈ Finset.range (N + 1),
        IsRegularDensityW (m + 3) Λ (μ (t - (i : ℝ) * t / N)) := fun N hN i hi => hμreg _ (sa16y4_node_mem hN ht.1 hi)
    have hsum : ∀ N : ℕ, 1 ≤ N →
        sa16y4_Good (fun y => ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * sa16q_mol N (μ (t - (i : ℝ) * t / N)) y) ∧
        SA16SubOp d m p s D.M (fun y => ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * sa16q_mol N (μ (t - (i : ℝ) * t / N)) y)
          (sa16y4_GInt d m N p s D.M t μ σ) := fun N hN =>
      sa16y4_subop_sum hd2 hs0 hsub.1 D.M (fun i => sa16y4_hat N t i σ)
        (fun i => sa16q_mol N (μ (t - (i : ℝ) * t / N)))
        (fun i => sa16so_G d m p s D.M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))) (Finset.range (N + 1))
        (fun i hi => ((hdens D.M hM _ (hnode N hN i hi)).2 N).1)
        (fun i hi => ((hdens D.M hM _ (hnode N hN i hi)).2 N).2.2)
    have haW : ∀ N : ℕ, 1 ≤ N → ∀ x, |∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ *
        sa16q_mol N (μ (t - (i : ℝ) * t / N)) x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3)) := by
      intro N hN x
      have hw0 : ∀ i ∈ Finset.range (N + 1), 0 ≤ sa16y4_hat N t i σ := fun i _ => sa16y4_hat_nonneg N t i σ
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ Finset.range (N + 1), |sa16y4_hat N t i σ * sa16q_mol N (μ (t - (i : ℝ) * t / N)) x|
          ≤ ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * (W * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [abs_mul, abs_of_nonneg (hw0 i hi)]
            exact mul_le_mul_of_nonneg_left (((hdens D.M hM _ (hnode N hN i hi)).2 N).2.1 x) (hw0 i hi)
        _ = W * (1 + ‖x‖) ^ (-((d : ℝ) + 3)) := by
            rw [← Finset.sum_mul, sa16y4_hat_sum hN ht.1 hσ, one_mul]
    have hμr := hdens D.M hM (μ (t - σ)) (hμreg _ hr)
    have hr1 := sa16y4_f_tendsto2 (p := p) (m := m) hm hd hs0 hsd D.M (W := W) (Bm := Bm) (R0 := R0)
      (νlim := D.invβ) hW0 (Bj := fun j => A0.B' (φs j)) (fun j => A0.ν (φs j)) hνl
      (fun j => A0.bc (φs j) σ) (fun j => A0.hbo (φs j) σ hσ)
      (fun k y => b (t - σ) y k) hcl hψ (sa16sw_cc_lap hψ) hψ0 huni
      (fun j y => ∑ i ∈ Finset.range (φs j + 1 + 1), sa16y4_hat (φs j + 1) t i σ *
        sa16q_mol (φs j + 1) (μ (t - (i : ℝ) * t / ((φs j + 1 : ℕ) : ℝ))) y)
      (μ (t - σ))
      (fun j => (hsum (φs j + 1) (by omega)).1.1) hμr.1.1.1
      (fun j x => haW (φs j + 1) (by omega) x) hμr.1.2.1
      (fun x => (sa16y4_aInt_tendsto hd (m := m) (Λ := Λ) ht.1 μ hμreg hmupt' hσ x).comp hNj)
      (fun j => A0.T1 (φs j) σ)
      (fun j => A0.T0 (φs j) σ)
      (fun j => by rw [hT0e (φs j)]; exact (hsum (φs j + 1) (by omega)).2) (fun j => A0.hcomp (φs j) σ hσ)
      (sa16so_G d m p s D.M (μ (t - σ))) hμr.1.2.2
      (fun j => A0.K (φs j) σ) (fun j => A0.hK (φs j) σ)
      (fun j => A0.u (φs j) σ) (G σ) (fun j => A0.hbd (φs j) σ hσ) (fun ℓ => hGw σ hσ ℓ)
    have hs0' : 0 ≤ (D.coeff μ).s := by simpa [WholeDyn.coeff, hDs] using hs0
    have hsd' : (D.coeff μ).s < d := by simpa [WholeDyn.coeff, hDs] using hsd
    obtain ⟨K, -, hK⟩ := HRS.MH.AdjointRd.Phase2SA12Limit.test_nonlocal_decay hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD ψ hψ
    obtain ⟨hKc', hKb'⟩ := hK (t - σ) (htT _ hr)
    obtain ⟨hq1, hq⟩ := sa16so_conj_facts (p := p)
    have hN : MemLp (nonlocalTestRd (D.coeff μ) (t - σ) ψ) (ENNReal.conjExponent (ENNReal.ofReal p)) volume :=
      sa16so_memLp_decay hKc' (K := K) (r := (d : ℝ) + 3 + s + 1) (by linarith [hs0]) hKb' hq1 hq
    have eNL : sa16r_ell d m p hψ (sa16so_G d m p s D.M (μ (t - σ)) (G σ)) =
        ∫ x, wrep d m p (G σ) x * nonlocalTestRd (D.coeff μ) (t - σ) ψ x :=
      sa16so_weak_G (p := p) m (D.coeff μ) (t - σ) hs0' hsd' (by simpa [WholeDyn.coeff] using hμr.1.1.1) hψ hN
        (sa16so_G d m p s D.M (μ (t - σ))) (fun φ' => by simpa [WholeDyn.coeff, hDs] using hμr.1.2.2 φ') (G σ)
    have e := sa16y4_flim_eq (p := p) (D.coeff μ) t σ (fun τ x => wrep d m p (G τ) x) (G σ) rfl hψ
      (fun k => (hcl k).differentiable (by simp))
    rw [← e, ← eNL]
    exact hr1
  obtain ⟨hid, hint⟩ := hlim hψ (∫ x, φ x * ψ x)
    (fun σ => forwardWeakTerm (D.coeff μ) t (fun τ x => wrep d m p (G τ) x) ψ σ) (hΦlim hψ) hflim
  exact ⟨sa16y4_eq_field (D.coeff μ) t G φ hψ hid, hint⟩

end Tl1

end HRS.Whole.AppendixA.Phase2SA16R
