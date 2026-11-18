import HRS.MS.SA16Y9Wp1
import HRS.MS.SA16Y4Fin5

/-!
# S.A.16 (SA16Y9) Fm1: the approximation family `A0` of a sub-regime datum, exposed (stability, G2c, part 1)

`sa16y9_sub_fam`: the first half of `sa16y4_sub_limit` (Fin5), with the data lift `Φ` an input and the family returned as an
`SA16Approx` record `A0` with its defining equalities (`ν_n = ν + 1/(n+1)`, `bcInt`, `GInt`, `Kint`), the level-`m` bound and the
uniform `SA16DerCoef` bound, together with the `hdiv`/`hνb` hypotheses of `sa16y4_weak_limit`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Fm1
variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem sa16y9_sub_fam (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (p : ℝ)
    [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (hsub : s ≤ (d : ℝ) - 2 ∧ (d : ℝ) < p * (s + 1)) :
    ∃ cE CN B CG : ℝ, 0 < CN ∧ 0 ≤ B ∧ 0 ≤ CG ∧
      ∀ (D : WholeDyn d) (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → ∀ t ∈ Ioc (0 : ℝ) T, ∀ Cφ : ℝ, 0 ≤ Cφ →
      ∀ Φ : ℕ → WmpSpace d (m + 1 + 1) p, (∀ n, ‖sa16sz_iota2 d m p (Φ n)‖ ≤ Cφ) →
      ∃ A0 : SA16Approx d m p t CG (CN * Cφ * Real.exp (|cE| * t)),
        (∀ n, A0.φ n = Φ n) ∧ (∀ n, A0.ν n = D.invβ + 1 / ((n : ℝ) + 1)) ∧
        (∀ n, A0.bc n = sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D (μ r))) ∧
        (∀ n, A0.T1 n = sa16y4_GInt d (m + 1) (n + 1) p s D.M t μ) ∧
        (∀ n, A0.T0 n = sa16y4_GInt d m (n + 1) p s D.M t μ) ∧
        (∀ n, A0.K n = sa16y4_Kint d m (n + 1) p s D.M t μ (fun r => meanFieldDriftW D (μ r))) ∧
        (∀ n, ∀ r ∈ Icc (0 : ℝ) t, ‖sa16sz_iota2 d m p (A0.u n r)‖ ≤
          CN * ‖sa16sz_iota2 d m p (Φ n)‖ * Real.exp (cE * r)) ∧
        (∀ n, ∀ σ ∈ Icc (0 : ℝ) t, SA16DerCoef (m + 1) B (A0.bc n σ)) ∧
        (∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ), ∃ cN R0 : ℝ, 0 ≤ cN ∧
          ∀ n, ∀ r ∈ Icc (0 : ℝ) t, ∀ x, |sa16so_divFun (A0.bc n r) ψ x| ≤
            cN * (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0).indicator (fun _ => (1 : ℝ)) x) ∧
        (∃ νb : ℝ, ∀ n, A0.ν n ≤ νb) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  obtain ⟨A, L, hA0, hL0, hbc⟩ := sa16y4_drift_const hd hs0 hsd m MB Λ ΛV G₀
  obtain ⟨cE, CN, B, CG, B', Bk, hCN, hB0, hCG, happ⟩ :=
    sa16y4_approx2 d m hd s p MB Λ A L hs0 hsub.1 hsub.2 hA0 hL0
  refine ⟨cE, CN, B, CG, hCN, hB0, hCG, fun D μ hD t ht Cφ hCφ Φ hΦ => ?_⟩
  have htT : ∀ r ∈ Icc (0 : ℝ) t, r ∈ Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hμreg : ∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ r) := fun r hr =>
    sa16so_regDensity_of_MF hD.hμ.regular (htT r hr)
  have hM : ∀ i j, |D.M i j| ≤ MB := hD.hM
  set b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun r => meanFieldDriftW D (μ r) with hbdef
  have hb : ∀ r ∈ Icc (0 : ℝ) t, ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) (b r) ∧ ‖b r 0‖ ≤ A ∧
      ∀ j, 1 ≤ j → j ≤ m + 2 → ∀ x, ‖iteratedFDeriv ℝ j (b r) x‖ ≤ L := fun r hr => hbc νbar T D μ hD r (htT r hr)
  have happ := happ t ht.1 D.M hM μ hμreg b hb
  have hνpos : ∀ n : ℕ, 0 < D.invβ + 1 / ((n : ℝ) + 1) := fun n => by
    have := hD.hν.1; positivity
  choose uu huu hsol hbound hDer hBdd hT0n hcompn hKb hBk0 hKc using
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
  let A0 : SA16Approx d m p t CG Bm :=
    { ν := fun n => D.invβ + 1 / ((n : ℝ) + 1), hν := hνpos,
      bc := fun n => sa16y4_bcInt d (n + 1) t b, B' := fun n => B' (n + 1),
      hbo := fun n r hr => hBdd n r hr,
      T1 := fun n => sa16y4_GInt d (m + 1) (n + 1) p s D.M t μ,
      T0 := fun n => sa16y4_GInt d m (n + 1) p s D.M t μ,
      hcomp := fun n r hr => hcompn n r hr, hT0 := fun n r hr => hT0n n r hr,
      K := fun n => sa16y4_Kint d m (n + 1) p s D.M t μ b, hK := fun n r => rfl,
      Bk := fun n => Bk (n + 1), hKb := fun n r hr => hKb n r hr, hKc := fun n x => hKc n x,
      φ := Φ, u := uu, hu := huu, hsol := hsol, hbd := hbdn }
  refine ⟨A0, fun n => rfl, fun n => rfl, fun n => rfl, fun n => rfl, fun n => rfl, fun n => rfl,
    fun n r hr => hbound n r hr, fun n σ hσ => hDer n σ hσ, fun {ψ} hψ => ?_, ?_⟩
  · obtain ⟨cN, R0, hcN, hh⟩ := hdivb hψ
    exact ⟨cN, R0, hcN, fun n r hr x => hh (n + 1) (by omega) r hr x⟩
  · exact ⟨D.invβ + 1, fun n => by
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
      show D.invβ + 1 / ((n : ℝ) + 1) ≤ D.invβ + 1
      linarith⟩

end Fm1

end HRS.Whole.AppendixA.Phase2SA16R
