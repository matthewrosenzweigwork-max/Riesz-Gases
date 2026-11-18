import HRS.MS.SA16Y4Fin4
import HRS.MS.SA16Y4Fin3
import HRS.MS.SA16Y4Fin2
import HRS.MS.SA16Y6CAp3
import HRS.MS.SA16Y5Lm1
import HRS.MS.SA16Y5Lm3
import HRS.MS.SA16Y5Nf4
import HRS.MS.SA16Y4Lf2
import HRS.MS.SA16Y4Wl1
import HRS.MS.SA16Y4Tc3
import HRS.MS.SA16Y4Id3
import HRS.MS.SA16SNl4
import HRS.MS.SA12LimitL7
import HRS.MS.SA16Y6C1
import HRS.MS.SA16Y5Fin5

/-! # SA16Y6 critical-case copy of SA16Y5Fin5 (s = d-1) -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Fin5
variable {d : ℕ}
set_option maxHeartbeats 6400000 in
theorem sa16y6c_iso_limit (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s = (d : ℝ) - 1) (hθ0 : 0 < s + 2 - d)
    (m : ℕ) (hm : 1 ≤ m) (p : ℝ) [Fact (2 ≤ p)] (hfar : (d : ℝ) < p * (s + 1)) (MB Λ ΛV G₀ νbar T : ℝ)
    (MCls : Matrix (Fin d) (Fin d) ℝ → Prop)
    (hHd : ∀ Wd : ℝ, 0 ≤ Wd → ∃ cN : ℝ, 0 ≤ cN ∧ ∀ {M : Matrix (Fin d) (Fin d) ℝ}, MCls M →
      (∀ i j, |M i j| ≤ MB) → ∀ {μ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) →
      sa16z_Cb 2 Wd μ → sa16y5_Dec (m + 2) Wd μ → ∀ (N' : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p),
        SA16IsoOp d (m + 1) p s M μ N' → ∀ G : WmpSpace d (m + 1 + 1) p,
          fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(sa16r_iota d m p (N' G))) ≤
            cN * jetEnergy d m p (sa16sz_iota2 d m p G)) :
    ∃ Kc cE : ℝ, 0 ≤ Kc ∧ ∀ (D : WholeDyn d) (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ →
      MCls D.M → ∀ t ∈ Ioc (0 : ℝ) T,
      ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, wNormE m p φ < ⊤ →
      ∃ G : ℝ → WmpSpace d m p,
        (∀ τ ∈ Icc (0 : ℝ) t, ‖G τ‖ ≤ Kc * (wNormE m p φ).toReal * Real.exp (cE * τ)) ∧
        (∀ ℓ : StrongDual ℝ (WmpSpace d m p), ContinuousOn (fun τ => ℓ (G τ)) (Icc (0 : ℝ) t)) ∧
        ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ}, IsCcInfty ψ →
          (∀ τ ∈ Icc (0 : ℝ) t, ∫ x, (fun τ x => wrep d m p (G τ) x) τ x * ψ x = (∫ x, φ x * ψ x) +
            ∫ σ in Icc (0 : ℝ) τ, forwardWeakTerm (D.coeff μ) t (fun τ x => wrep d m p (G τ) x) ψ σ) ∧
          IntegrableOn (fun σ => forwardWeakTerm (D.coeff μ) t (fun τ x => wrep d m p (G τ) x) ψ σ) (Icc 0 t) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp1 : 1 ≤ p := by linarith
  have hsd : s < d := by linarith
  obtain ⟨A, L, hA0, hL0, hbc⟩ := sa16y4_drift_const hd hs0 hsd m MB Λ ΛV G₀
  obtain ⟨cE, CN, B, Cg, B', Bk, hCN, hB0, hCg, happ⟩ :=
    sa16y6c_approx3 d m hd s p Λ A L MB hs0 hs1 hθ0 hfar hA0 hL0 MCls hHd
  obtain ⟨Cl, hCl0, hlift⟩ := sa16y4_data_lifts (d := d) (p := p) hp1 m
  obtain ⟨W, hW0, hdens⟩ := sa16y5_density_data hd m Λ
  refine ⟨CN * Cl, cE, by positivity, fun D μ hD hMC t ht φ hφ => ?_⟩
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
  obtain ⟨Φ, hΦbd, hΦlim⟩ := hlift φ hφ
  choose uu huu hsol hbound hDer hBdd hNiso hKb hBk0 hKc using
    fun n : ℕ => happ (n + 1) (by omega) (D.invβ + 1 / ((n : ℝ) + 1)) (hνpos n) (Φ n)
  set w : ℝ := (wNormE m p φ).toReal with hw
  have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
  set Bm : ℝ := CN * (Cl * w) * Real.exp (|cE| * t) with hBm
  have hBm0 : 0 ≤ Bm := by positivity
  have hbdn : ∀ n, ∀ r ∈ Icc (0 : ℝ) t, ‖sa16sz_iota2 d m p (uu n r)‖ ≤ Bm := by
    intro n r hr
    refine (hbound n r hr).trans ?_
    have h1 : ‖sa16sz_iota2 d m p (Φ n)‖ ≤ Cl * w := hΦbd n
    have h2 : Real.exp (cE * r) ≤ Real.exp (|cE| * t) := by
      refine Real.exp_le_exp.2 ?_
      calc cE * r ≤ |cE| * r := mul_le_mul_of_nonneg_right (le_abs_self _) hr.1
        _ ≤ |cE| * t := mul_le_mul_of_nonneg_left hr.2 (abs_nonneg _)
    rw [hBm]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hCN.le) h2 (Real.exp_pos _).le (by positivity)
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
      ∀ y, |sa16r_ell d (m + 1) p hψ (sa16y5_NInt d m (n + 1) p s D.M t μ r y)| ≤
        Cn * ‖sa16sz_iota2 d m p y‖ := by
    intro ψ hψ
    obtain ⟨cψ, Cb, hcψ0, hCb0, hκc, hprod, hmem⟩ := sa16y5_nl_data (p := p) hd hs0 hsd hW0 hψ
    refine ⟨(d : ℝ) * d * MB * cψ, by positivity, fun n r hr y => ?_⟩
    obtain ⟨hGood, hIso⟩ := hNiso n r hr
    have hc1 : Continuous (sa16y5_aInt d (n + 1) t μ r) := hGood.1.continuous
    have hmm := fun i => hmem _ hc1 (haWall (n + 1) (by omega) r hr) i
    rw [sa16y5_nl_rep (p := p) hm hs0 hsd D.M hGood.1 hψ (fun i => (hmm i).1) _ hIso y]
    exact sa16y5_Phi_bound hm D.M hM0 hcψ0 (fun i => (hmm i).1) (fun i => (hmm i).2)
      (fun i => (hc1.mul (hκc i)).aestronglyMeasurable) _
  let A0 : SA16ApproxI d m p t Bm :=
    { ν := fun n => D.invβ + 1 / ((n : ℝ) + 1), hν := hνpos,
      bc := fun n => sa16y4_bcInt d (n + 1) t b, B' := fun n => B' (n + 1),
      hbo := fun n r hr => hBdd n r hr,
      N := fun n => sa16y5_NInt d m (n + 1) p s D.M t μ,
      K := fun n => sa16y5_Kint d m (n + 1) p s D.M t μ b, hK := fun n r => rfl,
      Bk := fun n => Bk (n + 1), hKb := fun n r hr => hKb n r hr, hKc := fun n x => hKc n x,
      φ := Φ, u := uu, hu := huu, hsol := hsol, hbd := hbdn }
  obtain ⟨φs, hφs, G, hGn, hGw, hGc, hlim⟩ := sa16y5_weak_limit (p := p) ht.1 A0 hNl
    (fun {ψ} hψ => by
      obtain ⟨cN, R0, hcN, hh⟩ := hdivb hψ
      exact ⟨cN, R0, hcN, fun n r hr x => hh (n + 1) (by omega) r hr x⟩)
    ⟨D.invβ + 1, fun n => by
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
      show D.invβ + 1 / ((n : ℝ) + 1) ≤ D.invβ + 1
      linarith⟩
  have hbound' : ∀ τ ∈ Icc (0 : ℝ) t, ‖G τ‖ ≤ CN * Cl * w * Real.exp (cE * τ) := by
    intro τ hτ
    refine sa16y4_norm_le_of_weak (fun j => sa16sz_iota2 d m p (uu (φs j) τ)) (G τ)
      (b := CN * Cl * w * Real.exp (cE * τ)) (fun j => ?_) (fun ℓ => hGw τ hτ ℓ)
    refine (hbound (φs j) τ hτ).trans ?_
    have h1 : ‖sa16sz_iota2 d m p (Φ (φs j))‖ ≤ Cl * w := hΦbd (φs j)
    calc CN * ‖sa16sz_iota2 d m p (Φ (φs j))‖ * Real.exp (cE * τ) ≤ CN * (Cl * w) * Real.exp (cE * τ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hCN.le) (Real.exp_pos _).le
      _ = CN * Cl * w * Real.exp (cE * τ) := by ring
  refine ⟨G, hbound', hGc, fun {ψ} hψ => ?_⟩
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
    have hνl : Tendsto (fun j => D.invβ + 1 / ((φs j : ℝ) + 1)) atTop (𝓝 D.invβ) := by
      have h := (tendsto_const_nhds (x := D.invβ)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφs.tendsto_atTop)
      simpa using h
    have hcl : ∀ k : Fin d, ContDiff ℝ 1 (fun y => b (t - σ) y k) := fun k =>
      ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff.comp
        ((hb (t - σ) hr).1.of_le (by exact_mod_cast (by omega : 1 ≤ m + 2))))
    have huni : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ k x, ‖x‖ ≤ R0 →
        |sa16y4_bcInt d (φs j + 1) t b σ k x - b (t - σ) x k| ≤ ε := fun ε hε =>
      hNj.eventually (sa16y4_bcInt_tendsto t L ht.1 hL0 b hbcont hblip hdpt' hσ R0 hε)
    -- the nonlocal data
    obtain ⟨cψ, Cb, hcψ0, hCb0, hκc, hprod, hmem⟩ := sa16y5_nl_data (p := p) hd hs0 hsd hW0 hψ
    have hGI := fun j => hNiso (φs j) σ hσ
    have haWj : ∀ j x, |sa16y5_aInt d (φs j + 1) t μ σ x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3)) :=
      fun j x => haWall (φs j + 1) (by omega) σ hσ x
    have hmj := fun j i => hmem _ (hGI j).1.1.continuous (haWj j) i
    have hμr := hdens (μ (t - σ)) (hμreg _ hr)
    have hμc : Continuous (μ (t - σ)) := hμr.1.1.1.continuous
    have hr1 := sa16y5_f_tendsto2 (p := p) (m := m) hm hd hs0 hsd D.M (W := W) (Bm := Bm) (R0 := R0)
      (νlim := D.invβ) hW0 (Bj := fun j => B' (φs j + 1)) (fun j => D.invβ + 1 / ((φs j : ℝ) + 1)) hνl
      (fun j => sa16y4_bcInt d (φs j + 1) t b σ) (fun j => hBdd (φs j) σ hσ)
      (fun k y => b (t - σ) y k) hcl hψ (sa16sw_cc_lap hψ) hψ0 huni
      (fun j => sa16y5_aInt d (φs j + 1) t μ σ) (μ (t - σ))
      (fun j => (hGI j).1.1) hμr.1.1.1 haWj hμr.1.2
      (fun x => (sa16y4_aInt_tendsto hd (m := m) (Λ := Λ) ht.1 μ hμreg hmupt' hσ x).comp hNj)
      (fun j => sa16y5_NInt d m (φs j + 1) p s D.M t μ σ)
      (fun j y => sa16y5_nl_rep (p := p) hm hs0 hsd D.M (hGI j).1.1 hψ (fun i => (hmj j i).1) _ (hGI j).2 y)
      (fun j => sa16y5_Kint d m (φs j + 1) p s D.M t μ b σ) (fun j => rfl)
      (fun j => uu (φs j) σ) (G σ) (fun j => hbdn (φs j) σ hσ) (fun ℓ => hGw σ hσ ℓ)
    have hs0' : 0 ≤ (D.coeff μ).s := by simpa [WholeDyn.coeff, hDs] using hs0
    have hsd' : (D.coeff μ).s < d := by simpa [WholeDyn.coeff, hDs] using hsd
    obtain ⟨K, -, hK⟩ := HRS.MH.AdjointRd.Phase2SA12Limit.test_nonlocal_decay hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T D μ hD ψ hψ
    obtain ⟨hKc', hKb'⟩ := hK (t - σ) (htT _ hr)
    obtain ⟨hq1, hq⟩ := sa16so_conj_facts (p := p)
    have hNt : MemLp (nonlocalTestRd (D.coeff μ) (t - σ) ψ) (ENNReal.conjExponent (ENNReal.ofReal p)) volume :=
      sa16so_memLp_decay hKc' (K := K) (r := (d : ℝ) + 3 + s + 1) (by linarith [hs0]) hKb' hq1 hq
    have hN1 := fun i => (hmem (μ (t - σ)) hμc hμr.1.2 i).1
    have eNL : sa16y5_Phi d m hm p s D.M (μ (t - σ)) ψ (G σ) =
        ∫ x, wrep d m p (G σ) x * nonlocalTestRd (D.coeff μ) (t - σ) ψ x := by
      have := sa16y5_Phi_eq (p := p) hm (D.coeff μ) (t - σ) hs0' hsd'
        (by simpa [WholeDyn.coeff] using hμr.1.1.1) hψ (by simpa [WholeDyn.coeff, hDs] using hN1) hNt (G σ)
      simpa [WholeDyn.coeff, hDs] using this
    have e := sa16y4_flim_eq (p := p) (D.coeff μ) t σ (fun τ x => wrep d m p (G τ) x) (G σ) rfl hψ
      (fun k => (hcl k).differentiable (by simp))
    rw [← e, ← eNL]
    exact hr1
  obtain ⟨hid, hint⟩ := hlim hψ (∫ x, φ x * ψ x)
    (fun σ => forwardWeakTerm (D.coeff μ) t (fun τ x => wrep d m p (G τ) x) ψ σ) (hΦlim hψ) hflim
  exact ⟨sa16y4_eq_field (D.coeff μ) t G φ hψ hid, hint⟩

end Fin5

end HRS.Whole.AppendixA.Phase2SA16R
