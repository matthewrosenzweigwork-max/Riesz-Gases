import HRS.MS.UniqE3g

/-!
# E3 of `UniqPlan.md`, part 8: the combined estimate `e3_diffusion_transport`

For the flow bundle of `b^σ = meanFieldDriftW D (ρ (t-σ))`, `u` with `ulocNormE 1 χ u ≤ B`, `σ ∈ [0,t]`,
`ε ∈ (0,1]`, a centre `c`, `ς = ς_c^σ`, `z_ε = η_ε * u`, `φ_σ = η_ε * (ς z_ε)` (`phiTest`):

`2 (ν ∫ u Δφ_σ - ∫ u ∑_i ∂_i(b_i φ_σ)) + ∫ (b·∇ς) z_ε² ≤ -ν ∫ ς |∇z_ε|² + C₁ (ν+1) E_ε(σ) + C₂ ε B²`,

with `E_ε(σ) = cellEnergy χ Ψ σ z_ε`, constants independent of `u, B, σ, ε, c`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3

variable {d : ℕ}

/-- The test function `φ_σ = η_ε * (ς_c^σ z_ε)` of `e2_energy_identity`. -/
def phiTest (d : ℕ) (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d) (σ : ℝ) (c : Euc d) (ε : ℝ)
    (u : Euc d → ℝ) : Euc d → ℝ :=
  fun y => ∫ x, (varsigma χ Ψ σ c x * moll d ε u x) * eta d ε (x - y)

theorem phiTest_eq_moll (χ : Euc d → ℝ) (Ψ : ℝ → Euc d → Euc d) (σ : ℝ) (c : Euc d) (ε : ℝ)
    (u : Euc d → ℝ) :
    phiTest d χ Ψ σ c ε u = moll d ε (fun x => varsigma χ Ψ σ c x * moll d ε u x) :=
  e3_phi_eq_moll _

theorem e3_D1_prod_bound {ς z : Euc d → ℝ} (hς : ContDiff ℝ 1 ς) (hz : ContDiff ℝ 1 z) {K : ℝ}
    (hK : ∀ x, ‖fderiv ℝ ς x‖ ≤ K) (hς0 : ∀ x, 0 ≤ ς x) (hς1 : ∀ x, ς x ≤ 1) (i : Fin d)
    (x : Euc d) :
    D1 i (fun y => ς y * z y) x ^ 2 ≤ 2 * K ^ 2 * z x ^ 2 + 2 * ‖fderiv ℝ z x‖ ^ 2 := by
  rw [e3_D1_mul (hς.differentiable (by simp)) (hz.differentiable (by simp))]
  have h1 : |D1 i z x| ≤ ‖fderiv ℝ z x‖ := e3_abs_apply_le _ i
  have h2 : |D1 i ς x| ≤ K := (e3_abs_apply_le _ i).trans (hK x)
  have h3 : (ς x * D1 i z x) ^ 2 ≤ ‖fderiv ℝ z x‖ ^ 2 := by
    have : |ς x * D1 i z x| ≤ ‖fderiv ℝ z x‖ := by
      rw [abs_mul, abs_of_nonneg (hς0 x)]
      calc ς x * |D1 i z x| ≤ 1 * ‖fderiv ℝ z x‖ :=
            mul_le_mul (hς1 x) h1 (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    calc (ς x * D1 i z x) ^ 2 = |ς x * D1 i z x| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) this 2
  have h4 : (z x * D1 i ς x) ^ 2 ≤ K ^ 2 * z x ^ 2 := by
    have : |z x * D1 i ς x| ≤ |z x| * K := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    calc (z x * D1 i ς x) ^ 2 = |z x * D1 i ς x| ^ 2 := (sq_abs _).symm
      _ ≤ (|z x| * K) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = K ^ 2 * z x ^ 2 := by rw [mul_pow, sq_abs]; ring
  nlinarith [sq_nonneg (ς x * D1 i z x - z x * D1 i ς x)]

theorem e3_div_term_bound {b : Euc d → Euc d} {Cb : ℝ} (hdrift : DriftFacts b Cb)
    {ς z : Euc d → ℝ} (hς : ContDiff ℝ 1 ς) (hςc : HasCompactSupport ς) (hς0 : ∀ x, 0 ≤ ς x)
    (hz : Continuous z) :
    -(∫ x, (∑ i, D1 i (fun y => b y i) x) * ς x * z x ^ 2) ≤
      (d * Cb) * ∫ x, ς x * z x ^ 2 := by
  have hsum : ∀ x, -(∑ i, D1 i (fun y => b y i) x) ≤ d * Cb := by
    intro x
    have h1 : |∑ i, D1 i (fun y => b y i) x| ≤ d * Cb := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |D1 i (fun y => b y i) x| ≤ ∑ _i : Fin d, Cb :=
            Finset.sum_le_sum fun i _ => hdrift.d1 i x
        _ = d * Cb := by simp
    exact (neg_le_abs _).trans h1
  have hbc : ∀ i, Continuous (D1 i (fun y => b y i)) := fun i =>
    e3_continuous_D1 ((hdrift.smooth i).of_le (by norm_num)) i
  have iA : Integrable (fun x => (∑ i, D1 i (fun y => b y i) x) * ς x * z x ^ 2) volume :=
    e3_integrable_cs hςc
      (((continuous_finsetSum _ fun i _ => hbc i).mul hς.continuous).mul (hz.pow 2))
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have iB : Integrable (fun x => ς x * z x ^ 2) volume :=
    e3_integrable_cs hςc (hς.continuous.mul (hz.pow 2))
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  rw [← integral_neg, ← integral_const_mul]
  refine integral_mono iA.neg (iB.const_mul _) fun x => ?_
  have h0 : 0 ≤ ς x * z x ^ 2 := mul_nonneg (hς0 x) (sq_nonneg _)
  have := mul_le_mul_of_nonneg_right (hsum x) h0
  simp only
  linarith

theorem e3_rem_total_bound {b : Euc d → Euc d} {Cb K : ℝ} (hdrift : DriftFacts b Cb)
    (hCb : 0 ≤ Cb) {ε : ℝ} (hε : 0 < ε) {B : ℝ} {u : Euc d → ℝ}
    (hLM : LocMass B u) {ς : Euc d → ℝ} (hς1 : ContDiff ℝ 1 ς) (hς0 : ∀ x, 0 ≤ ς x)
    (hςle : ∀ x, ς x ≤ 1) (hK : ∀ x, ‖fderiv ℝ ς x‖ ≤ K) {S : Set (Euc d)} (hS : IsCompact S)
    (hSς : tsupport ς ⊆ S) {N₁ N₂ : ℝ}
    (hM : ∫ x in S, moll d ε (fun y => ‖u y‖) x ^ 2 ≤ N₁ * B ^ 2)
    (hA : ∫ x in S, moll d ε u x ^ 2 ≤ N₁ * B ^ 2)
    (hGr : ∫ x in S, ‖fderiv ℝ (moll d ε u) x‖ ^ 2 ≤ N₂ * B ^ 2) :
    |∑ i, ∫ x, u x * transRem d ε b (fun x => ς x * moll d ε u x) i x| ≤
      d * (ε * Cb * (B ^ 2 * ((3 / 2) * N₁ + K ^ 2 * N₁ + N₂))) := by
  have hzs : ContDiff ℝ ∞ (moll d ε u) := moll_contDiff hε hLM.locallyIntegrable
  have hz1 : ContDiff ℝ 1 (moll d ε u) := hzs.of_le (by norm_num)
  have hzcont2 : Continuous (fun x => moll d ε u x ^ 2) := hz1.continuous.pow 2
  have hgcont2 : Continuous (fun x => ‖fderiv ℝ (moll d ε u) x‖ ^ 2) :=
    ((hz1.continuous_fderiv (by simp)).norm).pow 2
  have hP1 : ContDiff ℝ 1 (fun x => ς x * moll d ε u x) := hς1.mul hz1
  have hPS : ∀ x, x ∉ S → ς x * moll d ε u x = 0 := fun x hx => by
    simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hSς h))]
  have hDPS : ∀ i x, x ∉ S → D1 i (fun y => ς y * moll d ε u y) x = 0 := by
    intro i x hx
    obtain ⟨h1, h2⟩ := e3_zero_off (fun h => hx (hSς h)) i
    rw [e3_D1_mul (hς1.differentiable (by simp)) (hz1.differentiable (by simp))]
    simp [h1, h2]
  have hPsq : ∫ x in S, (ς x * moll d ε u x) ^ 2 ≤ N₁ * B ^ 2 := by
    refine le_trans (setIntegral_mono_on
      ((hP1.continuous.pow 2).continuousOn.integrableOn_compact hS)
      (hzcont2.continuousOn.integrableOn_compact hS) hS.isClosed.measurableSet
      (fun x _ => ?_)) hA
    have : ς x ^ 2 ≤ 1 := pow_le_one₀ (hς0 x) (hςle x)
    have h2 := mul_le_mul_of_nonneg_right this (sq_nonneg (moll d ε u x))
    rw [mul_pow]
    linarith
  have hDPsq : ∀ i : Fin d, ∫ x in S, D1 i (fun y => ς y * moll d ε u y) x ^ 2 ≤
      2 * K ^ 2 * (N₁ * B ^ 2) + 2 * (N₂ * B ^ 2) := by
    intro i
    have hint : IntegrableOn (fun x => D1 i (fun y => ς y * moll d ε u y) x ^ 2) S volume :=
      ((e3_continuous_D1 hP1 i).pow 2).continuousOn.integrableOn_compact hS
    calc ∫ x in S, D1 i (fun y => ς y * moll d ε u y) x ^ 2
        ≤ ∫ x in S, (2 * K ^ 2 * moll d ε u x ^ 2 + 2 * ‖fderiv ℝ (moll d ε u) x‖ ^ 2) :=
          setIntegral_mono_on hint
            (((hzcont2.const_mul (2 * K ^ 2)).add (hgcont2.const_mul 2)).continuousOn.integrableOn_compact
              hS) hS.isClosed.measurableSet
            (fun x _ => e3_D1_prod_bound hς1 hz1 hK hς0 hςle i x)
      _ = 2 * K ^ 2 * (∫ x in S, moll d ε u x ^ 2) + 2 * ∫ x in S, ‖fderiv ℝ (moll d ε u) x‖ ^ 2 := by
          rw [integral_add ((hzcont2.const_mul (2 * K ^ 2)).continuousOn.integrableOn_compact hS)
            ((hgcont2.const_mul 2).continuousOn.integrableOn_compact hS),
            integral_const_mul, integral_const_mul]
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ 2 * K ^ 2)
          linarith
  have hεCb : 0 ≤ ε * Cb := mul_nonneg hε.le hCb
  have hRi : ∀ i : Fin d, |∫ x, u x * transRem d ε b (fun x => ς x * moll d ε u x) i x| ≤
      ε * Cb * (B ^ 2 * ((3 / 2) * N₁ + K ^ 2 * N₁ + N₂)) := by
    intro i
    refine (e3_rem_i_bound hdrift hCb hε hLM hP1 hS hPS i (hDPS i)).trans ?_
    set M := ∫ x in S, moll d ε (fun y => ‖u y‖) x ^ 2
    set A := ∫ x in S, (ς x * moll d ε u x) ^ 2
    set Dd := ∫ x in S, D1 i (fun y => ς y * moll d ε u y) x ^ 2
    have h2 := hDPsq i
    have h3 : (1 / 2) * M + (1 / 2) * A + ((1 / 2) * M + (1 / 2) * Dd) ≤
        B ^ 2 * ((3 / 2) * N₁ + K ^ 2 * N₁ + N₂) := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hεCb
    linarith
  calc _ ≤ ∑ i : Fin d, |∫ x, u x * transRem d ε b (fun x => ς x * moll d ε u x) i x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ε * Cb * (B ^ 2 * ((3 / 2) * N₁ + K ^ 2 * N₁ + N₂)) :=
        Finset.sum_le_sum fun i _ => hRi i
    _ = _ := by simp

theorem e3_arith_final {ν Γ Ncov E J I₁ Iς Ib Dv Rs dC Lr C1 fpD fpT : ℝ}
    (hν : 0 ≤ ν) (hΓ : 0 ≤ Γ) (hE : 0 ≤ E) (hdC : 0 ≤ dC)
    (hDiff : 2 * fpD ≤ -(ν * I₁) + ν * Γ * J)
    (hTr : 2 * (-fpT) + Ib = -Dv + 2 * Rs) (hDv : -Dv ≤ dC * Iς)
    (hJ : J ≤ Ncov * E) (hEz : Iς ≤ E) (hR : Rs ≤ Lr) (hC1a : Γ * Ncov ≤ C1) (hC1b : dC ≤ C1) :
    2 * (fpD - fpT) + Ib ≤ -(ν * I₁) + C1 * (ν + 1) * E + 2 * Lr := by
  have s1 : ν * Γ * J ≤ ν * Γ * (Ncov * E) := mul_le_mul_of_nonneg_left hJ (mul_nonneg hν hΓ)
  have s2 : (Γ * Ncov) * (ν * E) ≤ C1 * (ν * E) :=
    mul_le_mul_of_nonneg_right hC1a (mul_nonneg hν hE)
  have s3 : dC * Iς ≤ dC * E := mul_le_mul_of_nonneg_left hEz hdC
  have s4 : dC * E ≤ C1 * E := mul_le_mul_of_nonneg_right hC1b hE
  linarith

theorem e3_diffusion_transport {D : WholeDyn d} (hν : 0 ≤ D.invβ) {ρ : ℝ → Euc d → ℝ} {t : ℝ}
    (ht : 0 ≤ t) {m : ℕ} (hm : 1 ≤ m) {Cb K : ℝ} {χ χh : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d}
    (hχ : IsUlocCutoff χ)
    (hb : IsAdvectingDrift m Cb t (fun σ => meanFieldDriftW D (ρ (t - σ))))
    (hF : FlowBundle d m Cb t χ χh (fun σ => meanFieldDriftW D (ρ (t - σ))) Ψ K) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ (u : Euc d → ℝ) (B : ℝ), 0 ≤ B → ulocNormE 1 χ u ≤ ENNReal.ofReal B →
        ∀ σ ∈ Icc (0 : ℝ) t, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ c : Euc d,
          cellEnergy χ Ψ σ (moll d ε u) ≠ ⊤ ∧
          2 * (fpDiff D u (phiTest d χ Ψ σ c ε u) -
              fpTrans (meanFieldDriftW D (ρ (t - σ))) u (phiTest d χ Ψ σ c ε u)) +
            ∫ x, inner ℝ (meanFieldDriftW D (ρ (t - σ)) x) (gradient (varsigma χ Ψ σ c) x) *
              moll d ε u x ^ 2 ≤
          -(D.invβ * ∫ x, varsigma χ Ψ σ c x * ‖fderiv ℝ (moll d ε u) x‖ ^ 2) +
            C₁ * (D.invβ + 1) * (cellEnergy χ Ψ σ (moll d ε u)).toReal + C₂ * ε * B ^ 2 := by
  have hCb : 0 ≤ Cb := uc3_Cb_nonneg ht hb
  obtain ⟨Γ, hΓ0, hΓ⟩ := e3_varsigma_grad_sq hχ hF.flow hCb
  obtain ⟨Ncell, hNcell⟩ := e3_cellEnergy_le hF
  obtain ⟨N₁, hN₁⟩ := e3_moll_sq_set_le d (2 * Real.exp (Cb * t) + 1)
  obtain ⟨N₂, hN₂⟩ := e3_grad_sq_set_le d (2 * Real.exp (Cb * t) + 1)
  have hr0 : 0 ≤ 2 * Real.exp (Cb * t) := by positivity
  set Ncov : ℝ := (coverN d Cb t (2 * Real.exp (Cb * t)) : ℝ) with hNcov
  have hNcov0 : 0 ≤ Ncov := Nat.cast_nonneg _
  set Q : ℝ := (3 / 2) * N₁ + K ^ 2 * N₁ + N₂ with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨max (Γ * Ncov) (d * Cb), 2 * d * Cb * Q, ?_, by positivity, ?_⟩
  · exact (mul_nonneg hΓ0 hNcov0).trans (le_max_left _ _)
  intro u B hB hu σ hσ ε hε hε1 c
  have hLM : LocMass B u := locMass_of_ulocNormE (m := 1) hχ hB hu
  have hE : cellEnergy χ Ψ σ (moll d ε u) ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
    (hNcell ε hε hε1 B u hLM σ hσ)
  refine ⟨hE, ?_⟩
  have hdrift : DriftFacts (meanFieldDriftW D (ρ (t - σ))) Cb := driftFacts_of_advecting hm hb hσ
  have hς2 : ContDiff ℝ 2 (varsigma χ Ψ σ c) := hF.contDiff σ hσ c
  have hς1 : ContDiff ℝ 1 (varsigma χ Ψ σ c) := hς2.of_le (by norm_num)
  have hςc : HasCompactSupport (varsigma χ Ψ σ c) := hF.compact_supp σ hσ c
  have hς0 : ∀ x, 0 ≤ varsigma χ Ψ σ c x := fun x => (hF.range σ hσ c x).1
  have hςle : ∀ x, varsigma χ Ψ σ c x ≤ 1 := fun x => (hF.range σ hσ c x).2
  have hSς := hF.supp σ hσ c
  have hSc : IsCompact (closedBall (Ψ σ c) (2 * Real.exp (Cb * t))) := isCompact_closedBall _ _
  have hSball : closedBall (Ψ σ c) (2 * Real.exp (Cb * t)) ⊆
      ball (Ψ σ c) (2 * Real.exp (Cb * t) + 1) := closedBall_subset_ball (by linarith)
  have hzs : ContDiff ℝ ∞ (moll d ε u) := moll_contDiff hε hLM.locallyIntegrable
  have hz1 : ContDiff ℝ 1 (moll d ε u) := hzs.of_le (by norm_num)
  have hzc : Continuous (moll d ε u) := hz1.continuous
  rw [phiTest_eq_moll]
  have hinner : ∀ x, inner ℝ (meanFieldDriftW D (ρ (t - σ)) x) (gradient (varsigma χ Ψ σ c) x) =
      ∑ i, meanFieldDriftW D (ρ (t - σ)) x i * D1 i (varsigma χ Ψ σ c) x := fun x =>
    e3_inner_gradient _ _ _
  simp_rw [hinner]
  have hDiff := e3_diffusion_bound hν hε hLM hς2 hςc hς0 hΓ0 (hΓ σ hσ c) hSc hSς
  have hTr := e3_transport_identity hdrift.smooth hε hLM hς1 hςc
  have hJ := e3_ball_le_cellEnergy hF hσ hr0 hzc hE (Ψ σ c)
  have hEz := e3_integral_le_cellEnergy hF hσ hzc hE c
  have hEz0 : 0 ≤ (cellEnergy χ Ψ σ (moll d ε u)).toReal := ENNReal.toReal_nonneg
  have hDv := e3_div_term_bound hdrift hς1 hςc hς0 hzc
  have hG : LocMass B (fun y => ‖u y‖) :=
    ⟨hLM.1.norm, fun c' => by simpa only [enorm_norm] using hLM.2 c'⟩
  have hR := e3_rem_total_bound hdrift hCb hε hLM hς1 hς0 hςle
    (fun x => hF.fderiv_le σ hσ c x) hSc hSς
    (hN₁ ε hε hε1 B _ hG (Ψ σ c) _ hSball) (hN₁ ε hε hε1 B u hLM (Ψ σ c) _ hSball)
    (hN₂ hχ u B hB hu ε hε hε1 (Ψ σ c) _ hSball)
  have key := e3_arith_final hν hΓ0 hEz0 (mul_nonneg (Nat.cast_nonneg d) hCb) hDiff hTr hDv hJ hEz
    (le_abs_self _ |>.trans hR) (le_max_left _ _) (le_max_right _ _)
  have hconst : 2 * (d * (ε * Cb * (B ^ 2 * Q))) = 2 * d * Cb * Q * ε * B ^ 2 := by ring
  rw [hconst] at key
  exact key

end HRS.MS.UniqE3
