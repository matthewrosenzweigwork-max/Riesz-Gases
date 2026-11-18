import HRS.MS.Fp81S21RankKernel3
import HRS.MS.R2S11Aux4

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS.Whole
open HRS.MS.R26T3

private abbrev fp81s21_RankTailIndex {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) := ℝ≥0 × Σ n : ℕ, Particle R n

private def fp81s21_RankTailLaw {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (i : fp81s21_RankTailIndex R) (N : ℕ) :
    Measure (EucConfig p.d N) := by
  classical
  exact if h : N = i.2.1 then
    h.symm ▸ (i.2.2.P.map (i.2.2.X i.1))
  else HRS.Whole.modulatedGibbs (rieszKernel p.d p.s) N p.β
    (r26t3_mu R (i.1 : ℝ))

/-- Uniform raw and centered particle `L²` errors for the finite-rank velocity
approximants. The profile is selected before particle size, realization, time,
velocity, and approximation index. -/
theorem fp81s21_rankKernel_particle_sqerr (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ),
        ∀ Λ : ℝ, 0 ≤ Λ →
        ∀ D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d,
        ∀ B C : ℝ, 0 ≤ B → 0 ≤ C →
        IsR2UniformApprox p.s C B (HRS.Whole.withDensityReal R.ρβ)
          (fun θ => commutatorKernel p.d p.s θ.1)
          (fun θ k => (D θ k).kernel) →
        ∀ κ : ℕ → ℝ, (∀ k, 0 ≤ κ k) → Tendsto κ atTop (𝓝 0) →
        (∀ θ k u, 0 ≤ u →
          eLpNorm (fun xy : Euc p.d × Euc p.d =>
            (D θ k).kernel xy.1 xy.2 - commutatorKernel p.d p.s θ.1 xy.1 xy.2)
            2 ((r26t3_mu R u).prod (r26t3_mu R u)) ≤ ENNReal.ofReal (κ k)) →
        ∃ τN : ℕ → ℝ, (∀ k, 0 ≤ τN k) ∧ Tendsto τN atTop (𝓝 0) ∧
          ∀ k N, 2 ≤ N → ∀ A : Particle R N, ∀ u : ℝ, 0 ≤ u →
            ∀ θ : HRS.MS.R2S11.s11V p.d Λ,
              fp81s21_SqErr A.P
                (fun ω => (N : ℝ) * pairEnergy (D θ k).kernel
                  (A.X u.toNNReal ω) (r26t3_mu R u))
                (fun ω => (N : ℝ) * pairEnergy (commutatorKernel p.d p.s θ.1)
                  (A.X u.toNNReal ω) (r26t3_mu R u)) (τN k) ∧
              fp81s21_SqErr A.P (fp81s21_particleQuad A u (D θ k).kernel)
                (fp81s21_particleQuad A u (commutatorKernel p.d p.s θ.1)) (τN k) := by
  obtain ⟨δ0, hδ0, hδhalf, hUniform⟩ := fp81s21_uniform_density_moments p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R Λ hΛ D B C hB hC hApprox κ hκ hκConv hProduct
  obtain ⟨pinf, K, C₀, c₀, M, L, Mρ, Cm, hpinf, hc₀, hGaussian, hRound2,
    hMoment, hParticle⟩ := hUniform δ hδ hδle R
  let K' : ℝ := max K 1
  have hK1 : 1 ≤ K' := le_max_right _ _
  have hKle : K ≤ K' := le_max_left _ _
  obtain ⟨Bvel, -, -, hvelBound, -⟩ :=
    HRS.MS.R2S11.s11_velocity_uniform_approx p.hd p.hs0 p.hs p.ha p.hβ R.thermal Λ
  let Berr : ℝ := C * B + Bvel
  have hBvel : 0 ≤ Bvel := by
    let θ0 : HRS.MS.R2S11.s11V p.d Λ :=
      ⟨fun _ => 0, ⟨contDiff_const, by simp [cbNormVecE]⟩⟩
    have hdp : 0 < p.d := lt_of_lt_of_le (by decide : 0 < 2) p.hd
    letI : NeZero p.d := ⟨Nat.ne_of_gt hdp⟩
    letI : Nontrivial (Euc p.d) := inferInstance
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (Euc p.d)
    have hz : commutatorKernel p.d p.s θ0.1 x y = 0 := by simp [θ0, commutatorKernel]
    have hbnd := (hvelBound θ0).bound x y hxy
    rw [hz, abs_zero] at hbnd
    have hw : 0 < 1 + rieszWeight p.s (x - y) := by
      have := HRS.MS.R2S11.s11_rieszWeight_nonneg (d := p.d) p.s (x - y)
      linarith
    nlinarith
  have hBerr : 0 ≤ Berr := by dsimp [Berr]; positivity
  have hApproxBound : ∀ θ k,
      IsBoundedPairKernel p.s (C * B) ((D θ k).kernel) := by
    intro θ k
    refine ⟨?_, ?_, ?_⟩
    · change Measurable (Function.uncurry (r2FiniteRankKernel (D θ k).c (D θ k).u))
      exact HRS.MS.R2Mt.s92_finiteRank_meas (D θ k).valid
    · intro x y
      change r2FiniteRankKernel (D θ k).c (D θ k).u x y =
        r2FiniteRankKernel (D θ k).c (D θ k).u y x
      exact HRS.MS.R2Mt.s92_finiteRank_symm (D θ k).valid x y
    · intro x y hxy
      exact hApprox.envelope θ k x y hxy
  have hApproxBound' : ∀ θ k,
      IsBoundedPairKernel p.s Berr ((D θ k).kernel) := by
    intro θ k
    refine ⟨(hApproxBound θ k).measurable, (hApproxBound θ k).symm, ?_⟩
    intro x y hxy
    calc
      |(D θ k).kernel x y| ≤ (C * B) * (1 + rieszWeight p.s (x - y)) :=
        (hApproxBound θ k).bound x y hxy
      _ ≤ Berr * (1 + rieszWeight p.s (x - y)) := by
        exact mul_le_mul_of_nonneg_right
          (by dsimp [Berr]; exact le_add_of_nonneg_right hBvel)
          (by have := HRS.MS.R2S11.s11_rieszWeight_nonneg (d := p.d) p.s (x - y); linarith)
  have hCommBound' : ∀ θ : HRS.MS.R2S11.s11V p.d Λ,
      IsBoundedPairKernel p.s Berr (commutatorKernel p.d p.s θ.1) := by
    intro θ
    refine ⟨(hvelBound θ).measurable, (hvelBound θ).symm, ?_⟩
    intro x y hxy
    calc
      |commutatorKernel p.d p.s θ.1 x y| ≤ Bvel * (1 + rieszWeight p.s (x - y)) :=
        (hvelBound θ).bound x y hxy
      _ ≤ Berr * (1 + rieszWeight p.s (x - y)) := by
        exact mul_le_mul_of_nonneg_right
          (by dsimp [Berr]; exact le_add_of_nonneg_left (mul_nonneg hC hB))
          (by have := HRS.MS.R2S11.s11_rieszWeight_nonneg (d := p.d) p.s (x - y); linarith)
  let h : HRS.MS.R2S11.s11V p.d Λ → Euc p.d → Euc p.d → ℝ :=
    fun θ => commutatorKernel p.d p.s θ.1
  let hj : HRS.MS.R2S11.s11V p.d Λ → ℕ → Euc p.d → Euc p.d → ℝ :=
    fun θ k => (D θ k).kernel
  let ρ : fp81s21_RankTailIndex R → Euc p.d → ℝ := fun i => R.ρ (i.1 : ℝ)
  let Pfam : fp81s21_RankTailIndex R → ∀ N, Measure (EucConfig p.d N) :=
    fun i N => fp81s21_RankTailLaw R i N
  have hρ : ∀ i, IsRound2Density p.d p.s M L (ρ i) := by
    intro i
    exact hRound2 (i.1 : ℝ) i.1.property
  have hP : ∀ i N, 2 ≤ N →
      HasR2ActualDensity p.s p.β pinf K' (HRS.Whole.withDensityReal (ρ i)) (Pfam i N) := by
    intro i N hN
    by_cases hNsize : N = i.2.1
    · subst N
      have hAD := (hParticle i.2.1 hN i.2.2 (i.1 : ℝ) i.1.property).1
      have hAD' : HasR2ActualDensity p.s p.β pinf K
          (HRS.Whole.withDensityReal (ρ i)) (Pfam i i.2.1) := by
        simpa [Pfam, fp81s21_RankTailLaw, ρ, r26t3_mu] using hAD
      rcases hAD' with ⟨hprob, hdom, hratio⟩
      refine ⟨hprob, hdom, ?_⟩
      exact hratio.trans (ENNReal.ofReal_le_ofReal hKle)
    · let μ : Measure (Euc p.d) := r26t3_mu R (i.1 : ℝ)
      have hRound : IsRound2Density p.d p.s M L (ρ i) := hρ i
      haveI hμ : IsProbabilityMeasure μ := by
        change IsProbabilityMeasure (HRS.Whole.withDensityReal (ρ i))
        exact HRS.MS.R2Mt.s92_isProb_mu hRound.prob
      obtain ⟨Cnorm, hnorm0, hnorm⟩ := HRS.MS.R2Mt.s92_normalizer_bounds
        p.hd p.hs0 p.hs M L p.β (2 * p.β) p.hβ (by linarith [p.hβ])
      have hW := (hnorm (ρ i) hRound N hN p.β ⟨le_rfl, by linarith [p.hβ]⟩).1
      let Q : Measure (EucConfig p.d N) :=
        HRS.Whole.modulatedGibbs (rieszKernel p.d p.s) N p.β μ
      haveI hQ : IsProbabilityMeasure Q := by
        change IsProbabilityMeasure (HRS.Whole.modulatedGibbs (rieszKernel p.d p.s) N p.β μ)
        exact HRS.MS.R2Mt.s92_isProb_Q hW
      have hSelf := fp81s21_gibbs_actualDensity hQ rfl hpinf hK1
      have hPfam : Pfam i N = Q := by
        simp [Pfam, fp81s21_RankTailLaw, Q, μ, hNsize]
      rw [hPfam]
      exact hSelf
  have hErrKernel : ∀ θ k,
      IsBoundedPairKernel p.s Berr (fun x y => hj θ k x y - h θ x y) := by
    intro θ k
    refine ⟨?_, ?_, ?_⟩
    · exact (hApproxBound θ k).measurable.sub (hvelBound θ).measurable
    · intro x y
      change (D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y =
        (D θ k).kernel y x - commutatorKernel p.d p.s θ.1 y x
      rw [(hApproxBound θ k).symm x y, (hvelBound θ).symm x y]
    · intro x y hxy
      calc
        |hj θ k x y - h θ x y| ≤ |hj θ k x y| + |h θ x y| := abs_sub _ _
        _ ≤ (C * B) * (1 + rieszWeight p.s (x - y)) +
              Bvel * (1 + rieszWeight p.s (x - y)) :=
          add_le_add ((hApproxBound θ k).bound x y hxy)
            ((hvelBound θ).bound x y hxy)
        _ = Berr * (1 + rieszWeight p.s (x - y)) := by dsimp [Berr]; ring
  obtain ⟨CF, hCF0, hCF⟩ := HRS.MS.R2Mt.s92_F_bound p.hd p.hs0 p.hs M L
    p.β pinf K' Berr 2 p.hβ hpinf (by norm_num)
  let τe : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (κ k) ^ 2
  have hτe : Tendsto τe atTop (𝓝 0) := by
    have h₁ : Tendsto (fun k => ENNReal.ofReal (κ k)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hκConv
    have hpow := ((ENNReal.continuous_pow 2).tendsto (0 : ℝ≥0∞)).comp h₁
    have hpow0 : Tendsto
        ((fun a : ℝ≥0∞ => a ^ 2) ∘ (fun k => ENNReal.ofReal (κ k))) atTop (𝓝 0) := by
      simpa using hpow
    have hτeq : τe =
        ((fun a : ℝ≥0∞ => a ^ 2) ∘ (fun k => ENNReal.ofReal (κ k))) := by
      funext k
      rfl
    rw [hτeq]
    exact hpow0
  have hτeb : ∀ θ i k,
      (eLpNorm (fun xy : Euc p.d × Euc p.d => hj θ k xy.1 xy.2 - h θ xy.1 xy.2)
        (ENNReal.ofReal 2)
        ((HRS.Whole.withDensityReal (ρ i)).prod (HRS.Whole.withDensityReal (ρ i)))) ^ 2 ≤ τe k := by
    intro θ i k
    have hpr := hProduct θ k (i.1 : ℝ) i.1.property
    have hpr' : eLpNorm (fun xy : Euc p.d × Euc p.d =>
        hj θ k xy.1 xy.2 - h θ xy.1 xy.2) (ENNReal.ofReal 2)
        ((HRS.Whole.withDensityReal (ρ i)).prod (HRS.Whole.withDensityReal (ρ i))) ≤
        ENNReal.ofReal (κ k) := by
      simpa [h, hj, ρ, r26t3_mu] using hpr
    dsimp [τe]
    exact pow_le_pow_left' hpr' 2
  have hTail := HRS.MS.R2S11.s11_tailFam (d := p.d) p.hd p.hs0 p.hs
    M L p.β pinf K' Berr 2 0 p.hβ hpinf (by norm_num)
    (ρ := ρ) hρ (P := Pfam) hP (h := h) (hj := hj)
    (fun θ k => by simpa using hErrKernel θ k) hτe hτeb
  let tailRaw : ℕ → ℝ≥0∞ := fun k =>
    ⨆ θ : HRS.MS.R2S11.s11V p.d Λ, ⨆ i : fp81s21_RankTailIndex R,
      ⨆ n : {n : ℕ // 2 ≤ n},
        eLpNorm (fun X => (n.1 : ℝ) * pairEnergy
          (fun x y => hj θ k x y - h θ x y) X (HRS.Whole.withDensityReal (ρ i)))
          (ENNReal.ofReal 2) (Pfam i n.1)
  let tailCenter : ℕ → ℝ≥0∞ := fun k =>
    ⨆ θ : HRS.MS.R2S11.s11V p.d Λ, ⨆ i : fp81s21_RankTailIndex R,
      ⨆ n : {n : ℕ // 2 ≤ n},
        eLpNorm (fun X => (n.1 : ℝ) *
          (pairEnergy (fun x y => hj θ k x y - h θ x y) X (HRS.Whole.withDensityReal (ρ i)) -
            ∫ Y, pairEnergy (fun x y => hj θ k x y - h θ x y) Y
              (HRS.Whole.withDensityReal (ρ i)) ∂(Pfam i n.1)))
          (ENNReal.ofReal 2) (Pfam i n.1)
  have hTailRawConv : Tendsto tailRaw atTop (𝓝 0) := by
    simpa [tailRaw, h, hj] using hTail.1
  have hTailCenterConv : Tendsto tailCenter atTop (𝓝 0) := by
    simpa [tailCenter, h, hj] using hTail.2
  have hTailRawBound : ∀ k, tailRaw k ≤ ENNReal.ofReal CF := by
    intro k
    dsimp [tailRaw]
    refine iSup_le fun θ => iSup_le fun i => iSup_le fun n => ?_
    exact (hCF (ρ i) (hρ i) (fun x y => hj θ k x y - h θ x y)
      (hErrKernel θ k) n.1 n.2 (Pfam i n.1) (hP i n.1 n.2)).1
  have hTailCenterBound : ∀ k, tailCenter k ≤ ENNReal.ofReal CF := by
    intro k
    dsimp [tailCenter]
    refine iSup_le fun θ => iSup_le fun i => iSup_le fun n => ?_
    exact (hCF (ρ i) (hρ i) (fun x y => hj θ k x y - h θ x y)
      (hErrKernel θ k) n.1 n.2 (Pfam i n.1) (hP i n.1 n.2)).2
  have hTailRawFinite : ∀ k, tailRaw k ≠ ⊤ := by
    intro k
    exact ne_of_lt (lt_of_le_of_lt (hTailRawBound k) ENNReal.ofReal_lt_top)
  have hTailCenterFinite : ∀ k, tailCenter k ≠ ⊤ := by
    intro k
    exact ne_of_lt (lt_of_le_of_lt (hTailCenterBound k) ENNReal.ofReal_lt_top)
  let rawReal : ℕ → ℝ := fun k => (tailRaw k).toReal
  let centerReal : ℕ → ℝ := fun k => (tailCenter k).toReal
  have hRawRealConv : Tendsto rawReal atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hTailRawConv
    change Tendsto (fun k => (tailRaw k).toReal) atTop (𝓝 0)
    exact h
  have hCenterRealConv : Tendsto centerReal atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hTailCenterConv
    change Tendsto (fun k => (tailCenter k).toReal) atTop (𝓝 0)
    exact h
  let τN : ℕ → ℝ := fun k => rawReal k + centerReal k
  have hτNnonneg : ∀ k, 0 ≤ τN k := by
    intro k
    dsimp [τN, rawReal, centerReal]
    exact add_nonneg (ENNReal.toReal_nonneg) (ENNReal.toReal_nonneg)
  have hτNconv : Tendsto τN atTop (𝓝 0) := by
    simpa [τN] using hRawRealConv.add hCenterRealConv
  refine ⟨τN, hτNnonneg, hτNconv, ?_⟩
  intro k N hN A u hu θ
  let idx : fp81s21_RankTailIndex R := ⟨u.toNNReal, ⟨N, A⟩⟩
  let nidx : {n : ℕ // 2 ≤ n} := ⟨N, hN⟩
  let μu : Measure (Euc p.d) := HRS.Whole.withDensityReal (R.ρ u)
  let Pcfg : Measure (EucConfig p.d N) := A.P.map (A.X u.toNNReal)
  have hρu : HRS.Whole.IsRound2Density p.d p.s M L (R.ρ u) := hRound2 u hu
  haveI hμu : IsProbabilityMeasure μu := HRS.MS.R2Mt.s92_isProb_mu hρu.prob
  have hXsol := A.strong (u + 1)
  have htime : (u.toNNReal : ℝ) ≤ u + 1 := by
    rw [Real.coe_toNNReal _ hu]
    linarith
  have hX : Measurable (A.X u.toNNReal) := hXsol.adapted u.toNNReal
  have hPcfgEq : Pfam idx N = Pcfg := by
    simp [Pfam, idx, fp81s21_RankTailLaw, Pcfg]
  have hμidx : μu = HRS.Whole.withDensityReal (ρ idx) := by
    simp [μu, ρ, idx, Real.coe_toNNReal _ hu]
  have hApproxBoundμ : Measurable (fun q : Euc p.d × Euc p.d =>
      (D θ k).kernel q.1 q.2) := (hApproxBound θ k).measurable
  have hCommBoundμ : Measurable (fun q : Euc p.d × Euc p.d =>
      commutatorKernel p.d p.s θ.1 q.1 q.2) := (hvelBound θ).measurable
  have hErrBoundμ : Measurable (fun q : Euc p.d × Euc p.d =>
      (D θ k).kernel q.1 q.2 - commutatorKernel p.d p.s θ.1 q.1 q.2) :=
    (hErrKernel θ k).measurable
  have hApproxRow := HRS.MS.R2Chaos.s94_rowOKE p.hd p.hs0 p.hs
    (hρ := hρu) (hh := hApproxBound' θ k)
  have hCommRow := HRS.MS.R2Chaos.s94_rowOKE p.hd p.hs0 p.hs
    (hρ := hρu) (hh := hCommBound' θ)
  have hErrRow := HRS.MS.R2Chaos.s94_rowOKE p.hd p.hs0 p.hs
    (hρ := hρu) (hh := hErrKernel θ k)
  have hPairApprox : Measurable (fun X : EucConfig p.d N =>
      pairEnergy (D θ k).kernel X μu) :=
    HRS.MS.R2Chaos.s94_pE_meas_config (N := N) (μ := μu) hApproxBoundμ
  have hPairComm : Measurable (fun X : EucConfig p.d N =>
      pairEnergy (commutatorKernel p.d p.s θ.1) X μu) :=
    HRS.MS.R2Chaos.s94_pE_meas_config (N := N) (μ := μu) hCommBoundμ
  have hPairErr : Measurable (fun X : EucConfig p.d N =>
      pairEnergy (fun x y => (D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y) X μu) :=
    HRS.MS.R2Chaos.s94_pE_meas_config (N := N) (μ := μu) hErrBoundμ
  let rawApprox : EucConfig p.d N → ℝ := fun X =>
    (N : ℝ) * pairEnergy (D θ k).kernel X μu
  let rawComm : EucConfig p.d N → ℝ := fun X =>
    (N : ℝ) * pairEnergy (commutatorKernel p.d p.s θ.1) X μu
  let rawErr : EucConfig p.d N → ℝ := fun X =>
    (N : ℝ) * pairEnergy
      (fun x y => (D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y) X μu
  have hRawSub : ∀ X, rawApprox X - rawComm X = rawErr X := by
    intro X
    dsimp [rawApprox, rawComm, rawErr]
    rw [HRS.MS.Wr.pairEnergy_sub hApproxRow hCommRow X]
    ring
  have hRawApproxMeas : Measurable rawApprox := by
    exact measurable_const.mul hPairApprox
  have hRawCommMeas : Measurable rawComm := by
    exact measurable_const.mul hPairComm
  have hRawErrMeas : Measurable rawErr := by
    exact measurable_const.mul hPairErr
  have hRawDiffMeas : Measurable (fun ω =>
      (N : ℝ) * pairEnergy (D θ k).kernel (A.X u.toNNReal ω) μu -
        (N : ℝ) * pairEnergy (commutatorKernel p.d p.s θ.1) (A.X u.toNNReal ω) μu) := by
    exact (hRawApproxMeas.sub hRawCommMeas).comp hX
  have hActualK : HasR2ActualDensity p.s p.β pinf K μu Pcfg := by
    change HasR2ActualDensity p.s p.β pinf K
      (HRS.Whole.withDensityReal (R.ρ u)) (A.P.map (A.X u.toNNReal))
    simpa [r26t3_mu] using (hParticle N hN A u hu).1
  rcases hActualK with ⟨hActualProb, hActualAC, hActualRatio⟩
  have hActualK' : HasR2ActualDensity p.s p.β pinf K' μu Pcfg :=
    ⟨hActualProb, hActualAC, hActualRatio.trans (ENNReal.ofReal_le_ofReal hKle)⟩
  have hApproxMom := hCF (R.ρ u) hρu (D θ k).kernel (hApproxBound' θ k)
    N hN Pcfg hActualK'
  have hCommMom := hCF (R.ρ u) hρu (commutatorKernel p.d p.s θ.1)
    (hCommBound' θ) N hN Pcfg hActualK'
  have hApproxMap : eLpNorm (fun ω => rawApprox (A.X u.toNNReal ω))
      (ENNReal.ofReal 2) A.P = eLpNorm rawApprox (ENNReal.ofReal 2) Pcfg := by
    rw [eLpNorm_map_measure hRawApproxMeas.aestronglyMeasurable hX.aemeasurable]
    rfl
  have hCommMap : eLpNorm (fun ω => rawComm (A.X u.toNNReal ω))
      (ENNReal.ofReal 2) A.P = eLpNorm rawComm (ENNReal.ofReal 2) Pcfg := by
    rw [eLpNorm_map_measure hRawCommMeas.aestronglyMeasurable hX.aemeasurable]
    rfl
  have hApproxMem : MemLp (fun ω => rawApprox (A.X u.toNNReal ω)) 2 A.P := by
    apply memLp_iff.2
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, hApproxMap]
    exact lt_of_le_of_lt hApproxMom.1 ENNReal.ofReal_lt_top
  have hCommMem : MemLp (fun ω => rawComm (A.X u.toNNReal ω)) 2 A.P := by
    apply memLp_iff.2
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, hCommMap]
    exact lt_of_le_of_lt hCommMom.1 ENNReal.ofReal_lt_top
  have hApproxInt : Integrable (fun ω => rawApprox (A.X u.toNNReal ω)) A.P :=
    hApproxMem.integrable (by norm_num)
  have hCommInt : Integrable (fun ω => rawComm (A.X u.toNNReal ω)) A.P :=
    hCommMem.integrable (by norm_num)
  have hMeanErr : (∫ ω, rawApprox (A.X u.toNNReal ω) ∂A.P) -
      (∫ ω, rawComm (A.X u.toNNReal ω) ∂A.P) =
      (N : ℝ) * ∫ X, pairEnergy
        (fun x y => (D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y) X μu ∂Pcfg := by
    rw [← integral_sub hApproxInt hCommInt]
    calc
      ∫ ω, rawApprox (A.X u.toNNReal ω) - rawComm (A.X u.toNNReal ω) ∂A.P =
          ∫ ω, rawErr (A.X u.toNNReal ω) ∂A.P := by
            apply integral_congr_ae
            filter_upwards [] with ω
            exact hRawSub (A.X u.toNNReal ω)
      _ = (N : ℝ) * ∫ X, pairEnergy
          (fun x y => (D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y) X μu ∂Pcfg := by
        dsimp [rawErr]
        rw [integral_const_mul,
          integral_map hX.aemeasurable hPairErr.aestronglyMeasurable]
  have hCenteredPoint : ∀ ω,
      fp81s21_particleQuad A u (D θ k).kernel ω -
        fp81s21_particleQuad A u (commutatorKernel p.d p.s θ.1) ω =
      (N : ℝ) * (pairEnergy
          (fun x y => (D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y)
          (A.X u.toNNReal ω) μu -
        ∫ X, pairEnergy
          (fun x y => (D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y)
          X μu ∂Pcfg) := by
    intro ω
    change rawApprox (A.X u.toNNReal ω) -
        ∫ ω', rawApprox (A.X u.toNNReal ω') ∂A.P -
      (rawComm (A.X u.toNNReal ω) -
        ∫ ω', rawComm (A.X u.toNNReal ω') ∂A.P) = _
    linear_combination hRawSub (A.X u.toNNReal ω) - hMeanErr
  have hCenteredMeas : Measurable (fun ω =>
      fp81s21_particleQuad A u (D θ k).kernel ω -
        fp81s21_particleQuad A u (commutatorKernel p.d p.s θ.1) ω) := by
    have hEq : (fun ω => fp81s21_particleQuad A u (D θ k).kernel ω -
        fp81s21_particleQuad A u (commutatorKernel p.d p.s θ.1) ω) =
        fun ω => (N : ℝ) * (pairEnergy
          (fun x y => (D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y)
          (A.X u.toNNReal ω) μu -
          ∫ X, pairEnergy
            (fun x y => (D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y)
            X μu ∂Pcfg) := funext hCenteredPoint
    rw [hEq]
    exact (measurable_const.mul (hPairErr.sub_const _)).comp hX
  have hRawAtTail : eLpNorm (fun X => rawErr X) (ENNReal.ofReal 2) Pcfg ≤ tailRaw k := by
    have hRawFun : rawErr = fun X => (N : ℝ) * pairEnergy
        (fun x y => hj θ k x y - h θ x y) X (HRS.Whole.withDensityReal (ρ idx)) := by
      funext X
      simp [rawErr, h, hj, hμidx]
    rw [hRawFun, ← hPcfgEq]
    calc
      eLpNorm (fun X => (N : ℝ) * pairEnergy
          (fun x y => hj θ k x y - h θ x y) X (HRS.Whole.withDensityReal (ρ idx)))
          (ENNReal.ofReal 2) (Pfam idx N) ≤
          ⨆ n' : {n : ℕ // 2 ≤ n}, eLpNorm
            (fun X => (n'.1 : ℝ) * pairEnergy
              (fun x y => hj θ k x y - h θ x y) X (HRS.Whole.withDensityReal (ρ idx)))
            (ENNReal.ofReal 2) (Pfam idx n'.1) := by
              simpa [nidx] using le_iSup (fun n' : {n : ℕ // 2 ≤ n} =>
                eLpNorm (fun X => (n'.1 : ℝ) * pairEnergy
                  (fun x y => hj θ k x y - h θ x y) X
                  (HRS.Whole.withDensityReal (ρ idx)))
                  (ENNReal.ofReal 2) (Pfam idx n'.1)) nidx
      _ ≤ ⨆ i' : fp81s21_RankTailIndex R, ⨆ n' : {n : ℕ // 2 ≤ n},
          eLpNorm (fun X => (n'.1 : ℝ) * pairEnergy
            (fun x y => hj θ k x y - h θ x y) X (HRS.Whole.withDensityReal (ρ i')))
            (ENNReal.ofReal 2) (Pfam i' n'.1) := by
        exact le_iSup (fun i' : fp81s21_RankTailIndex R => ⨆ n' : {n : ℕ // 2 ≤ n},
          eLpNorm (fun X => (n'.1 : ℝ) * pairEnergy
            (fun x y => hj θ k x y - h θ x y) X (HRS.Whole.withDensityReal (ρ i')))
            (ENNReal.ofReal 2) (Pfam i' n'.1)) idx
      _ ≤ tailRaw k := by
        change _ ≤ ⨆ θ' : HRS.MS.R2S11.s11V p.d Λ,
          ⨆ i' : fp81s21_RankTailIndex R, ⨆ n' : {n : ℕ // 2 ≤ n},
            eLpNorm (fun X => (n'.1 : ℝ) * pairEnergy
              (fun x y => hj θ' k x y - h θ' x y)
              X (HRS.Whole.withDensityReal (ρ i')))
              (ENNReal.ofReal 2) (Pfam i' n'.1)
        exact le_iSup (fun θ' : HRS.MS.R2S11.s11V p.d Λ =>
          ⨆ i' : fp81s21_RankTailIndex R, ⨆ n' : {n : ℕ // 2 ≤ n},
            eLpNorm (fun X => (n'.1 : ℝ) * pairEnergy
              (fun x y => hj θ' k x y - h θ' x y)
              X (HRS.Whole.withDensityReal (ρ i')))
              (ENNReal.ofReal 2) (Pfam i' n'.1)) θ
  have hCenterFun : (fun X : EucConfig p.d N => (N : ℝ) *
      (pairEnergy (fun x y => (D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y)
          X μu -
        ∫ Y, pairEnergy
          (fun x y => (D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y)
          Y μu ∂Pcfg)) =
      (fun X : EucConfig p.d N => (N : ℝ) *
      (pairEnergy (fun x y => hj θ k x y - h θ x y) X
          (HRS.Whole.withDensityReal (ρ idx)) -
        ∫ Y, pairEnergy (fun x y => hj θ k x y - h θ x y) Y
          (HRS.Whole.withDensityReal (ρ idx)) ∂(Pfam idx N))) := by
    funext X
    rw [← hPcfgEq]
    simp [h, hj, hμidx]
  have hCenterAtTail : eLpNorm (fun X => (N : ℝ) *
      (pairEnergy (fun x y => (D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y) X μu -
        ∫ Y, pairEnergy (fun x y => (D θ k).kernel x y -
          commutatorKernel p.d p.s θ.1 x y) Y μu ∂Pcfg))
      (ENNReal.ofReal 2) Pcfg ≤ tailCenter k := by
    rw [hCenterFun, ← hPcfgEq]
    calc
      eLpNorm (fun X => (N : ℝ) *
          (pairEnergy (fun x y => hj θ k x y - h θ x y) X
              (HRS.Whole.withDensityReal (ρ idx)) -
            ∫ Y, pairEnergy (fun x y => hj θ k x y - h θ x y) Y
              (HRS.Whole.withDensityReal (ρ idx)) ∂(Pfam idx N)))
          (ENNReal.ofReal 2) (Pfam idx N) ≤
        ⨆ n' : {n : ℕ // 2 ≤ n}, eLpNorm
          (fun X => (n'.1 : ℝ) *
            (pairEnergy (fun x y => hj θ k x y - h θ x y) X
                (HRS.Whole.withDensityReal (ρ idx)) -
              ∫ Y, pairEnergy (fun x y => hj θ k x y - h θ x y) Y
                (HRS.Whole.withDensityReal (ρ idx)) ∂(Pfam idx n'.1)))
          (ENNReal.ofReal 2) (Pfam idx n'.1) := by
            simpa [nidx] using le_iSup (fun n' : {n : ℕ // 2 ≤ n} =>
              eLpNorm (fun X => (n'.1 : ℝ) *
                (pairEnergy (fun x y => hj θ k x y - h θ x y) X
                    (HRS.Whole.withDensityReal (ρ idx)) -
                  ∫ Y, pairEnergy (fun x y => hj θ k x y - h θ x y) Y
                    (HRS.Whole.withDensityReal (ρ idx)) ∂(Pfam idx n'.1)))
                (ENNReal.ofReal 2) (Pfam idx n'.1)) nidx
      _ ≤ ⨆ i' : fp81s21_RankTailIndex R, ⨆ n' : {n : ℕ // 2 ≤ n},
          eLpNorm (fun X => (n'.1 : ℝ) *
            (pairEnergy (fun x y => hj θ k x y - h θ x y) X
                (HRS.Whole.withDensityReal (ρ i')) -
              ∫ Y, pairEnergy (fun x y => hj θ k x y - h θ x y) Y
                (HRS.Whole.withDensityReal (ρ i')) ∂(Pfam i' n'.1)))
            (ENNReal.ofReal 2) (Pfam i' n'.1) := by
        exact le_iSup (fun i' : fp81s21_RankTailIndex R => ⨆ n' : {n : ℕ // 2 ≤ n},
          eLpNorm (fun X => (n'.1 : ℝ) *
            (pairEnergy (fun x y => hj θ k x y - h θ x y) X
                (HRS.Whole.withDensityReal (ρ i')) -
              ∫ Y, pairEnergy (fun x y => hj θ k x y - h θ x y) Y
                (HRS.Whole.withDensityReal (ρ i')) ∂(Pfam i' n'.1)))
            (ENNReal.ofReal 2) (Pfam i' n'.1)) idx
      _ ≤ tailCenter k := by
        change _ ≤ ⨆ θ' : HRS.MS.R2S11.s11V p.d Λ,
          ⨆ i' : fp81s21_RankTailIndex R, ⨆ n' : {n : ℕ // 2 ≤ n},
            eLpNorm (fun X => (n'.1 : ℝ) *
              (pairEnergy (fun x y => hj θ' k x y - h θ' x y) X
                  (HRS.Whole.withDensityReal (ρ i')) -
                ∫ Y, pairEnergy (fun x y => hj θ' k x y - h θ' x y) Y
                  (HRS.Whole.withDensityReal (ρ i')) ∂(Pfam i' n'.1)))
              (ENNReal.ofReal 2) (Pfam i' n'.1)
        exact le_iSup (fun θ' : HRS.MS.R2S11.s11V p.d Λ =>
          ⨆ i' : fp81s21_RankTailIndex R, ⨆ n' : {n : ℕ // 2 ≤ n},
            eLpNorm (fun X => (n'.1 : ℝ) *
              (pairEnergy (fun x y => hj θ' k x y - h θ' x y) X
                  (HRS.Whole.withDensityReal (ρ i')) -
                ∫ Y, pairEnergy (fun x y => hj θ' k x y - h θ' x y) Y
                  (HRS.Whole.withDensityReal (ρ i')) ∂(Pfam i' n'.1)))
              (ENNReal.ofReal 2) (Pfam i' n'.1)) θ
  have hRawΩMap : eLpNorm (fun ω => rawErr (A.X u.toNNReal ω))
      (ENNReal.ofReal 2) A.P = eLpNorm rawErr (ENNReal.ofReal 2) Pcfg := by
    rw [eLpNorm_map_measure hRawErrMeas.aestronglyMeasurable hX.aemeasurable]
    rfl
  have hRawL2 : eLpNorm (fun ω =>
      (N : ℝ) * pairEnergy (D θ k).kernel (A.X u.toNNReal ω) μu -
        (N : ℝ) * pairEnergy (commutatorKernel p.d p.s θ.1)
          (A.X u.toNNReal ω) μu) (ENNReal.ofReal 2) A.P ≤ ENNReal.ofReal (τN k) := by
    rw [show (fun ω =>
      (N : ℝ) * pairEnergy (D θ k).kernel (A.X u.toNNReal ω) μu -
        (N : ℝ) * pairEnergy (commutatorKernel p.d p.s θ.1)
          (A.X u.toNNReal ω) μu) = fun ω => rawErr (A.X u.toNNReal ω) from by
            funext ω; exact hRawSub (A.X u.toNNReal ω)]
    rw [hRawΩMap]
    calc
      eLpNorm rawErr (ENNReal.ofReal 2) Pcfg ≤ tailRaw k := hRawAtTail
      _ = ENNReal.ofReal (rawReal k) := (ENNReal.ofReal_toReal (hTailRawFinite k)).symm
      _ ≤ ENNReal.ofReal (τN k) := ENNReal.ofReal_le_ofReal (by
        dsimp [τN, rawReal]
        exact le_add_of_nonneg_right (ENNReal.toReal_nonneg))
  have hRawSq := fp81s21_SqErr_of_eLpNorm_sub A.P
    (fun ω => (N : ℝ) * pairEnergy (D θ k).kernel (A.X u.toNNReal ω) μu)
    (fun ω => (N : ℝ) * pairEnergy (commutatorKernel p.d p.s θ.1)
      (A.X u.toNNReal ω) μu) (τN k) (hτNnonneg k) hRawDiffMeas (by simpa using hRawL2)
  have hCenterMeasCfg : Measurable (fun X : EucConfig p.d N => (N : ℝ) *
      (pairEnergy (fun x y => (D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y) X μu -
        ∫ Y, pairEnergy (fun x y => (D θ k).kernel x y -
          commutatorKernel p.d p.s θ.1 x y) Y μu ∂Pcfg)) := by
    exact measurable_const.mul (hPairErr.sub_const _)
  have hCenterΩMap : eLpNorm (fun ω =>
      fp81s21_particleQuad A u (D θ k).kernel ω -
        fp81s21_particleQuad A u (commutatorKernel p.d p.s θ.1) ω)
      (ENNReal.ofReal 2) A.P =
      eLpNorm (fun X => (N : ℝ) *
        (pairEnergy (fun x y => (D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y) X μu -
          ∫ Y, pairEnergy (fun x y => (D θ k).kernel x y -
            commutatorKernel p.d p.s θ.1 x y) Y μu ∂Pcfg))
        (ENNReal.ofReal 2) Pcfg := by
    rw [show (fun ω =>
      fp81s21_particleQuad A u (D θ k).kernel ω -
        fp81s21_particleQuad A u (commutatorKernel p.d p.s θ.1) ω) =
        fun ω => (fun X => (N : ℝ) *
          (pairEnergy (fun x y => (D θ k).kernel x y - commutatorKernel p.d p.s θ.1 x y) X μu -
            ∫ Y, pairEnergy (fun x y => (D θ k).kernel x y -
              commutatorKernel p.d p.s θ.1 x y) Y μu ∂Pcfg)) (A.X u.toNNReal ω) from by
          funext ω
          exact hCenteredPoint ω]
    rw [eLpNorm_map_measure hCenterMeasCfg.aestronglyMeasurable hX.aemeasurable]
    rfl
  have hCenterL2 : eLpNorm (fun ω =>
      fp81s21_particleQuad A u (D θ k).kernel ω -
        fp81s21_particleQuad A u (commutatorKernel p.d p.s θ.1) ω)
      (ENNReal.ofReal 2) A.P ≤ ENNReal.ofReal (τN k) := by
    rw [hCenterΩMap]
    calc
      _ ≤ tailCenter k := hCenterAtTail
      _ = ENNReal.ofReal (centerReal k) :=
        (ENNReal.ofReal_toReal (hTailCenterFinite k)).symm
      _ ≤ ENNReal.ofReal (τN k) := ENNReal.ofReal_le_ofReal (by
        dsimp [τN, centerReal]
        exact le_add_of_nonneg_left (ENNReal.toReal_nonneg))
  have hCenterSq := fp81s21_SqErr_of_eLpNorm_sub A.P
    (fp81s21_particleQuad A u (D θ k).kernel)
    (fp81s21_particleQuad A u (commutatorKernel p.d p.s θ.1))
    (τN k) (hτNnonneg k) hCenteredMeas (by simpa using hCenterL2)
  exact ⟨hRawSq, hCenterSq⟩

#print axioms fp81s21_rankKernel_particle_sqerr

end HRS.Fp81.S21
