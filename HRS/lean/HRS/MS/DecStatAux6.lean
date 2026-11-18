import HRS.MS.DecStatAux5

/-!
# SA4, packet 6: the per-`N` smooth-metric bound with the rate `rdRate ... e`

`sa4_arith_smooth`, `sa4_arith_wass`: the real arithmetic with the additive error; `sa4_smooth_core`, `sa4_smooth_rate`: copies of
`sa2_smooth_core`, `sa2_smooth_rate` with the remainder bound `Sa4Rem` and the test/`Y_0` data `Sa4Test`, `Sa4Y0`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas HRS.MS.MainRdStat
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.DecStat

variable {d : ℕ}

section Arith

/-- the real arithmetic of the smooth rate (with the additive error `Cs e`) -/
theorem sa4_arith_smooth {Bs c0 Cs e Cy Ct dd T ε q σ E w Ccov : ℝ} (hBs : 0 ≤ Bs) (hc0 : 0 ≤ c0) (hCs : 0 ≤ Cs)
    (he : 0 ≤ e) (hCy : 0 ≤ Cy) (hCt : 0 ≤ Ct) (hdd : 0 ≤ dd) (hT : 0 ≤ T) (hε : 0 ≤ ε) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hσ : 0 ≤ σ) (hE : 0 ≤ E) (hw : 0 ≤ w)
    (hC1 : ε + Real.sqrt q * Real.sqrt w + σ * (E + e) < 1 → Ccov ≤ 2 * q * Ct * Bs ^ 2 * T * w)
    (hC2 : 1 ≤ ε + Real.sqrt q * Real.sqrt w + σ * (E + e) → Ccov ≤ 4 * q * dd * T * Bs ^ 2) :
    σ * c0 * Bs * ((E + Cs * e) * T) + ε * (Cy * Bs) + 1 / 2 * Ccov ≤
      (c0 * T * (1 + Cs) + Cy + Ct * T + 2 * dd * T) * (Bs + Bs ^ 2) *
        (ε + Real.sqrt q * Real.sqrt w + σ * (E + e)) := by
  set r : ℝ := ε + Real.sqrt q * Real.sqrt w + σ * (E + e) with hr
  have hsq : 0 ≤ Real.sqrt q * Real.sqrt w := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hσE : 0 ≤ σ * E := by positivity
  have hσe : 0 ≤ σ * e := by positivity
  have hr0 : 0 ≤ r := by rw [hr]; nlinarith
  have hσEr : σ * E ≤ r := by rw [hr]; nlinarith
  have hσer : σ * e ≤ r := by rw [hr]; nlinarith
  have hεr : ε ≤ r := by rw [hr]; nlinarith
  have hB2 : 0 ≤ Bs ^ 2 := sq_nonneg _
  have h1 : σ * c0 * Bs * ((E + Cs * e) * T) ≤ c0 * T * Bs * r + c0 * Cs * T * Bs * r := by
    calc σ * c0 * Bs * ((E + Cs * e) * T) = (c0 * T * Bs) * (σ * E) + (c0 * Cs * T * Bs) * (σ * e) := by ring
      _ ≤ (c0 * T * Bs) * r + (c0 * Cs * T * Bs) * r :=
          add_le_add (mul_le_mul_of_nonneg_left hσEr (by positivity))
            (mul_le_mul_of_nonneg_left hσer (by positivity))
  have h2 : ε * (Cy * Bs) ≤ Cy * Bs * r := by
    calc ε * (Cy * Bs) = (Cy * Bs) * ε := by ring
      _ ≤ (Cy * Bs) * r := mul_le_mul_of_nonneg_left hεr (by positivity)
  by_cases hr1 : r < 1
  · have hqw : q * w ≤ r := by
      have hs2 : (Real.sqrt q * Real.sqrt w) ^ 2 = q * w := by
        rw [mul_pow, Real.sq_sqrt hq0, Real.sq_sqrt hw]
      have hsr : Real.sqrt q * Real.sqrt w ≤ r := by rw [hr]; nlinarith
      have hs1 : Real.sqrt q * Real.sqrt w < 1 := lt_of_le_of_lt hsr hr1
      calc q * w = (Real.sqrt q * Real.sqrt w) ^ 2 := hs2.symm
        _ ≤ Real.sqrt q * Real.sqrt w := by nlinarith
        _ ≤ r := hsr
    have h3 : 1 / 2 * Ccov ≤ Ct * T * Bs ^ 2 * r := by
      have := hC1 hr1
      calc 1 / 2 * Ccov ≤ 1 / 2 * (2 * q * Ct * Bs ^ 2 * T * w) := by linarith
        _ = (Ct * T * Bs ^ 2) * (q * w) := by ring
        _ ≤ (Ct * T * Bs ^ 2) * r := mul_le_mul_of_nonneg_left hqw (by positivity)
    have hK1 : c0 * T * Bs + c0 * Cs * T * Bs + Cy * Bs + Ct * T * Bs ^ 2 ≤
        (c0 * T * (1 + Cs) + Cy + Ct * T + 2 * dd * T) * (Bs + Bs ^ 2) := by
      have : 0 ≤ dd * T * Bs := by positivity
      have : 0 ≤ dd * T * Bs ^ 2 := by positivity
      have : 0 ≤ c0 * T * Bs ^ 2 := by positivity
      have : 0 ≤ c0 * Cs * T * Bs ^ 2 := by positivity
      have : 0 ≤ Cy * Bs ^ 2 := by positivity
      have : 0 ≤ Ct * T * Bs := by positivity
      nlinarith
    calc σ * c0 * Bs * ((E + Cs * e) * T) + ε * (Cy * Bs) + 1 / 2 * Ccov
        ≤ (c0 * T * Bs * r + c0 * Cs * T * Bs * r) + Cy * Bs * r + Ct * T * Bs ^ 2 * r :=
          add_le_add (add_le_add h1 h2) h3
      _ = (c0 * T * Bs + c0 * Cs * T * Bs + Cy * Bs + Ct * T * Bs ^ 2) * r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK1 hr0
  · push Not at hr1
    have h3 : 1 / 2 * Ccov ≤ 2 * dd * T * Bs ^ 2 * r := by
      have := hC2 hr1
      calc 1 / 2 * Ccov ≤ 1 / 2 * (4 * q * dd * T * Bs ^ 2) := by linarith
        _ = (2 * dd * T * Bs ^ 2) * q := by ring
        _ ≤ (2 * dd * T * Bs ^ 2) * r :=
            mul_le_mul_of_nonneg_left (hq1.trans hr1) (by positivity)
    have hK1 : c0 * T * Bs + c0 * Cs * T * Bs + Cy * Bs + 2 * dd * T * Bs ^ 2 ≤
        (c0 * T * (1 + Cs) + Cy + Ct * T + 2 * dd * T) * (Bs + Bs ^ 2) := by
      have : 0 ≤ Ct * T * Bs := by positivity
      have : 0 ≤ Ct * T * Bs ^ 2 := by positivity
      have : 0 ≤ c0 * T * Bs ^ 2 := by positivity
      have : 0 ≤ c0 * Cs * T * Bs ^ 2 := by positivity
      have : 0 ≤ Cy * Bs ^ 2 := by positivity
      have : 0 ≤ dd * T * Bs := by positivity
      nlinarith
    calc σ * c0 * Bs * ((E + Cs * e) * T) + ε * (Cy * Bs) + 1 / 2 * Ccov
        ≤ (c0 * T * Bs * r + c0 * Cs * T * Bs * r) + Cy * Bs * r + 2 * dd * T * Bs ^ 2 * r :=
          add_le_add (add_le_add h1 h2) h3
      _ = (c0 * T * Bs + c0 * Cs * T * Bs + Cy * Bs + 2 * dd * T * Bs ^ 2) * r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK1 hr0

/-- the real arithmetic of the Wasserstein rate (with the additive error `Cs e`) -/
theorem sa4_arith_wass {Bs c0 Cs e Cy Ct T ε q σ E w : ℝ} (hBs : 0 ≤ Bs) (hc0 : 0 ≤ c0) (hCs : 0 ≤ Cs) (he : 0 ≤ e)
    (hCy : 0 ≤ Cy) (hCt : 0 ≤ Ct) (hT : 0 ≤ T) (hε : 0 ≤ ε) (hq0 : 0 ≤ q) (hσ : 0 ≤ σ) (hE : 0 ≤ E) (hw : 0 ≤ w) :
    ε * (Cy * Bs) + Real.sqrt (2 * q * Ct * Bs ^ 2 * T * w) + σ * c0 * Bs * ((E + Cs * e) * T) ≤
      (Cy + Real.sqrt (2 * Ct * T) + c0 * T * (1 + Cs)) * Bs * (ε + Real.sqrt q * Real.sqrt w + σ * (E + e)) := by
  set r : ℝ := ε + Real.sqrt q * Real.sqrt w + σ * (E + e) with hr
  have hsq : 0 ≤ Real.sqrt q * Real.sqrt w := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hσE : 0 ≤ σ * E := by positivity
  have hσe : 0 ≤ σ * e := by positivity
  have hs1 : Real.sqrt (2 * q * Ct * Bs ^ 2 * T * w) =
      Real.sqrt (2 * Ct * T) * Bs * (Real.sqrt q * Real.sqrt w) := by
    have e' : 2 * q * Ct * Bs ^ 2 * T * w = (2 * Ct * T * Bs ^ 2) * (q * w) := by ring
    rw [e', Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hBs,
      Real.sqrt_mul hq0]
  have hεr : ε ≤ r := by rw [hr]; nlinarith
  have hqr : Real.sqrt q * Real.sqrt w ≤ r := by rw [hr]; nlinarith
  have hσr : σ * E ≤ r := by rw [hr]; nlinarith
  have hσer : σ * e ≤ r := by rw [hr]; nlinarith
  have h1 : ε * (Cy * Bs) ≤ Cy * Bs * r := by
    calc ε * (Cy * Bs) = (Cy * Bs) * ε := by ring
      _ ≤ (Cy * Bs) * r := mul_le_mul_of_nonneg_left hεr (by positivity)
  have h2 : Real.sqrt (2 * Ct * T) * Bs * (Real.sqrt q * Real.sqrt w) ≤
      Real.sqrt (2 * Ct * T) * Bs * r :=
    mul_le_mul_of_nonneg_left hqr (by positivity)
  have h3 : σ * c0 * Bs * ((E + Cs * e) * T) ≤ c0 * T * Bs * r + c0 * Cs * T * Bs * r := by
    calc σ * c0 * Bs * ((E + Cs * e) * T) = (c0 * T * Bs) * (σ * E) + (c0 * Cs * T * Bs) * (σ * e) := by ring
      _ ≤ (c0 * T * Bs) * r + (c0 * Cs * T * Bs) * r :=
          add_le_add (mul_le_mul_of_nonneg_left hσr (by positivity))
            (mul_le_mul_of_nonneg_left hσer (by positivity))
  rw [hs1]
  calc _ ≤ Cy * Bs * r + Real.sqrt (2 * Ct * T) * Bs * r + (c0 * T * Bs * r + c0 * Cs * T * Bs * r) := by linarith
    _ = _ := by ring

end Arith

section SmoothCore

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}

theorem sa4_smooth_core (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) {C₀c : ℝ} (hC₀c : 0 ≤ C₀c)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {q : ℕ} (ts : Fin q → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ) (hφc : ∀ a, Continuous (φ a))
    {B : Fin q → ℝ} (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a)
    (hcl : ∀ a, IsClassicalAdjointW (S.coeff N) (ts a) (φ a)
      (fun r => propagatorW (S.coeff N) r (ts a) (φ a)))
    {Ccov : ℝ}
    (hcov : covDiscrepancyMatrix (R N).P S.T (sa2Sg S R N ts φ)
      (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N)) ≤ Ccov)
    (hη : ∀ ψ : Euc d → ℝ, Measurable fun ζ => (R N).η ζ ψ)
    {ce : ℝ} (hce : 0 ≤ ce) {κ : Fin q → ℝ} (hκ : ∀ a, 0 ≤ κ a) (hrem : Sa4Rem S N C₀c Λ ce ts φ κ)
    {eI : Fin q → ℝ} (heI : ∀ a, 0 ≤ eI a)
    (hIdiff : ∀ a, ∫⁻ ζ, ENNReal.ofReal |(sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ) a| ∂(R N).P ≤
      ENNReal.ofReal (eI a)) :
    smoothDist 2 (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
      (∑ a, S.sigma N * κ a) * ((𝔈 N + ce) * S.T) + ∑ a, eI a +
        1 / 2 * Ccov := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  have hr3 : 3 ≤ mStar d + 3 := Nat.le_add_left _ _
  have hmV : 2 ≤ mStar d + 4 := by have := sa2_two_le_mStar (d := d); omega
  have h𝔈 : 0 < 𝔈 N := hS.energy.pos N hN1
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  obtain ⟨hmart, -⟩ := sa2_vecmart hF ts hts φ hB hB0
  have hsb := sa2_sb_isDet hS hN1 ts φ hB0 hB
  have hdec := sa2_decomp hS hr3 hmV hN1 hF ts hts φ hB hB0 hcl
  have hinj := HRS.MS.PathFidi.sa26_flow_inj_all hT0 (hS.flow N hN1) hF
  have hψc : ∀ a, Continuous (propagatorW (S.coeff N) 0 (ts a) (φ a)) := fun a =>
    (hB a 0 ⟨le_rfl, (hts a).1⟩).1.1.continuous
  have hXm : ∀ t : ℝ≥0, Measurable ((R N).X t) := fun t => (hF.adapted t).mono (ℱ.le _) le_rfl
  have hIempm0 : Measurable[ℱ 0] (sa2Iemp S R N ts φ) :=
    HRS.MS.PathFidi.sa26_Iemp_meas (m := ℱ 0) hN0 S ts φ (hF.adapted 0) hψc
  have hIempm : Measurable (sa2Iemp S R N ts φ) := hIempm0.mono (ℱ.le 0) le_rfl
  have hItilm : Measurable (sa2Itil S R N ts φ) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a => measurable_const.mul (hη _))
  have hZm : Measurable (fluctStatRd (S.sigma N) (R N).X (S.ρ N) ts φ) :=
    HRS.MS.PathFidi.sa26_fluct_meas hN0 _ hXm _ ts φ hφc
  have hMT : AEMeasurable (vectorItoIntegral (R N).P ℱ W'
      (fun a => killAfter (sa2Phi S (ts a) (φ a) (R N).X) (ts a)) S.T) (R N).P :=
    (hmart.sq_int S.T ⟨hT0, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hRm : AEMeasurable (sa2Rem S R N ts φ) (R N).P := by
    refine ((hZm.sub hIempm).aemeasurable.sub hMT).congr ?_
    filter_upwards [hdec] with ζ h
    simp only [Pi.sub_apply]
    rw [h]
    abel
  -- the remainder
  have hL1 := sa4_rem_L1 hS hd hN hF.progressive hC₀c hC₀ hce ts hts φ hκ hrem hinj
  set cR : ℝ := ∑ a, S.sigma N * κ a with hcR
  have hcR0 : 0 ≤ cR := by
    refine Finset.sum_nonneg fun a _ => ?_
    have := sa2_sigma_nonneg S N
    have := hκ a
    positivity
  have hbd : ∫⁻ ζ, ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖ ∂(R N).P ≤
      ENNReal.ofReal (cR * ((𝔈 N + ce) * S.T)) := by
    have hsplit : ENNReal.ofReal ((𝔈 N + ce) * S.T) =
        ENNReal.ofReal (𝔈 N) * ENNReal.ofReal S.T + ENNReal.ofReal ce * ENNReal.ofReal S.T := by
      rw [add_mul, ENNReal.ofReal_add (mul_nonneg h𝔈.le hT0) (mul_nonneg hce hT0),
        ENNReal.ofReal_mul h𝔈.le, ENNReal.ofReal_mul hce]
    rw [ENNReal.ofReal_mul hcR0, hsplit]
    exact hL1
  have hRint : Integrable (sa2Rem S R N ts φ) (R N).P := by
    refine ⟨hRm.aestronglyMeasurable, ?_⟩
    have : HasFiniteIntegral (fun ζ => ‖sa2Rem S R N ts φ ζ‖) (R N).P := by
      rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ζ => norm_nonneg _)]
      exact lt_of_le_of_lt hbd ENNReal.ofReal_lt_top
    exact (hasFiniteIntegral_norm_iff _).1 this
  have hRle : ∫ ζ, ‖sa2Rem S R N ts φ ζ‖ ∂(R N).P ≤ cR * ((𝔈 N + ce) * S.T) :=
    HRS.MS.PathFidi.sa26_integral_le_lintegral (g := fun ζ => ‖sa2Rem S R N ts φ ζ‖)
      (fun _ => norm_nonneg _) hRm.norm.aestronglyMeasurable
      (mul_nonneg hcR0 (mul_nonneg (add_nonneg h𝔈.le hce) hT0)) hbd
  -- the initial difference
  have hcoord : ∀ a, Integrable (fun ζ => (sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ) a) (R N).P ∧
      ∫ ζ, |(sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ) a| ∂(R N).P ≤ eI a := by
    intro a
    have hm : Measurable fun ζ => (sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ) a := by
      have := (hIempm.sub hItilm)
      exact (measurable_pi_apply a).comp ((WithLp.measurable_ofLp 2 _).comp this)
    exact HRS.Main.A8P.a8p_abs_integral_le hm.aemeasurable (heI a) (hIdiff a)
  have hDint : Integrable (fun ζ => ‖sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ‖) (R N).P := by
    have hsum : Integrable (fun ζ => ∑ a, |(sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ) a|) (R N).P :=
      integrable_finset_sum _ fun a _ => (hcoord a).1.abs
    refine Integrable.mono' hsum (hIempm.sub hItilm).norm.aestronglyMeasurable ?_
    refine Eventually.of_forall fun ζ => ?_
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact HRS.Main.A8P.a8p_norm_le_sum_abs _
  have hDle : ∫ ζ, ‖sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ‖ ∂(R N).P ≤ ∑ a, eI a := by
    calc ∫ ζ, ‖sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ‖ ∂(R N).P
        ≤ ∫ ζ, ∑ a, |(sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ) a| ∂(R N).P :=
          integral_mono_of_nonneg (Eventually.of_forall fun ζ => norm_nonneg _)
            (integrable_finset_sum _ fun a _ => (hcoord a).1.abs)
            (Eventually.of_forall fun ζ => HRS.Main.A8P.a8p_norm_le_sum_abs _)
      _ = ∑ a, ∫ ζ, |(sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ) a| ∂(R N).P :=
          integral_finset_sum _ fun a _ => (hcoord a).1.abs
      _ ≤ ∑ a, eI a := Finset.sum_le_sum fun a _ => (hcoord a).2
  -- the abstract bound
  have habs := HRS.Main.A8P.a8p_smooth_abstract (R N).P ℱ S.T hT0
    (vectorItoIntegral (R N).P ℱ W'
      (fun a => killAfter (sa2Phi S (ts a) (φ a) (R N).X) (ts a)))
    (killedCovMatrix (fun a => sa2Phi S (ts a) (φ a) (R N).X) ts)
    hmart _ hsb (sa2Iemp S R N ts φ) hIempm0 (sa2Itil S R N ts φ) hItilm
    (fluctStatRd (S.sigma N) (R N).X (S.ρ N) ts φ) (sa2Rem S R N ts φ) hRint hdec hDint
  have hlaw : surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η =
      law (R N).P (sa2Itil S R N ts φ) ∗ multivariateGaussian 0
        (integratedCov S.T (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N))) := by
    unfold surrogateStatLawRd
    rw [sa2_sigma_eq hS ts hts φ]
    rfl
  unfold fluctStatLawRd
  rw [hlaw]
  have hcov' : covDiscrepancyMatrix (R N).P S.T
      (killedCovMatrix (fun a => sa2Phi S (ts a) (φ a) (R N).X) ts)
      (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N)) ≤ Ccov := hcov
  refine habs.trans ?_
  linarith


theorem sa4_smooth_rate (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) {C₀c Ct Cy c0 Cs e : ℝ}
    (hc0 : 0 ≤ c0) (hCs : 0 ≤ Cs) (he : 0 ≤ e) (hC₀c : 0 ≤ C₀c) (hCt : 0 ≤ Ct) (hCy : 0 ≤ Cy)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {χ : Euc d → ℝ} (hTest : Sa4Test d S.s χ C₀c Ct)
    (hY : Sa4Y0 d χ Cy) {m₀ : ℕ} {Cin : ℝ} {ε : ℕ → ℝ} {Ψ : ℕ → Set (Euc d → ℝ)} {m₂ : ℝ} (hm₂ : 0 ≤ m₂)
    (hmom : PropagatedSecondMoment S R m₂) {q : ℕ} (ts : Fin q → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ) (hφc : ∀ a, Continuous (φ a))
    {B : Fin q → ℝ} (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb (mStar d) (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm (mStar d) (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a)
    (hrem : Sa4Rem S N C₀c Λ (Cs * e) ts φ (fun a => c0 * B a))
    (hcl : ∀ a, IsClassicalAdjointW (S.coeff N) (ts a) (φ a)
      (fun r => propagatorW (S.coeff N) r (ts a) (φ a)))
    (hIF : InitialFluctuationRd S R χ m₀ Cin ε Ψ)
    (hΨ : ∀ a, propagatorW (S.coeff N) 0 (ts a) (φ a) ∈ Submodule.span ℝ (Ψ N)) :
    smoothDist 2 (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
      (c0 * S.T * (1 + Cs) + Cy + Ct * S.T + 2 * d * S.T) *
        ((∑ a, B a) + (∑ a, B a) ^ 2) *
        rdRate (ε N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈 N) e := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  have h𝔈 : 0 < 𝔈 N := hS.energy.pos N hN1
  have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  have hinj := HRS.MS.PathFidi.sa26_flow_inj_all hT0 (hS.flow N hN1) hF
  have hB2 : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a := fun a rr h =>
    ⟨sa2_memCb_mono sa2_two_le_mStar (hB a rr h).1,
      (sa2_cbNorm_mono sa2_two_le_mStar _).trans (hB a rr h).2⟩
  have hcost := sa4_cov_cost hS hd hN hF.progressive hTest hCt hC₀c hC₀ ts hts φ hB0 hB hinj hm₂ hmom
  have htriv := sa2_cov_triv hS hN1 ts φ hB0 hB2
  have hη : ∀ ψ : Euc d → ℝ, Measurable fun ζ => (R N).η ζ ψ := hIF.η_meas N
  have hdiff : ∀ a, ∫⁻ ζ, ENNReal.ofReal |(sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ) a| ∂(R N).P ≤
      ENNReal.ofReal (ε N * (Cy * B a)) := by
    intro a
    obtain ⟨hY0c, hYn⟩ := hY m₀ hIF.m₀_le _ (B a) (hB0 a) (hB a 0 ⟨le_rfl, (hts a).1⟩).1
      (hB a 0 ⟨le_rfl, (hts a).1⟩).2
    exact sa2_I1_diff hS hN1 hIF ts φ a (hΨ a) hYn hY0c
  have hcore := sa4_smooth_core hS hd hN hC₀c hC₀ ts hts φ hφc hB0 hB2 hcl
    (Ccov := covDiscrepancyMatrix (R N).P S.T (sa2Sg S R N ts φ)
      (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N))) le_rfl hη
    (ce := Cs * e) (mul_nonneg hCs he) (κ := fun a => c0 * B a) (fun a => mul_nonneg hc0 (hB0 a)) hrem
    (eI := fun a => ε N * (Cy * B a)) (fun a => by have := hB0 a; positivity) hdiff
  have hcR : ∑ a, S.sigma N * (c0 * B a) = S.sigma N * c0 * ∑ a, B a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have hsumε : ∑ a, ε N * (Cy * B a) = ε N * (Cy * ∑ a, B a) := by
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [hcR, hsumε] at hcore
  refine hcore.trans ?_
  have hq1 : S.qN N ≤ 1 := (Q54c.qScale_bounds hN0 (S.hκ N) (S.hinvβ N)).2
  have key := sa4_arith_smooth (Bs := ∑ a, B a) (c0 := c0) (Cs := Cs) (e := e) (Cy := Cy) (Ct := Ct) (dd := (d : ℝ))
    (T := S.T) (ε := ε N) (q := S.qN N) (σ := S.sigma N) (E := 𝔈 N) (w := wN d N (𝔈 N) m₂)
    (Ccov := covDiscrepancyMatrix (R N).P S.T (sa2Sg S R N ts φ)
      (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N)))
    (Finset.sum_nonneg fun a _ => hB0 a) hc0 hCs he hCy hCt (Nat.cast_nonneg d) hT0 hε (sa2_q_nonneg S N) hq1
    (sa2_sigma_nonneg S N) h𝔈.le (sa2_wN_nonneg h𝔈.le hm₂) (fun _ => hcost) (fun _ => htriv)
  unfold rdRate
  exact key


end SmoothCore

end HRS.MS.DecStat
