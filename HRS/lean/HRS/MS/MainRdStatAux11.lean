import HRS.MS.MainRdStatAux10

/-!
# SA2, packet 7a: the smooth-metric core estimate at fixed `N`, and the coupling of the initial data
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

section SmoothCore

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}

theorem sa2_smooth_core (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) {Lm C₀c Cq : ℝ}
    (hLm : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) S.T →
      HasLogMoment (HRS.Whole.withDensityReal (S.ρ N t)) Lm)
    (hcomm : Sa2Comm d S.s Lm C₀c Cq) (hCq : 0 ≤ Cq) (hC₀c : 0 ≤ C₀c)
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
    {eI : Fin q → ℝ} (heI : ∀ a, 0 ≤ eI a)
    (hIdiff : ∀ a, ∫⁻ ζ, ENNReal.ofReal |(sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ) a| ∂(R N).P ≤
      ENNReal.ofReal (eI a)) :
    smoothDist 2 (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
      (∑ a, S.sigma N * (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a)))) * (𝔈 N * S.T) + ∑ a, eI a +
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
  have hL1 := sa2_rem_L1 hS hr3 hd hN hF.progressive hLm hcomm hCq hC₀c hC₀ ts hts φ hB hinj
  set cR : ℝ := ∑ a, S.sigma N * (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a))) with hcR
  have hcR0 : 0 ≤ cR := by
    refine Finset.sum_nonneg fun a _ => ?_
    have := sa2_sigma_nonneg S N
    have := sa2_cMB_nonneg (d := d) (MB := MB) (M := S.M) hS.matrix_bound
    have := hB0 a
    positivity
  have hbd : ∫⁻ ζ, ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖ ∂(R N).P ≤ ENNReal.ofReal (cR * (𝔈 N * S.T)) := by
    rw [ENNReal.ofReal_mul hcR0, ENNReal.ofReal_mul h𝔈.le]
    exact hL1
  have hRint : Integrable (sa2Rem S R N ts φ) (R N).P := by
    refine ⟨hRm.aestronglyMeasurable, ?_⟩
    have : HasFiniteIntegral (fun ζ => ‖sa2Rem S R N ts φ ζ‖) (R N).P := by
      rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ζ => norm_nonneg _)]
      exact lt_of_le_of_lt hbd ENNReal.ofReal_lt_top
    exact (hasFiniteIntegral_norm_iff _).1 this
  have hRle : ∫ ζ, ‖sa2Rem S R N ts φ ζ‖ ∂(R N).P ≤ cR * (𝔈 N * S.T) :=
    HRS.MS.PathFidi.sa26_integral_le_lintegral (g := fun ζ => ‖sa2Rem S R N ts φ ζ‖)
      (fun _ => norm_nonneg _) hRm.norm.aestronglyMeasurable (mul_nonneg hcR0 (mul_nonneg h𝔈.le hT0)) hbd
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

end SmoothCore

section InitialCoupling

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ}
  {𝔈 : ℕ → ℝ}

/-- The coordinates of `I_emp - Ĩ` from the coupling (I1). -/
theorem sa2_I1_diff (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {χ : Euc d → ℝ} {m₀ : ℕ} {Cin : ℝ} {ε : ℕ → ℝ} {Ψ : ℕ → Set (Euc d → ℝ)}
    (hIF : InitialFluctuationRd S R χ m₀ Cin ε Ψ) {q : ℕ} (ts : Fin q → ℝ) (φ : Fin q → Euc d → ℝ)
    (a : Fin q) (hmem : propagatorW (S.coeff N) 0 (ts a) (φ a) ∈ Submodule.span ℝ (Ψ N))
    {Y : ℝ} (hY : y0Norm m₀ χ (propagatorW (S.coeff N) 0 (ts a) (φ a)) ≤ Y)
    (hY0 : Y0Class m₀ χ (propagatorW (S.coeff N) 0 (ts a) (φ a))) :
    ∫⁻ ζ, ENNReal.ofReal |(sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ) a| ∂(R N).P ≤
      ENNReal.ofReal (ε N * Y) := by
  have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
  have hI1 := hIF.I1 N hN _ hmem hY0
  have hinit := HRS.MS.PathFidi.sa26_init_ae (hS.flow N hN)
  have hdat := hS.mean_field.datum N hN
  have hA0 := sa2_AN_nonneg S N
  have hA1 := sa2_AN_le_one S N
  have hAk := sa2_AN_mul S N
  refine le_trans (lintegral_mono_ae ?_) (hI1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hY hε)))
  filter_upwards [hinit] with ζ hζ
  refine ENNReal.ofReal_le_ofReal ?_
  have heq : (sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ) a =
      S.AN N * (S.κ N * (HRS.Whole.pair (HRS.Whole.empirical ((R N).X₀ ζ)) (propagatorW (S.coeff N) 0 (ts a) (φ a)) -
        HRS.Whole.pair S.μ0 (propagatorW (S.coeff N) 0 (ts a) (φ a))) -
        (R N).η ζ (propagatorW (S.coeff N) 0 (ts a) (φ a))) := by
    simp only [sa2Iemp, sa2Itil, PiLp.sub_apply, WithLp.ofLp_toLp, hζ, hdat]
    rw [← hAk]; ring
  rw [heq, abs_mul, abs_of_nonneg hA0]
  calc S.AN N * _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hA1 (abs_nonneg _)
    _ = _ := one_mul _

end InitialCoupling

end HRS.MS.MainRdStat
