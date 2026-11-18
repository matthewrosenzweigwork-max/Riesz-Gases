import HRS.MS.MainRdStatAux14

/-!
# SA2, packet 8b: the Hilbert-space (`W_p`) core estimate at fixed `N`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

theorem sa2_y0Norm_nonneg {m₀ : ℕ} {χ : Euc d → ℝ} {ψ : Euc d → ℝ} : 0 ≤ y0Norm m₀ χ ψ := by
  unfold y0Norm HRS.PDE.ToolboxRd.c01Norm
  exact add_nonneg ENNReal.toReal_nonneg (add_nonneg (Real.iSup_nonneg fun x => abs_nonneg _)
    (Real.iSup_nonneg fun p => by positivity))

section WassCore

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}

theorem sa2_diffcoord_meas (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    {N : ℕ} (hN : 1 ≤ N) {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (φ : Fin q → Euc d → ℝ) {B : Fin q → ℝ}
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a)
    (hη : ∀ ψ : Euc d → ℝ, Measurable fun ζ => (R N).η ζ ψ) (a : Fin q) :
    Measurable fun ζ => (sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ) a := by
  have hN0 : 0 < N := by omega
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  have hψc : ∀ a, Continuous (propagatorW (S.coeff N) 0 (ts a) (φ a)) := fun a =>
    (hB a 0 ⟨le_rfl, (hts a).1⟩).1.1.continuous
  have hIempm0 : Measurable[ℱ 0] (sa2Iemp S R N ts φ) :=
    HRS.MS.PathFidi.sa26_Iemp_meas (m := ℱ 0) hN0 S ts φ (hF.adapted 0) hψc
  have hIempm : Measurable (sa2Iemp S R N ts φ) := hIempm0.mono (ℱ.le 0) le_rfl
  have hItilm : Measurable (sa2Itil S R N ts φ) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a => measurable_const.mul (hη _))
  exact (measurable_pi_apply a).comp ((WithLp.measurable_ofLp 2 _).comp (hIempm.sub hItilm))

/-- the covariance cost in the Hilbert-Schmidt form -/
theorem sa2_covH (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) {ℱ : Filtration ℝ (R N).mΩ}
    (hprog : IsProgressive ℱ (ofNNRealTime (R N).X))
    {χ : Euc d → ℝ} {C₀c Ct : ℝ} (hTest : Sa2Test d S.s χ C₀c Ct) (hCt : 0 ≤ Ct) (hC₀c : 0 ≤ C₀c)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {q : ℕ} (ts : Fin q → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ) {B : Fin q → ℝ}
    (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a)
    (hU : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a),
      ulocNormE 2 χ (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ ENNReal.ofReal (B a))
    (hinj : ∀ᵐ ζ ∂(R N).P, ∀ᵐ rr ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal rr) ζ))
    {m₂ : ℝ} (hm₂ : 0 ≤ m₂) (hmom : PropagatedSecondMoment S R m₂) :
    covDiscrepancy (R N).P S.T (fun rr ζ => hsCovForm (sa2PhiH S R N ts φ rr ζ))
        (fun rr => HRS.Main.A8P.a8pForm (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) rr)) ≤
      2 * S.qN N * Ct * (∑ a, B a) ^ 2 * S.T * wN d N (𝔈 N) m₂ := by
  unfold covDiscrepancy
  simp only [sa2_hsCov_eq]
  refine sa2_cov_cost_gen hS hd hN hprog hTest hCt hC₀c hC₀ ts hts φ hB0 hB hU hinj hm₂ hmom
    (fun rr ζ => traceNormForm (HRS.Main.A8P.a8pForm (sa2Sg S R N ts φ rr ζ) -
      HRS.Main.A8P.a8pForm (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) rr)))
    (fun rr ζ => traceNormForm_nonneg _) (fun rr ζ => ?_)
  rw [← HRS.Main.A8P.a8pForm_sub]
  refine (HRS.Main.A8P.a8p_traceNormForm_le _).trans (le_of_eq ?_)
  simp only [Matrix.sub_apply]

theorem sa2_wass_core (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    {N : ℕ} (hN : 1 ≤ N) {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (φ : Fin q → Euc d → ℝ) (hφc : ∀ a, Continuous (φ a)) {B : Fin q → ℝ} (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a)
    (hcl : ∀ a, IsClassicalAdjointW (S.coeff N) (ts a) (φ a)
      (fun r => propagatorW (S.coeff N) r (ts a) (φ a)))
    (hη : ∀ ψ : Euc d → ℝ, Measurable fun ζ => (R N).η ζ ψ) {Ccov : ℝ}
    (hcov : covDiscrepancy (R N).P S.T (fun rr ζ => hsCovForm (sa2PhiH S R N ts φ rr ζ))
        (fun rr => HRS.Main.A8P.a8pForm (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) rr)) ≤
      Ccov)
    {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    wassersteinE p (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
      (∫⁻ ζ, ENNReal.ofReal (‖sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ‖ ^ p) ∂(R N).P) ^ (1 / p) +
        ENNReal.ofReal (Real.sqrt Ccov) +
        (∫⁻ ζ, ENNReal.ofReal (‖sa2Rem S R N ts φ ζ‖ ^ p) ∂(R N).P) ^ (1 / p) := by
  have hN0 : 0 < N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  have hr3 : 3 ≤ mStar d + 3 := Nat.le_add_left _ _
  have hmV : 2 ≤ mStar d + 4 := by have := sa2_two_le_mStar (d := d); omega
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  obtain ⟨M, hM, hMid⟩ := sa2_hilbert_mart (S := S) hF ts hts φ hB0 hB
  have hsb := sa2_sb_isDet hS hN ts φ hB0 hB
  have hdec := sa2_decomp hS hr3 hmV hN hF ts hts φ hB hB0 hcl
  have hψc : ∀ a, Continuous (propagatorW (S.coeff N) 0 (ts a) (φ a)) := fun a =>
    (hB a 0 ⟨le_rfl, (hts a).1⟩).1.1.continuous
  have hXm : ∀ t : ℝ≥0, Measurable ((R N).X t) := fun t => (hF.adapted t).mono (ℱ.le _) le_rfl
  have hIempm0 : Measurable[ℱ 0] (sa2Iemp S R N ts φ) :=
    HRS.MS.PathFidi.sa26_Iemp_meas (m := ℱ 0) hN0 S ts φ (hF.adapted 0) hψc
  have hItilm : Measurable (sa2Itil S R N ts φ) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a => measurable_const.mul (hη _))
  have hZm : Measurable (fluctStatRd (S.sigma N) (R N).X (S.ρ N) ts φ) :=
    HRS.MS.PathFidi.sa26_fluct_meas hN0 _ hXm _ ts φ hφc
  have hMt : AEMeasurable (M S.T) (R N).P :=
    ((hM.adapted S.T).mono (ℱ.le _) le_rfl).aemeasurable
  have hRm : AEMeasurable (sa2Rem S R N ts φ) (R N).P := by
    have hMT' : AEMeasurable (vectorItoIntegral (R N).P ℱ W'
        (fun a => killAfter (sa2Phi S (ts a) (φ a) (R N).X) (ts a)) S.T) (R N).P := hMt.congr hMid
    refine ((hZm.sub (hIempm0.mono (ℱ.le 0) le_rfl)).aemeasurable.sub hMT').congr ?_
    filter_upwards [hdec] with ζ h
    simp only [Pi.sub_apply]
    rw [h]
    abel
  have hW : IsCylindricalBrownian (R N).P ℱ W' := gfb3_isCylindricalBrownian_of_filtration hF.brownian
  have hZ : ∀ᵐ ζ ∂(R N).P, fluctStatRd (S.sigma N) (R N).X (S.ρ N) ts φ ζ =
      sa2Iemp S R N ts φ ζ + M S.T ζ + sa2Rem S R N ts φ ζ := by
    filter_upwards [hdec, hMid] with ζ h1 h2
    rw [h2]; exact h1
  have habs := HRS.Main.A8P.a8p_wass_abstract (R N).P ℱ S.T hT0 W' hW (sa2PhiH S R N ts φ)
    (fun T => sa2_phiH_isHS (S := S) hF.progressive ts φ hB0 hB T) M hM
    (fun rr => HRS.Main.A8P.a8pForm (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) rr))
    (HRS.Main.A8P.a8p_isDetCovDensity hsb) _ (HRS.Main.A8P.a8p_gauss hsb)
    (sa2Iemp S R N ts φ) (sa2Itil S R N ts φ) (fluctStatRd (S.sigma N) (R N).X (S.ρ N) ts φ)
    (sa2Rem S R N ts φ) hIempm0 hItilm.aemeasurable hRm hZ p hp1 hp2
  have hlaw : surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η =
      law (R N).P (sa2Itil S R N ts φ) ∗ multivariateGaussian 0
        (integratedCov S.T (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N))) := by
    unfold surrogateStatLawRd
    rw [sa2_sigma_eq hS ts hts φ]
    rfl
  unfold fluctStatLawRd
  rw [hlaw]
  refine habs.trans ?_
  have hsq : ENNReal.ofReal (Real.sqrt (covDiscrepancy (R N).P S.T
      (fun rr ζ => hsCovForm (sa2PhiH S R N ts φ rr ζ))
      (fun rr => HRS.Main.A8P.a8pForm (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) rr)))) ≤
      ENNReal.ofReal (Real.sqrt Ccov) := ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hcov)
  exact add_le_add (add_le_add le_rfl hsq) le_rfl

end WassCore

end HRS.MS.MainRdStat
