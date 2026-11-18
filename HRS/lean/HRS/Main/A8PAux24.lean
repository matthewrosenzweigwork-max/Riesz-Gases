import HRS.Main.A8PAux23

/-!
# Packet A8P, part 24: the smooth-metric core estimate at fixed `N`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

section SmoothCore

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

theorem a8p_smooth_core (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {C₀' Cq cT : ℝ} (hcom : A8CommSpec d S.s C₀' Cq) (hCq : 0 ≤ Cq) (hC : C₀' ≤ C₀)
    (hcT0 : 0 ≤ cT)
    (hcT : ∀ (M : Matrix (Fin d) (Fin d) ℝ), PDE.MatBound MB M → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      MemSobolev (PDE.mStar d : ℝ) ψ →
        HasTransportBound d S.s (gfb2_v M ψ) (cT * sobolevNorm (PDE.mStar d : ℝ) ψ))
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a))
    {Ccov : ℝ} (hcov : covDiscrepancyMatrix (R N).P S.T (a8pSg S R N ts φ) (a8pSb S N ts φ) ≤ Ccov)
    (hη : ∀ ψ : Torus d → ℝ, Measurable fun ω => (R N).η ω ψ) {eI : ℝ} (heI : 0 ≤ eI)
    (hIdiff : ∀ a, ∫⁻ ω, ENNReal.ofReal
        |S.sigma N * flucPair ((R N).X 0 ω) (S.ρ N 0) (propagator (S.dyn N) (S.ρ N) 0 (ts a) (φ a)) -
          S.AN N * (R N).η ω (propagator (S.dyn N) (S.ρ N) 0 (ts a) (φ a))| ∂(R N).P ≤
        ENNReal.ofReal (eI * a8pK Λ₁ (ts a) (φ a))) :
    smoothDist 2
      (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
      (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
    (∑ a, S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ (ts a) (φ a))))) * (S.T * 𝔈 N) +
      ∑ a, eI * a8pK Λ₁ (ts a) (φ a) +
      (1 / 2) * Ccov := by
  have hN1 : 1 ≤ N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N hN1
  obtain ⟨hmart, -⟩ := a8p_vector_mart hspec hCa hS hN1 hF ts hts φ hφc hφ
  have hsb := a8p_sb_isDet hspec hCa hS hN1 ts hts φ hφc hφ
  have hdec := a8p_decomp hspec hCa hS hN hF ts hts φ hφc hφ
  have hψc : ∀ a, Continuous (propagator (S.dyn N) (S.ρ N) 0 (ts a) (φ a)) := fun a => by
    obtain ⟨-, hcl, -⟩ := a8p_adj_pkg hspec hCa hS hN1 (hts a) (hφc a) (hφ a)
    exact Q54c.isCk_continuous (hcl.c2 0 ⟨le_rfl, (hts a).1⟩)
  have hXm : ∀ t : ℝ≥0, Measurable ((R N).X t) := fun t => (hF.adapted t).mono (ℱ.le _) le_rfl
  have hIempm0 : Measurable[ℱ 0] (a8pIemp S R N ts φ) := by
    refine a8p_vec_meas (m := ℱ 0) _ fun a => Measurable.const_mul ?_ _
    exact a8p_flucPair_meas (m := ℱ 0) (hF.adapted 0) (hψc a) _
  have hIempm : Measurable (a8pIemp S R N ts φ) := hIempm0.mono (ℱ.le 0) le_rfl
  have hItilm : Measurable (a8pItil S R N ts φ) :=
    a8p_vec_meas _ fun a => measurable_const.mul (hη _)
  have hZm : Measurable (fluctStat (S.sigma N) (R N).X (S.ρ N) ts φ) := by
    refine a8p_vec_meas _ fun a => Measurable.const_mul ?_ _
    exact a8p_flucPair_meas (hXm _) (hφc a) _
  have hMT : AEMeasurable (vectorItoIntegral (R N).P ℱ W'
      (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a))
      S.T) (R N).P :=
    (hmart.sq_int S.T ⟨hT0, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hRm : AEMeasurable (a8pRem S R N ts φ) (R N).P := by
    refine ((hZm.sub hIempm).aemeasurable.sub hMT).congr ?_
    filter_upwards [hdec] with ω h
    simp only [Pi.sub_apply]
    rw [h]
    abel
  -- the remainder
  obtain ⟨hEint, hEle⟩ := a8p_Een hS hN1 (hF.progressive) (C₀ := C₀) (Λ := Λ)
  have hbd := a8p_rem_norm_bound hspec hCa hS hN hF hcom hCq hC hcT0 hcT ts hts φ hφc hφ
  set cR : ℝ := ∑ a, S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ (ts a) (φ a)))) with hcR
  have hcR0 : 0 ≤ cR := by
    refine Finset.sum_nonneg fun a _ => ?_
    have := a8pK_nonneg Λ₁ (ts a) (φ a)
    have := a8p_sigma_nonneg S N
    positivity
  have hRint : Integrable (a8pRem S R N ts φ) (R N).P := by
    refine Integrable.mono' (hEint.const_mul cR) hRm.aestronglyMeasurable ?_
    filter_upwards [hbd] with ω h
    exact h
  have hRle : ∫ ω, ‖a8pRem S R N ts φ ω‖ ∂(R N).P ≤ cR * (S.T * 𝔈 N) := by
    calc ∫ ω, ‖a8pRem S R N ts φ ω‖ ∂(R N).P
        ≤ ∫ ω, cR * (∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω) ∂(R N).P :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _)
            (hEint.const_mul cR) hbd
      _ = cR * ∫ ω, (∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω) ∂(R N).P := integral_const_mul _ _
      _ ≤ cR * (S.T * 𝔈 N) := mul_le_mul_of_nonneg_left hEle hcR0
  -- the initial difference
  have hcoord : ∀ a, Integrable (fun ω => (a8pIemp S R N ts φ ω - a8pItil S R N ts φ ω) a) (R N).P ∧
      ∫ ω, |(a8pIemp S R N ts φ ω - a8pItil S R N ts φ ω) a| ∂(R N).P ≤
        eI * a8pK Λ₁ (ts a) (φ a) := by
    intro a
    have hK := a8pK_nonneg Λ₁ (ts a) (φ a)
    have hm : Measurable fun ω => (a8pIemp S R N ts φ ω - a8pItil S R N ts φ ω) a := by
      have := (hIempm.sub hItilm)
      exact (measurable_pi_apply a).comp ((WithLp.measurable_ofLp 2 _).comp this)
    exact a8p_abs_integral_le hm.aemeasurable (mul_nonneg heI hK) (hIdiff a)
  have hDint : Integrable (fun ω => ‖a8pIemp S R N ts φ ω - a8pItil S R N ts φ ω‖) (R N).P := by
    have hsum : Integrable (fun ω => ∑ a, |(a8pIemp S R N ts φ ω - a8pItil S R N ts φ ω) a|) (R N).P :=
      integrable_finset_sum _ fun a _ => (hcoord a).1.abs
    refine Integrable.mono' hsum (hIempm.sub hItilm).norm.aestronglyMeasurable ?_
    refine Eventually.of_forall fun ω => ?_
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact a8p_norm_le_sum_abs _
  have hDle : ∫ ω, ‖a8pIemp S R N ts φ ω - a8pItil S R N ts φ ω‖ ∂(R N).P ≤
      ∑ a, eI * a8pK Λ₁ (ts a) (φ a) := by
    calc ∫ ω, ‖a8pIemp S R N ts φ ω - a8pItil S R N ts φ ω‖ ∂(R N).P
        ≤ ∫ ω, ∑ a, |(a8pIemp S R N ts φ ω - a8pItil S R N ts φ ω) a| ∂(R N).P :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _)
            (integrable_finset_sum _ fun a _ => (hcoord a).1.abs)
            (Eventually.of_forall fun ω => a8p_norm_le_sum_abs _)
      _ = ∑ a, ∫ ω, |(a8pIemp S R N ts φ ω - a8pItil S R N ts φ ω) a| ∂(R N).P :=
          integral_finset_sum _ fun a _ => (hcoord a).1.abs
      _ ≤ ∑ a, eI * a8pK Λ₁ (ts a) (φ a) := Finset.sum_le_sum fun a _ => (hcoord a).2
  -- the abstract bound
  have habs := a8p_smooth_abstract (R N).P ℱ S.T hT0
    (vectorItoIntegral (R N).P ℱ W'
      (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a)))
    (killedCovMatrix (fun a => a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) ts)
    hmart _ hsb (a8pIemp S R N ts φ) hIempm0 (a8pItil S R N ts φ) hItilm
    (fluctStat (S.sigma N) (R N).X (S.ρ N) ts φ) (a8pRem S R N ts φ) hRint hdec hDint
  have hsc := a8p_surrogateCov_eq (S.dyn N) (S.ρ N) (S.qN N) S.T ts φ (fun a => (hts a).2)
    (fun r => S.ρ N (Q54c.clampT S.T r)) (fun r hr => by rw [Q54c.clampT_of_mem hr])
  have hq := a8p_q_eq S N
  have hlaw : surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η =
      law (R N).P (a8pItil S R N ts φ) ∗ multivariateGaussian 0
        (integratedCov S.T (a8pSigBar ts (a8pG ts (a8pF S N ts φ))
          (fun r => S.ρ N (Q54c.clampT S.T r)) (2 * (S.sigma N ^ 2 * S.invβ N / N)))) := by
    unfold surrogateStatLaw
    rw [hsc, hq]
    rfl
  rw [hlaw]
  have hcov' : covDiscrepancyMatrix (R N).P S.T
      (killedCovMatrix (fun a => a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) ts)
      (a8pSigBar ts (a8pG ts (a8pF S N ts φ)) (fun r => S.ρ N (Q54c.clampT S.T r))
        (2 * (S.sigma N ^ 2 * S.invβ N / N))) ≤ Ccov := hcov
  refine habs.trans ?_
  linarith

end SmoothCore

end HRS.Main.A8P
