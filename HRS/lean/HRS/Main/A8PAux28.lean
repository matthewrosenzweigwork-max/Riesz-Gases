import HRS.Main.A8PAux27

/-!
# Packet A8P, part 28: the Wasserstein core estimate at fixed `N`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

section WassCore

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

theorem a8p_wass_core (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {C₀' Cq Cp : ℝ} (hcom : A8CommSpec d S.s C₀' Cq) (hCq : 0 ≤ Cq) (hC : C₀' ≤ C₀)
    (hCp0 : 0 ≤ Cp)
    (hCp : ∀ f g : Torus d → ℝ, Torus.IsCk 2 f → Torus.IsCk 2 g →
      MemSobolev (PDE.mStar d : ℝ) f → MemSobolev (PDE.mStar d : ℝ) g →
      HasFiniteHomSobolev (((d : ℝ) - S.s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ∧
      homSobolev (((d : ℝ) - S.s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ≤
        Cp * sobolevNorm (PDE.mStar d : ℝ) f * sobolevNorm (PDE.mStar d : ℝ) g)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a))
    (hnull : NullContactOccupation (R N).P S.T (R N).X)
    (hη : ∀ ψ : Torus d → ℝ, Measurable fun ω => (R N).η ω ψ)
    {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    wassersteinE p
      (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
      (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
    (∫⁻ ω, ENNReal.ofReal (‖a8pIemp S R N ts φ ω - a8pItil S R N ts φ ω‖ ^ p) ∂(R N).P) ^ (1 / p) +
      ENNReal.ofReal (Real.sqrt (a8pCovCost S N Cq Cp Ca Λ₁ Λ (𝔈 N) ts φ)) +
      (∫⁻ ω, ENNReal.ofReal (‖a8pRem S R N ts φ ω‖ ^ p) ∂(R N).P) ^ (1 / p) := by
  have hN1 : 1 ≤ N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N hN1
  obtain ⟨M, hM, hMid⟩ := a8p_hilbert_mart hspec hCa hS hN1 hF ts hts φ hφc hφ
  have hsb := a8p_sb_isDet hspec hCa hS hN1 ts hts φ hφc hφ
  have hdec := a8p_decomp hspec hCa hS hN hF ts hts φ hφc hφ
  have hψc : ∀ a, Continuous (propagator (S.dyn N) (S.ρ N) 0 (ts a) (φ a)) := fun a => by
    obtain ⟨-, hcl, -⟩ := a8p_adj_pkg hspec hCa hS hN1 (hts a) (hφc a) (hφ a)
    exact Q54c.isCk_continuous (hcl.c2 0 ⟨le_rfl, (hts a).1⟩)
  have hXm : ∀ t : ℝ≥0, Measurable ((R N).X t) := fun t => (hF.adapted t).mono (ℱ.le _) le_rfl
  have hIempm0 : Measurable[ℱ 0] (a8pIemp S R N ts φ) := by
    refine a8p_vec_meas (m := ℱ 0) _ fun a => Measurable.const_mul ?_ _
    exact a8p_flucPair_meas (m := ℱ 0) (hF.adapted 0) (hψc a) _
  have hItilm : Measurable (a8pItil S R N ts φ) :=
    a8p_vec_meas _ fun a => measurable_const.mul (hη _)
  have hZm : Measurable (fluctStat (S.sigma N) (R N).X (S.ρ N) ts φ) := by
    refine a8p_vec_meas _ fun a => Measurable.const_mul ?_ _
    exact a8p_flucPair_meas (hXm _) (hφc a) _
  have hMt : AEMeasurable (M S.T) (R N).P :=
    ((hM.adapted S.T).mono (ℱ.le _) le_rfl).aemeasurable
  have hRm : AEMeasurable (a8pRem S R N ts φ) (R N).P := by
    have hMT' : AEMeasurable (vectorItoIntegral (R N).P ℱ W'
      (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a))
      S.T) (R N).P := hMt.congr hMid
    refine ((hZm.sub (hIempm0.mono (ℱ.le 0) le_rfl)).aemeasurable.sub hMT').congr ?_
    filter_upwards [hdec] with ω h
    simp only [Pi.sub_apply]
    rw [h]
    abel
  have hW : IsCylindricalBrownian (R N).P ℱ W' := gfb3_isCylindricalBrownian_of_filtration hF.brownian
  have hZ : ∀ᵐ ω ∂(R N).P, fluctStat (S.sigma N) (R N).X (S.ρ N) ts φ ω =
      a8pIemp S R N ts φ ω + M S.T ω + a8pRem S R N ts φ ω := by
    filter_upwards [hdec, hMid] with ω h1 h2
    rw [h2]; exact h1
  have habs := a8p_wass_abstract (R N).P ℱ S.T hT0 W' hW (a8pPhiH S R N ts φ)
    (fun T => a8p_phiH_isHS hspec hCa hS hN1 hF.progressive ts hts φ hφc hφ T) M hM
    (fun r => a8pForm (a8pSb S N ts φ r)) (a8p_isDetCovDensity hsb) _ (a8p_gauss hsb)
    (a8pIemp S R N ts φ) (a8pItil S R N ts φ) (fluctStat (S.sigma N) (R N).X (S.ρ N) ts φ)
    (a8pRem S R N ts φ) hIempm0 hItilm.aemeasurable hRm hZ p hp1 hp2
  have hcov : covDiscrepancy (R N).P S.T (fun r ω => hsCovForm (a8pPhiH S R N ts φ r ω))
      (fun r => a8pForm (a8pSb S N ts φ r)) ≤ a8pCovCost S N Cq Cp Ca Λ₁ Λ (𝔈 N) ts φ := by
    unfold covDiscrepancy
    simp only [a8p_hsCov_eq]
    refine a8p_cov_cost_gen hspec hCa hS hN hcom hCq hC hCp0 hCp ts hts φ hφc hφ hF.progressive hnull
      (fun r ω => traceNormForm (a8pForm (a8pSg S R N ts φ r ω) - a8pForm (a8pSb S N ts φ r)))
      (fun r ω => traceNormForm_nonneg _) (fun r ω => ?_)
    rw [← a8pForm_sub]
    refine (a8p_traceNormForm_le _).trans (le_of_eq ?_)
    simp only [Matrix.sub_apply]
  have hlaw : surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η =
      law (R N).P (a8pItil S R N ts φ) ∗ multivariateGaussian 0
        (integratedCov S.T (a8pSb S N ts φ)) := by
    have hsc := a8p_surrogateCov_eq (S.dyn N) (S.ρ N) (S.qN N) S.T ts φ (fun a => (hts a).2)
      (fun r => S.ρ N (Q54c.clampT S.T r)) (fun r hr => by rw [Q54c.clampT_of_mem hr])
    have hq := a8p_q_eq S N
    unfold surrogateStatLaw
    rw [hsc, hq]
    rfl
  rw [hlaw]
  refine habs.trans ?_
  gcongr

end WassCore

end HRS.Main.A8P
