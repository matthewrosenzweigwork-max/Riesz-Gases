import HRS.Main.A9Final
import HRS.Main.A1014Aux4
import HRS.Main.A1014Aux5
import HRS.Main.A1014Aux6

/-!
# Packet A1014, part 7: the core `W_p` chain for one finite set of modes (fixed `N`, `t`)

`a1014_core_abs`: instantiation of `a1014_wass_abstract` with the objects of Proposition A.9
(`a9Z, a9I, a9Itil`, the `ℝ^q`-valued Hilbert martingale of the modes `k`, `embedCLM`, `hmCoordCLM`),
`p ∈ [1,2]`:
`W_p(particle, linear) ≤ ‖Z - 𝕀 - ι M_T‖_p + √(cost) + ‖𝕀 - Ĩ‖_p + ‖y - ι c y‖_{L^p(νG)}`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A1014

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.A33 HRS.PDE HRS.Main HRS.Main.A8P HRS.Main.A9 HRS.GF HRS.Uniform

variable {d : ℕ}

section Core

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ C₀' Cq Cp cT : ℝ}

theorem a1014_core_abs (hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : MeasureTheory.Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {Cin : ℝ} {εf : ℕ → ℝ} {ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ)}
    {νin : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {νG : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hνG : IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG)
    {q : ℕ} {k : Fin q → NonzeroLattice d} (hk : Function.Injective k) {p : ℝ} (hp1 : 1 ≤ p)
    (hp2 : p ≤ 2) :
    wassersteinE p
      (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
      (linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG) ≤
    (∫⁻ ω, ENNReal.ofReal (‖a9Z S R N t ω - a9I S R N t ω - embedCLM
        (fun a => a9unit (gammaIdx d : ℝ) (k a))
        (vectorItoIntegral (R N).P ℱ W'
          (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) ((fun _ : Fin q => t) a)
            (a8pF S N (fun _ : Fin q => t) (fun a => a9phi d (k a)) a) (R N).X)
            ((fun _ : Fin q => t) a)) S.T ω)‖ ^ p) ∂(R N).P) ^ (1 / p) +
    ENNReal.ofReal (Real.sqrt (a8pCovCost S N Cq Cp Ca Λ₁ Λ (𝔈 N) (fun _ : Fin q => t)
      (fun a => a9phi d (k a)))) +
    (∫⁻ ω, ENNReal.ofReal (‖a9I S R N t ω - a9Itil S R N t ηF ω‖ ^ p) ∂(R N).P) ^ (1 / p) +
    (∫⁻ y, ENNReal.ofReal (‖y - embedCLM (fun a => a9unit (gammaIdx d : ℝ) (k a))
      (hmCoordCLM (fun a => a9unit (gammaIdx d : ℝ) (k a)) y)‖ ^ p) ∂νG) ^ (1 / p) := by
  classical
  obtain ⟨hCa, hspec, hcom, hCq, hC, hCp0, hCp, hcT0, hcT⟩ := hP
  have hS' := a9_standing_mStar hS
  have hN1 : 1 ≤ N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  have hprob := hνG.1
  haveI := hprob
  set ts : Fin q → ℝ := fun _ => t with hts_def
  set φ : Fin q → Torus d → ℝ := fun a => a9phi d (k a) with hφ_def
  have hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T := fun _ => ht
  have hφc : ∀ a, Continuous (φ a) := fun a => a9phi_cont _
  have hφm : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a) := fun a => a9phi_mem _ _
  obtain ⟨M, hM, hMid⟩ := a8p_hilbert_mart hspec hCa hS' hN1 hF ts hts φ hφc hφm
  have hsb := a8p_sb_isDet hspec hCa hS' hN1 ts hts φ hφc hφm
  have hW : IsCylindricalBrownian (R N).P ℱ W' :=
    gfb3_isCylindricalBrownian_of_filtration hF.brownian
  set b : Fin q → NegSobolev d (gammaIdx d : ℝ) := fun a => a9unit (gammaIdx d : ℝ) (k a) with hb
  have hbo : Orthonormal ℝ b := a9unit_orthonormal hk
  have hι := norm_embedCLM_le hbo
  have hνγ := a9_gauss_law hS' hN1 ht k hνG
  have hZm := a9_Z_meas hS hN1 ht hF
  have hXm0 := a9_I_meas hS hN1 ht hF
  have hXtm := a9_Itil_meas hS hN1 ht hfield
  have habs := a1014_wass_abstract (R N).P ℱ S.T hT0 W' hW (a8pPhiH S R N ts φ)
    (fun T => a8p_phiH_isHS hspec hCa hS' hN1 hF.progressive ts hts φ hφc hφm T) M hM
    (fun r => a8pForm (a8pSb S N ts φ r)) (a8p_isDetCovDensity hsb)
    (multivariateGaussian (0 : ℝ^q) (integratedCov S.T (a8pSb S N ts φ))) (a8p_gauss hsb)
    (embedCLM b) hι (fun y => hmCoordCLM b y) (hmCoordCLM b).continuous.measurable νG hνγ
    (a9I S R N t) (a9Itil S R N t ηF) (a9Z S R N t) hXm0 hXtm.aemeasurable hZm.aemeasurable p hp1 hp2
  have hcov : covDiscrepancy (R N).P S.T (fun r ω => hsCovForm (a8pPhiH S R N ts φ r ω))
      (fun r => a8pForm (a8pSb S N ts φ r)) ≤ a8pCovCost S N Cq Cp Ca Λ₁ Λ (𝔈 N) ts φ := by
    unfold covDiscrepancy
    simp only [a8p_hsCov_eq]
    refine a8p_cov_cost_gen hspec hCa hS' hN hcom hCq hC hCp0 hCp ts hts φ hφc hφm hF.progressive
      (a8p_nullContact hS' hN1)
      (fun r ω => traceNormForm (a8pForm (a8pSg S R N ts φ r ω) - a8pForm (a8pSb S N ts φ r)))
      (fun r ω => traceNormForm_nonneg _) (fun r ω => ?_)
    rw [← a8pForm_sub]
    refine (a8p_traceNormForm_le _).trans (le_of_eq ?_)
    simp only [Matrix.sub_apply]
  have hmt : ∀ᵐ ω ∂(R N).P, M S.T ω = vectorItoIntegral (R N).P ℱ W'
      (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a))
      S.T ω := hMid
  have hfirst : (∫⁻ ω, ENNReal.ofReal (‖a9Z S R N t ω - a9I S R N t ω -
      embedCLM b (M S.T ω)‖ ^ p) ∂(R N).P) =
      ∫⁻ ω, ENNReal.ofReal (‖a9Z S R N t ω - a9I S R N t ω - embedCLM b
        (vectorItoIntegral (R N).P ℱ W'
          (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X)
            (ts a)) S.T ω)‖ ^ p) ∂(R N).P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hmt] with ω h
    rw [h]
  rw [hfirst] at habs
  refine habs.trans ?_
  exact add_le_add (add_le_add (add_le_add le_rfl
    (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hcov))) le_rfl) le_rfl

end Core

end HRS.Main.A1014
