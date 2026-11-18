import HRS.Main.GFB2Aux5
import HRS.Stochastic.DualityProof

/-!
# Packet GFB2, part 6: the scalar mild identity at the level of `E_m` (`gf_mild_identity`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

theorem gfb2_cbNorm_mono {j K : ℕ} (hjK : j ≤ K) (φ : Torus d → ℝ) :
    Torus.cbNorm j φ ≤ Torus.cbNorm K φ := by
  unfold Torus.cbNorm
  have hnn : ∀ i ∈ Finset.range (K + 1), 0 ≤ ⨆ y : Euc d, ‖iteratedFDeriv ℝ i (Torus.lift φ) y‖ :=
    fun i _ => Real.iSup_nonneg fun y => norm_nonneg _
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun i hi _ => hnn i hi

theorem gfb2_isRegularMF_mono {j K : ℕ} (hjK : j ≤ K) {Λ T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : IsRegularMF K Λ T ρ) : IsRegularMF j Λ T ρ := fun t ht =>
  ⟨by
    have h1 := (h t ht).1
    unfold Torus.IsCk at h1 ⊢
    exact ContDiff.of_le h1 (by exact_mod_cast hjK),
   (gfb2_cbNorm_mono hjK _).trans (h t ht).2⟩

theorem gfb2_propagator_isClassical {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : ℝ} {φ : Torus d → ℝ}
    (h : ∃ f, IsClassicalAdjointSolution D ρ t φ f) :
    IsClassicalAdjointSolution D ρ t φ (fun r => propagator D ρ r t φ) := by
  have e : (fun r => propagator D ρ r t φ) = h.choose := by
    funext r
    unfold propagator
    rw [dif_pos h]
  rw [e]
  exact h.choose_spec

theorem gfb2_eval_flucPair {m : ℝ} (hm : (d : ℝ) < 2 * m) (σ : ℝ) (μ ν : Measure (Torus d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ψ : Torus d → ℝ) (hc : Continuous ψ)
    (hs : Summable fun k : Lattice d => ‖Torus.fcoef ψ k‖) :
    NegSobolev.eval (σ • NegSobolev.ofMeasureDiff m μ ν) ψ = σ * (pair μ ψ - pair ν ψ) := by
  rw [Q54c.eval_smul, NegSobolev.eval_ofMeasureDiff_of_summable hm μ ν ψ hc hs]

theorem gfb2_summable_of_memSobolev {m : ℝ} (hm : (d : ℝ) < 2 * m) {ψ : Torus d → ℝ} (hψ : MemSobolev m ψ) :
    Summable fun k : Lattice d => ‖Torus.fcoef ψ k‖ := by
  obtain ⟨hL2, hs⟩ := hψ
  have hint : Integrable ψ := hL2.integrable one_le_two
  have hmi : (d : ℝ) / 2 + ((0 : ℕ) : ℝ) < m := by push_cast; linarith
  obtain ⟨hsum, -⟩ := Torus.sobolev_coeff_bound hmi hint hs
  simpa using hsum


theorem gf_mild_identity_proof (S : GeneralSetup d) (M : Matrix (Fin d) (Fin d) ℝ) (hMF : S.MFHypM M) (N : ℕ)
    (hN : 2 ≤ N) (m K : ℝ) (hm : (S.γ : ℝ) ≤ m)
    (EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d m)) (hEV : GFEvo S M N m K EV)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStrongSolution P (S.dynM M N) S.T X₀ W X)
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) S.T) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    ∀ᵐ ω ∂P,
      NegSobolev.eval (flucProc m (sigN S N) X (S.ρ N) t ω) φ =
        NegSobolev.eval (EV.VE t 0 (EV.j (flucProc (S.γ : ℝ) (sigN S N) X (S.ρ N) 0 ω))) φ +
        sigN S N * empiricalMartingale P ℱ W' (S.dynM M N) t
          (fun r => propagator (S.dynM M N) (S.ρ N) r t φ) X ((Real.toNNReal t : ℝ≥0) : ℝ) ω +
        sigN S N * ∫ r in (0 : ℝ)..t,
          flucInteraction (S.dynM M N) (propagator (S.dynM M N) (S.ρ N) r t φ)
            (X (Real.toNNReal r) ω) (S.ρ N r) := by
  classical
  have hd1 : 1 ≤ d := by have := S.hd; omega
  haveI : NeZero N := ⟨by omega⟩
  have hm2 := gfb2_two_m hm
  have hγ2 : (d : ℝ) < 2 * (S.γ : ℝ) := gfb2_two_m le_rfl
  obtain ⟨hCk, hMem⟩ := gf_smooth_mem_proof hφ m
  obtain ⟨hMFN, hReg⟩ := hMF N
  have hadj := hEV.adjoint t t ht.1 le_rfl ht.2 φ hCk hMem
  have hf := gfb2_propagator_isClassical hadj.1
  have hadj0 := hEV.adjoint 0 t le_rfl ht.1 ht.2 φ hCk hMem
  have hψ0c : Continuous (propagator (S.dynM M N) (S.ρ N) 0 t φ) :=
    Q54c.isCk_continuous (hf.c2 0 ⟨le_rfl, ht.1⟩)
  have hψ0s := gfb2_summable_of_memSobolev hm2 hadj0.2.1
  have hφc : Continuous φ := Q54c.isCk_continuous hCk
  have hφs := gfb2_summable_of_memSobolev hm2 hMem
  have hV : Torus.IsCk 2 (S.dynM M N).V := by
    have h1 : (2 : WithTop ℕ∞) ≤ ((S.γ + 2 * d + 12 : ℕ) : WithTop ℕ∞) := by
      exact_mod_cast (show 2 ≤ S.γ + 2 * d + 12 by omega)
    exact ContDiff.of_le S.V_reg h1
  have hreg3 : IsRegularMF 3 S.Λ S.T (S.ρ N) := gfb2_isRegularMF_mono (by omega) hReg
  have hkey : ∀ᵐ ω ∂P, flucPair (X (Real.toNNReal t) ω) (S.ρ N t) φ =
      flucPair (X 0 ω) (S.ρ N 0) (propagator (S.dynM M N) (S.ρ N) 0 t φ) +
      empiricalMartingale P ℱ W' (S.dynM M N) t
          (fun r => propagator (S.dynM M N) (S.ρ N) r t φ) X ((Real.toNNReal t : ℝ≥0) : ℝ) ω +
      ∫ r in (0 : ℝ)..t, flucInteraction (S.dynM M N) (propagator (S.dynM M N) (S.ρ N) r t φ)
            (X (Real.toNNReal r) ω) (S.ρ N r) := by
    rcases ht.1.eq_or_lt with h0 | hpos
    · subst h0
      refine Eventually.of_forall fun ω => ?_
      have hterm : propagator (S.dynM M N) (S.ρ N) 0 0 φ = φ := hf.terminal
      rw [hterm]
      have : empiricalMartingale P ℱ W' (S.dynM M N) 0
          (fun r => propagator (S.dynM M N) (S.ρ N) r 0 φ) X ((Real.toNNReal 0 : ℝ≥0) : ℝ) ω = 0 := by
        unfold empiricalMartingale
        exact itoIntegral_of_nonpos P ℱ W' _ (by simp) ω
      rw [this, intervalIntegral.integral_same]
      simp
    · have hdual := duality_identity_all hd1 hN hV hMFN hreg3 hX.toContact hF
        (Or.inr (nullContactOccupation_of_strong hX)) ⟨hpos, ht.2⟩ hCk hf
      filter_upwards [hdual.2] with ω hω
      have h1 := (hω t ⟨ht.1, le_rfl⟩).2
      have hterm : propagator (S.dynM M N) (S.ρ N) t t φ = φ := hf.terminal
      rw [hterm] at h1
      exact h1
  filter_upwards [hkey] with ω hω
  haveI : IsProbabilityMeasure (empirical (X (Real.toNNReal t) ω)) :=
    empirical_isProbabilityMeasure (by omega) _
  haveI : IsProbabilityMeasure (withDensityReal (S.ρ N t)) := isProb_withDensityReal (hMFN.density t ht)
  haveI : IsProbabilityMeasure (empirical (X (Real.toNNReal 0) ω)) :=
    empirical_isProbabilityMeasure (by omega) _
  haveI : IsProbabilityMeasure (empirical (X 0 ω)) := empirical_isProbabilityMeasure (by omega) _
  haveI : IsProbabilityMeasure (withDensityReal (S.ρ N 0)) :=
    isProb_withDensityReal (hMFN.density 0 ⟨le_rfl, S.hT.le⟩)
  have hL : NegSobolev.eval (flucProc m (sigN S N) X (S.ρ N) t ω) φ =
      sigN S N * flucPair (X (Real.toNNReal t) ω) (S.ρ N t) φ := by
    unfold flucProc
    exact gfb2_eval_flucPair hm2 _ _ _ φ hφc hφs
  have hR : NegSobolev.eval (EV.VE t 0 (EV.j (flucProc (S.γ : ℝ) (sigN S N) X (S.ρ N) 0 ω))) φ =
      sigN S N * flucPair (X 0 ω) (S.ρ N 0) (propagator (S.dynM M N) (S.ρ N) 0 t φ) := by
    rw [hEV.dual 0 t le_rfl ht.1 ht.2 _ φ hφ, hEV.j_eq, Q54c.eval_embed hm]
    unfold flucProc
    simp only [Real.toNNReal_zero]
    exact gfb2_eval_flucPair hγ2 _ _ _ _ hψ0c hψ0s
  rw [hL, hR, hω]
  ring

example := (@gf_mild_identity_proof : type_of% @HRS.GF.gf_mild_identity)

end HRS.GF
