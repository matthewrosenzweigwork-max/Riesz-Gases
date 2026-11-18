/-
# HRS.Equilibrium.PairMoments -- Proposition 4.12 (`M:Q:prop:moments`), proved (packet EQ-01b-moments)

`pair_moments_proof` restates `HRS.pair_moments` with a proof: the statement is verbatim that of
`PairCorrection.lean` (checked by `example := (@pair_moments_proof : type_of% @pair_moments)` in the
packet scratch file).  Route: `P_{N,β} = Q_{N,β}(μ_β)`, domination by the calibrated reference `R_N`
(`Q ≤ K R_N` for `N ≥ N₁`, a crude `Q ≤ K'_N R_N` below), single-site resampling (Wu) for pinned laws,
row moments via Lemma 4.10 (refined one- and two-pin marginal densities), the envelope integrals of
Lemma 4.11, and for the energy term the a.e. centring of `∇_xψ` obtained by differentiating
`∫ψ(x,y) μ(dy) = 0` along lines (FTC + Fubini + Lebesgue differentiation).
-/
import HRS.Equilibrium.PairMomentsEnergy
import HRS.Energy.Coercivity

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

variable {d : ℕ} {s : ℝ}

open HRS.PairMom

/-- Proposition 4.12 `M:Q:prop:moments` (source lines 4607-4636), under `P_{N,β}`, with
constants homogeneous quadratic in the kernel bound `K`. -/
theorem pair_moments_proof (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∃ C₀ : ℝ,
      (∀ (K : ℝ) (ψ : Torus d → Torus d → ℝ), Measurable (Function.uncurry ψ) → IsSymmPair ψ →
        IsCanonicalPair (withDensityReal ρ) ψ → PsiSize s K ψ → ∀ N : ℕ, 2 ≤ N →
          evariance (Fstat ψ) (canonicalGibbs (periodicRiesz d s) V N β) +
              ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
                ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
            ENNReal.ofReal (C₀ * K ^ 2 / N)) ∧
      (∀ (K : ℝ) (j : Torus d → Torus d → ℝ), Measurable (Function.uncurry j) → IsSymmPair j →
        IsCanonicalPair (withDensityReal ρ) j → (∀ x y, x ≠ y → |j x y| ≤ K * wEnv s x y) →
        ∀ N : ℕ, 2 ≤ N →
          evariance (Fstat j) (canonicalGibbs (periodicRiesz d s) V N β) ≤
            ENNReal.ofReal (C₀ * K ^ 2 * logEN N / N)) ∧
      (∀ (K : ℝ) (b : Torus d → Torus d → ℝ), Measurable (Function.uncurry b) → IsSymmPair b →
        (∀ x y, x ≠ y → |b x y| ≤ K * wEnv s x y ^ 2) → ∀ N : ℕ, 2 ≤ N →
          evariance (fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered b X)
              (canonicalGibbs (periodicRiesz d s) V N β) ≤
            ENNReal.ofReal (C₀ * K ^ 2 / N)) ∧
      (∀ (K : ℝ) (g3 : Torus d → Torus d → Torus d → ℝ),
        Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) →
        IsSymmTriple g3 → IsCanonicalTriple (withDensityReal ρ) g3 →
        (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤
          K * (wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z)) →
        ∀ N : ℕ, 2 ≤ N →
          evariance (fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum g3 X)
              (canonicalGibbs (periodicRiesz d s) V N β) ≤
            ENNReal.ofReal (C₀ * K ^ 2 * logEN N ^ 2 / (N : ℝ) ^ 2)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρs
  have hP : ∀ N : ℕ, canonicalGibbs (periodicRiesz d s) V N β =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) := by
    intro N
    refine canonicalGibbs_eq_modulatedGibbs (periodicRiesz d s) V β ρ hρ (fun x => periodicRiesz_neg x) ?_
    intro x
    exact (CoercAux.J_bounds (by omega : 1 ≤ d) hs0 hsd one_pos hρ.1 hΛ0.le hΛ x).1
  obtain ⟨Cψ, hCψ0, hCψ⟩ := partpsi_all hd hcrit β hβ ρ hρs
  obtain ⟨Ce, hCe0, hCe⟩ := energy_all hd hcrit β hβ ρ hρs
  obtain ⟨Cj, hCj0, hCj⟩ := partj_all hd hcrit β hβ ρ hρs
  obtain ⟨Cb, hCb0, hCb⟩ := partb_all hd hcrit β hβ ρ hρs
  obtain ⟨Ct, hCt0, hCt⟩ := partt_all hd hcrit β hβ ρ hρs
  refine ⟨Cψ + Ce + Cj + Cb + Ct, ?_, ?_, ?_, ?_⟩
  · intro K ψ hm hsymm hcan hsz N hN
    rw [hP N]
    have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have h1 := hCψ K ψ hm hsymm hcan (fun x y hxy => hsz.size x y hxy) N hN
    have h2 := hCe K ψ hsymm hcan hsz.smooth hsz.grad N hN
    calc evariance (Fstat ψ) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) +
          ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
            ∂(modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))
        ≤ ENNReal.ofReal (Cψ * K ^ 2 / N) + ENNReal.ofReal (Ce * K ^ 2 / N) := add_le_add h1 h2
      _ = ENNReal.ofReal ((Cψ + Ce) * K ^ 2 / N) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          refine div_le_div_of_nonneg_right ?_ hNp.le
          exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg K)
  · intro K j hm hsymm hcan hj N hN
    rw [hP N]
    have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hL := logEN_pos' (N := N) (by omega)
    refine (hCj K j hm hsymm hcan hj N hN).trans (ENNReal.ofReal_le_ofReal ?_)
    refine div_le_div_of_nonneg_right ?_ hNp.le
    have : 0 ≤ K ^ 2 * logEN N := by positivity
    nlinarith [mul_le_mul_of_nonneg_right (show Cj ≤ Cψ + Ce + Cj + Cb + Ct by linarith) this]
  · intro K b hm hsymm hb N hN
    rw [hP N]
    have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    refine (hCb K b hm hsymm hb N hN).trans (ENNReal.ofReal_le_ofReal ?_)
    refine div_le_div_of_nonneg_right ?_ hNp.le
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg K)
  · intro K g3 hm hsymm hcan hg3 N hN
    rw [hP N]
    have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hL := logEN_pos' (N := N) (by omega)
    refine (hCt K g3 hm hsymm hcan hg3 N hN).trans (ENNReal.ofReal_le_ofReal ?_)
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have : 0 ≤ K ^ 2 * logEN N ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right (show Ct ≤ Cψ + Ce + Cj + Cb + Ct by linarith) this]

end HRS

end
