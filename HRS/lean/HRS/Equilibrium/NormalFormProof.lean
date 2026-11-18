/-
# HRS.Equilibrium.NormalFormProof — packet Q84e: assembly of Proposition 4.16 (`normal_form`)

`normal_form_proof` has the statement of the frozen `HRS.normal_form` (PairCorrection.lean),
checked by the final `example`.  Route (source lines 4936-4971):

* integrability conjuncts: `Q84d.q84d_quadStat_integrable`, `q84d_Fstat_integrable`,
  `q84d_errStat_integrable`;
* the identity with the actual stationary centring: the algebraic lifted generator identity
  `Q84e.q84e_gen_alg` (finite-particle corrections), the Poisson equation in the form
  `B_x ψ + B_y ψ + 𝒥ψ = -H_f` (`Q84e.q84e_poisson_red`, using `μ(Bψ(·,y)) = 0`), the deleted-sum
  expansion `Q84e.q84e_quad_alg`, stationarity `q84d_stationarity`, centred in
  `Q84e.q84e_identity_centered`;
* the `L²` bound: `pair_moments_proof` on `ψ`, on the modified kernels `Jt, Gt, Bt`
  (`Q84e.q84e_modified_kernels_unif`) and `q84d_zeta_bound`, with `Q84e.q84e_err_L2` and
  `Q84e.q84e_arith`.
-/
import HRS.Equilibrium.TripleCanonical
import HRS.Equilibrium.Q84dStationary
import HRS.Equilibrium.PairMoments
import HRS.Equilibrium.Q84eAuxI
import HRS.Equilibrium.Q84eAuxM

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ} {s : ℝ}

theorem normal_form_proof (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∃ C : ℝ, ∀ (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ), Torus.IsSmooth f →
      IsPairCorrector d s V β ρ f K₁ ψ → ∀ N : ℕ, 2 ≤ N →
        Integrable (quadStat (hTransport d s f) (withDensityReal ρ))
            (canonicalGibbs (periodicRiesz d s) V N β) ∧
        Integrable (Fstat (N := N) ψ) (canonicalGibbs (periodicRiesz d s) V N β) ∧
        Integrable (errStat d s ρ (N := N) ψ) (canonicalGibbs (periodicRiesz d s) V N β) ∧
        (∀ X : Config d N, X ∉ collisionSet d N →
          Real.sqrt N / 2 * centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
              (quadStat (hTransport d s f) (withDensityReal ρ)) X =
            -particleGen d s V β (Fstat ψ) X +
              centeredUnder (canonicalGibbs (periodicRiesz d s) V N β) (errStat d s ρ ψ) X -
              (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
                (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρ f (Y i)) X)) ∧
        eLpNorm (centeredUnder (canonicalGibbs (periodicRiesz d s) V N β) (Fstat ψ)) 2
              (canonicalGibbs (periodicRiesz d s) V N β) +
            (∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
              ∂(canonicalGibbs (periodicRiesz d s) V N β)) ^ (1 / 2 : ℝ) +
            eLpNorm (centeredUnder (canonicalGibbs (periodicRiesz d s) V N β) (errStat d s ρ ψ)) 2
              (canonicalGibbs (periodicRiesz d s) V N β) +
            ENNReal.ofReal (1 / (N : ℝ)) *
              eLpNorm (fun X : Config d N => Real.sqrt N *
                  centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
                    (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρ f (Y i)) X) 2
                (canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal (C * (K₁ + posSeminorm (8 * d + 80) f) * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨C₀, hPM1, hPM2, hPM3, hPM4⟩ := pair_moments_proof hd hcrit β hβ V hV ρ hρ hρs
  obtain ⟨Cu, hCu0, hCu⟩ := Q84e.q84e_modified_kernels_unif hd hcrit β hβ V hV ρ hρ hρs
  obtain ⟨Cz, hCz0, hCz⟩ := Q84d.q84d_zeta_bound hd hcrit β hβ V hV ρ hρ hρs
  obtain ⟨C3, hC3⟩ := triple_canonical_proof hd hcrit β hβ V hV ρ hρ hρs
  set c0 : ℝ := Real.sqrt (max C₀ 0) with hc0def
  have hc0 : 0 ≤ c0 := Real.sqrt_nonneg _
  have hc0sq : c0 ^ 2 = max C₀ 0 := Real.sq_sqrt (le_max_right _ _)
  refine ⟨4 * c0 + 3 * c0 * Cu + Cz, fun f K₁ ψ hf hψ N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  haveI := Q84d.q84d_isProb hd hcrit hV hβ hN1 (N := N)
  set P := canonicalGibbs (periodicRiesz d s) V N β with hP
  have hK₁ := Q84d.q84d_K_nonneg hd hcrit hψ
  have hD := Q84d.q84d_posSeminorm_nonneg (8 * d + 80) f
  refine ⟨Q84d.q84d_quadStat_integrable hd hcrit β hβ V hV ρ hρ hρs f hf N hN,
    Q84d.q84d_Fstat_integrable hd hcrit β hβ V hV ρ hρ hρs f K₁ ψ hf hψ N hN,
    Q84d.q84d_errStat_integrable hd hcrit β hβ V hV ρ hρ hρs f K₁ ψ hf hψ N hN,
    Q84e.q84e_identity_centered hd hcrit hβ hV hρ hρs hf hψ hN, ?_⟩
  -- the kernels
  obtain ⟨-, hGcan, -, -, -⟩ := hC3 f K₁ ψ hf hψ
  obtain ⟨Jt, Bt, Gt, ⟨hJm, hJs, hJc, hJb⟩, ⟨hBm, hBs, hBb⟩, ⟨hGm, hGs, hGc, hGb⟩, hae⟩ :=
    hCu f K₁ ψ hf hψ hGcan
  -- variance bounds
  have hlog := Q84e.q84e_logEN_pos hN1
  have v1 := hPM1 K₁ ψ hψ.measurable hψ.symm hψ.canonical hψ.size N hN
  have v2 := hPM2 K₁ Jt hJm hJs hJc hJb N hN
  have v3 := hPM3 (Cu * K₁) Bt hBm hBs hBb N hN
  have v4 := hPM4 (Cu * K₁) Gt hGm hGs hGc hGb N hN
  have hmax : ∀ x : ℝ, 0 ≤ x → C₀ * x ≤ c0 ^ 2 * x := fun x hx =>
    mul_le_mul_of_nonneg_right (by rw [hc0sq]; exact le_max_left _ _) hx
  set a₁ : ℝ := c0 ^ 2 * K₁ ^ 2 / N with ha₁
  have ha₁0 : 0 ≤ a₁ := by positivity
  have w1 : evariance (Fstat ψ) P + ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal a₁ := by
    refine v1.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [ha₁]
    refine div_le_div_of_nonneg_right ?_ hNp.le
    have := hmax (K₁ ^ 2) (sq_nonneg _)
    linarith
  have hFψm : AEStronglyMeasurable (Fstat (N := N) ψ) P :=
    (Q84e.q84e_measurable_Fstat hψ.measurable).aestronglyMeasurable
  have T1 : eLpNorm (centeredUnder P (Fstat ψ)) 2 P ≤ ENNReal.ofReal (Real.sqrt a₁) :=
    Q84e.q84e_eLp_center_le P hFψm a₁ ha₁0 (le_trans le_self_add w1)
  have T2 : (∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt a₁) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ha₁0 (by norm_num)]
    exact ENNReal.rpow_le_rpow (le_trans le_add_self w1) (by norm_num)
  -- the error statistic
  set aJ : ℝ := c0 ^ 2 * K₁ ^ 2 * logEN N / N with haJ
  set aT : ℝ := c0 ^ 2 * (Cu * K₁) ^ 2 * logEN N ^ 2 / (N : ℝ) ^ 2 with haT
  set aB : ℝ := c0 ^ 2 * (Cu * K₁) ^ 2 / N with haB
  have haJ0 : 0 ≤ aJ := by positivity
  have haT0 : 0 ≤ aT := by positivity
  have haB0 : 0 ≤ aB := by positivity
  have wJ : evariance (Fstat Jt) P ≤ ENNReal.ofReal aJ := by
    refine v2.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [haJ]
    refine div_le_div_of_nonneg_right ?_ hNp.le
    have := hmax (K₁ ^ 2 * logEN N) (by positivity)
    linarith
  have wT : evariance (fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum Gt X) P ≤
      ENNReal.ofReal aT := by
    refine v4.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [haT]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have := hmax ((Cu * K₁) ^ 2 * logEN N ^ 2) (by positivity)
    linarith
  have wB : evariance (fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered Bt X) P ≤
      ENNReal.ofReal aB := by
    refine v3.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [haB]
    refine div_le_div_of_nonneg_right ?_ hNp.le
    have := hmax ((Cu * K₁) ^ 2) (sq_nonneg _)
    linarith
  have T3 : eLpNorm (centeredUnder P (errStat d s ρ ψ)) 2 P ≤
      ENNReal.ofReal (|2 / (N : ℝ)| * Real.sqrt aJ + Real.sqrt aT + Real.sqrt aB) :=
    Q84e.q84e_err_L2 P (E := errStat d s ρ (N := N) ψ) (FJ := Fstat Jt)
      (T := fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum Gt X)
      (B := fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered Bt X)
      (c1 := 2 / (N : ℝ)) haJ0 haT0 haB0 (hae N hN)
      (Q84e.q84e_measurable_Fstat hJm).aestronglyMeasurable
      (Q84e.q84e_measurable_scaledTriple hGm _).aestronglyMeasurable
      (Q84e.q84e_measurable_scaledPair hBm _).aestronglyMeasurable wJ wT wB
  have T4 := hCz f hf N hN
  -- arithmetic
  have harith := Q84e.q84e_arith hN1 hc0 hK₁ hCu0 hD hCz0
  calc _ ≤ ENNReal.ofReal (Real.sqrt a₁) + ENNReal.ofReal (Real.sqrt a₁) +
        ENNReal.ofReal (|2 / (N : ℝ)| * Real.sqrt aJ + Real.sqrt aT + Real.sqrt aB) +
        ENNReal.ofReal (Cz * posSeminorm (8 * d + 80) f * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
        gcongr
    _ = ENNReal.ofReal (Real.sqrt a₁ + Real.sqrt a₁ +
          (|2 / (N : ℝ)| * Real.sqrt aJ + Real.sqrt aT + Real.sqrt aB) +
          Cz * posSeminorm (8 * d + 80) f * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
        have hz : 0 ≤ Cz * posSeminorm (8 * d + 80) f * (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
          mul_nonneg (mul_nonneg hCz0 hD) (Real.rpow_nonneg hNp.le _)
        have hsum : 0 ≤ |2 / (N : ℝ)| * Real.sqrt aJ + Real.sqrt aT + Real.sqrt aB := by positivity
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) hsum, ← ENNReal.ofReal_add (by positivity) hz]
    _ ≤ _ := ENNReal.ofReal_le_ofReal harith

end HRS

namespace HRS

example := (@normal_form_proof : type_of% @HRS.normal_form)

end HRS

end
