import HRS.ME.FamUF2
import HRS.MD.EQInitParticle
import HRS.MD.EQInitGauss

/-!
# Chunk E, packet F3 (namespace `HRS.ME.FamU`): V-uniform copies of the initial-momentum bounds

* `eq_init_particle_unifV` (original `HRS.MD.EQInit.eq_init_particle_proof`, HRS/MD/EQInitParticle.lean:49):
  fixed data `d s hs0 hsd βm βp hβm hββ M hM` and `Bf : ℕ → ℝ`; the constant `C` and the thermal density bound
  `Lam` (through `eqstat_thermal_setup_unifV`, F2) are chosen before `V`; the constant `C₀` of
  `eq_static_linear_unifV` (F2) is V-uniform as well.
* `eq_init_gauss_unifV` (original `HRS.MD.EQInit.eq_init_gauss_proof`, HRS/MD/EQInitGauss.lean:104): the
  constant `8 * Σ + 1` was already V-free; the statement only moves `∀ V` behind it (the bound `Bf` is unused).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.ME.FamU

open HRS HRS.MD.EQInit

variable {d : ℕ}

/-- **F3.1** `eq_init_particle`, V-uniform. -/
theorem eq_init_particle_unifV (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (M : ℝ) (hM : (d : ℝ) / 2 < M) (Bf : ℕ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : Torus d → ℝ, Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
    ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
        ∫⁻ X, ‖zetaE M (canonicalGibbs (periodicRiesz d s) V N β) X‖ₑ ^ 2
          ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤ ENNReal.ofReal C := by
  have hM2 : (d : ℝ) < 2 * M := by linarith
  obtain ⟨C₀, hC₀, hC⟩ := HRS.ME.FamU.eq_static_linear_unifV hd hs0 hsd βm βp hβm hββ Bf
  obtain ⟨Lam, hLam⟩ := HRS.ME.FamU.eqstat_thermal_setup_unifV hd hs0 hsd βm βp hβm hββ Bf
  have hSpos : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * M)) :=
    tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos _).le _
  refine ⟨2 * C₀ * (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * M))) + 1, by positivity, ?_⟩
  intro V hV hVB β hβ ρβ hρ N hN
  obtain ⟨hρs, hΛ, hP⟩ := hLam V hV hVB β hβ ρβ hρ
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  haveI hμ : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρs.density
  haveI hPr : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [hP N]
    exact HRS.Q32c.q32c_Q_isProb hd hs0 hsd hβ0 (Λ := max Lam 1) (le_max_right _ _) hρs.density
      (fun x => (hΛ x).trans (le_max_left _ _)) (by omega)
  set P := canonicalGibbs (periodicRiesz d s) V N β with hPdef
  have hmeas : Measurable (zetaE M P) := by
    haveI := isProbabilityMeasure_meanEmpirical P hN1
    exact (measurable_ofMeasureDiff_empirical (m := M) hM2 (meanEmpirical P) hN1).const_smul
      (Real.sqrt N)
  refine (eqinit_lintegral_enorm_sq_le P hM2 (zetaE M P) hmeas (2 * C₀) (by positivity) ?_).trans
    (ENNReal.ofReal_le_ofReal (by linarith))
  intro k
  set f : Torus d → ℝ := Torus.realMode k with hf
  have hfc : Continuous f := continuous_realMode' k
  have hfm : Measurable f := hfc.measurable
  have hf2 : MemLp f 2 (withDensityReal ρβ) :=
    MemLp.of_bound hfc.aestronglyMeasurable (Real.sqrt 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact Torus.abs_realMode_le k x)
  have hint : ∫ x, f x ^ 2 ∂(withDensityReal ρβ) ≤ 2 := by
    have hb : ∀ x, f x ^ 2 ≤ 2 := fun x => by
      have := Torus.abs_realMode_le k x
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      nlinarith [abs_nonneg (f x), sq_abs (f x), Real.sqrt_nonneg 2]
    have := integral_mono hf2.integrable_sq (integrable_const (2 : ℝ)) hb
    simpa using this
  have hev := hC V hV hVB β hβ ρβ hρ N hN f hfm hf2
  have hcoord : ∀ X, ENNReal.ofReal (NegSobolev.coord (zetaE M P X) k ^ 2) =
      ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * M)) * N) *
        ‖pair (empirical X) f - ∫ Y, pair (empirical Y) f ∂P‖ₑ ^ 2 := by
    intro X
    rw [eqinit_coord_zeta hN1 hM2 P X k]
    have hj : (0 : ℝ) ≤ Lattice.jp k.1 ^ (-(2 * M)) := Real.rpow_nonneg (Torus.jp_pos _).le _
    have e1 : (Lattice.jp k.1 ^ (-M) * (Real.sqrt N * (pair (empirical X) f -
        ∫ Y, pair (empirical Y) f ∂P))) ^ 2 =
        Lattice.jp k.1 ^ (-(2 * M)) * N * (pair (empirical X) f - ∫ Y, pair (empirical Y) f ∂P) ^ 2 := by
      have h1 : (Lattice.jp k.1 ^ (-M)) ^ 2 = Lattice.jp k.1 ^ (-(2 * M)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Torus.jp_pos _).le]; congr 1; push_cast; ring
      have h2 : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
      calc _ = (Lattice.jp k.1 ^ (-M)) ^ 2 * Real.sqrt N ^ 2 *
            (pair (empirical X) f - ∫ Y, pair (empirical Y) f ∂P) ^ 2 := by ring
        _ = _ := by rw [h1, h2]
    rw [e1, ENNReal.ofReal_mul (mul_nonneg hj hN0.le)]
    congr 1
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  have hlint : ∫⁻ X, ENNReal.ofReal (NegSobolev.coord (zetaE M P X) k ^ 2) ∂P =
      ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * M)) * N) * evariance (fun X => pair (empirical X) f) P := by
    simp_rw [hcoord]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rfl
  rw [hlint]
  have hj : (0 : ℝ) ≤ Lattice.jp k.1 ^ (-(2 * M)) := Real.rpow_nonneg (Torus.jp_pos _).le _
  calc ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * M)) * N) * evariance (fun X => pair (empirical X) f) P
      ≤ ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * M)) * N) * ENNReal.ofReal (2 * C₀ * (N : ℝ)⁻¹) := by
        gcongr
        refine hev.trans (ENNReal.ofReal_le_ofReal ?_)
        have : 0 ≤ C₀ * (N : ℝ)⁻¹ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hint this]
    _ = ENNReal.ofReal (2 * C₀ * Lattice.jp k.1 ^ (-(2 * M))) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hj hN0.le)]
        congr 1
        field_simp

/-- **F3.2** `eq_init_gauss`, V-uniform: the constant `8 * Σ + 1` is V-free; `∀ V` is moved behind it. -/
theorem eq_init_gauss_unifV (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (M : ℝ) (hM : (d : ℝ) / 2 < M) (Bf : ℕ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : Torus d → ℝ, Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
    ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d M),
        IsStationaryGaussianField P' s β hs0 hsd (hβm.trans_le hβ.1) V ρβ M Z →
        ∫⁻ ω, ‖Z 0 ω‖ₑ ^ 2 ∂P' ≤ ENNReal.ofReal C := by
  have hM2 : (d : ℝ) < 2 * M := by linarith
  have hSpos : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * M)) :=
    tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos _).le _
  refine ⟨8 * (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * M))) + 1, by positivity, ?_⟩
  intro V hV _ β hβ ρβ hρ Ω' _ P' _ Z hZ
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ0 hV hρ
  refine (eqinit_lintegral_enorm_sq_le P' hM2 (Z 0) (hZ.meas 0) 8 (by norm_num) ?_).trans
    (ENNReal.ofReal_le_ofReal (by linarith))
  intro k
  set τ : Fin 2 → ℝ := fun _ => 0 with hτ
  set φ : Fin 2 → Torus d → ℝ := fun _ => Torus.realMode k with hφ
  have hτ0 : ∀ a, 0 ≤ τ a := fun a => le_rfl
  have hφs : ∀ a, Torus.IsSmooth (φ a) := fun _ => q38b_isSmooth_realMode k
  have hlaw := hZ.gaussian 2 τ φ hτ0 hφs
  set W : Ω' → EuclideanSpace ℝ (Fin 2) := fun ω =>
    (WithLp.toLp 2 fun a => NegSobolev.eval (Z (τ a) ω) (φ a) : EuclideanSpace ℝ (Fin 2)) with hW
  have hmeas : ∀ a : Fin 2, Measurable fun ω => NegSobolev.eval (Z (τ a) ω) (φ a) :=
    fun a => (q38b_measurable_eval_realMode k).comp (hZ.meas (τ a))
  have hWm : Measurable W :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.comp (measurable_pi_iff.2 hmeas)
  have hpsd := Q41.q41_lagcov_psd hd hs0 hsd hβ0 hV hρ
    (PoleCavityAux.continuous_of_smoothPos ⟨hρ.1, hsm, hpos⟩) hpos τ hτ0 φ hφs
  have hS01 : PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ0) ρβ τ φ 0 1 =
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β (Torus.realMode k)
        (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ0) ρβ 0 (Torus.realMode k)) := by
    simp [PDE.stationaryLagCov, τ, φ]
  have hle := eqinit_susc_semigroup_zero_le hd hs0 hsd β hβ0 V hV ρβ hρ k
  have hint := eqinit_gauss_prod_integrable P' W hWm.aemeasurable _ hlaw
  have hval := q38b_gauss_prod P' W hWm.aemeasurable _ hpsd hlaw
  have hsq : ∀ ω, W ω 0 * W ω 1 = NegSobolev.eval (Z 0 ω) (Torus.realMode k) ^ 2 := by
    intro ω; simp [hW, τ, φ, sq]
  have hint2 : Integrable (fun ω => NegSobolev.eval (Z 0 ω) (Torus.realMode k) ^ 2) P' := by
    simpa [hsq] using hint
  have hval2 : ∫ ω, NegSobolev.eval (Z 0 ω) (Torus.realMode k) ^ 2 ∂P' ≤ 8 := by
    simp_rw [hsq] at hval
    rw [hval, hS01]; exact hle
  have hcoord : ∀ ω, NegSobolev.coord (Z 0 ω) k ^ 2 =
      Lattice.jp k.1 ^ (-(2 * M)) * NegSobolev.eval (Z 0 ω) (Torus.realMode k) ^ 2 := by
    intro ω
    rw [q38b_eval_realMode]
    unfold NegSobolev.fourierCoeff
    have hj := Torus.jp_pos k.1
    have h1 : Lattice.jp k.1 ^ (-(2 * M)) * (Lattice.jp k.1 ^ M * NegSobolev.coord (Z 0 ω) k) ^ 2 =
        (Lattice.jp k.1 ^ (-(2 * M)) * (Lattice.jp k.1 ^ M) ^ 2) * NegSobolev.coord (Z 0 ω) k ^ 2 := by
      ring
    have h2 : Lattice.jp k.1 ^ (-(2 * M)) * (Lattice.jp k.1 ^ M) ^ 2 = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hj.le, ← Real.rpow_add hj]
      have : -(2 * M) + M * ((2 : ℕ) : ℝ) = 0 := by push_cast; ring
      rw [this, Real.rpow_zero]
    rw [h1, h2, one_mul]
  have hj0 : (0 : ℝ) ≤ Lattice.jp k.1 ^ (-(2 * M)) := Real.rpow_nonneg (Torus.jp_pos _).le _
  have hlint : ∫⁻ ω, ENNReal.ofReal (NegSobolev.coord (Z 0 ω) k ^ 2) ∂P' =
      ENNReal.ofReal (Lattice.jp k.1 ^ (-(2 * M)) *
        ∫ ω, NegSobolev.eval (Z 0 ω) (Torus.realMode k) ^ 2 ∂P') := by
    simp_rw [hcoord]
    rw [← integral_const_mul]
    rw [ofReal_integral_eq_lintegral_ofReal (hint2.const_mul _)
      (Filter.Eventually.of_forall fun ω => mul_nonneg hj0 (sq_nonneg _))]
  rw [hlint]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [mul_le_mul_of_nonneg_left hval2 hj0]

end HRS.ME.FamU

end
