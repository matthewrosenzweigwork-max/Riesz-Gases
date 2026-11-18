import HRS.MD.EQInitBase
import HRS.MD.EQStatLinear
import HRS.Equilibrium.Q32cAux2

/-!
# EQ-INITMOM (particle): `eq_init_particle`

`E_{ℙ_{N,β}}‖ζ_N^0‖²_{E_M} ≤ C_M` for `M > d/2`, uniformly in `N ≥ 2`, `β ∈ [β₋,β₊]` and the thermal density.
Coordinatewise: `ζ_k = ⟨k⟩^{-M} √N (μ_N(e_k) - E μ_N(e_k))`, so `E ζ_k² = ⟨k⟩^{-2M} N Var(μ_N(e_k)) ≤ 2C ⟨k⟩^{-2M}`
by `eq_static_linear_proof`; sum over `k`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQInit

variable {d : ℕ}

theorem eqinit_meanEmp_integral {N : ℕ} (hN : 1 ≤ N) (P : Measure (Config d N)) [IsProbabilityMeasure P]
    {f : Torus d → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂(meanEmpirical P) = ∫ Y, pair (empirical Y) f ∂P := by
  rw [integral_meanEmpirical P hf]
  have : ∀ Y : Config d N, pair (empirical Y) f = (N : ℝ)⁻¹ * ∑ i, f (Y i) :=
    fun Y => pair_empirical (by omega) Y f
  simp_rw [this]
  rw [integral_const_mul, integral_finsetSum]
  intro i _
  exact (hf.comp (continuous_apply i)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem eqinit_coord_zeta {N : ℕ} (hN : 1 ≤ N) {M : ℝ} (hM : (d : ℝ) < 2 * M)
    (P : Measure (Config d N)) [IsProbabilityMeasure P] (X : Config d N) (k : NonzeroLattice d) :
    NegSobolev.coord (zetaE M P X) k =
      Lattice.jp k.1 ^ (-M) * (Real.sqrt N * (pair (empirical X) (Torus.realMode k) -
        ∫ Y, pair (empirical Y) (Torus.realMode k) ∂P)) := by
  haveI := empirical_isProbabilityMeasure (by omega : 0 < N) X
  haveI := isProbabilityMeasure_meanEmpirical P hN
  unfold zetaE
  show Real.sqrt N * NegSobolev.coord (NegSobolev.ofMeasureDiff M (empirical X) (meanEmpirical P)) k = _
  rw [coord_ofMeasureDiff hM]
  unfold Torus.measureRealCoeff
  rw [eqinit_meanEmp_integral hN P (continuous_realMode' k)]
  unfold pair
  ring

theorem eq_init_particle_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (M : ℝ) (hM : (d : ℝ) / 2 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
        ∫⁻ X, ‖zetaE M (canonicalGibbs (periodicRiesz d s) V N β) X‖ₑ ^ 2
          ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤ ENNReal.ofReal C := by
  have hM2 : (d : ℝ) < 2 * M := by linarith
  obtain ⟨C₀, hC₀, hC⟩ := MD.EQStat.eq_static_linear_proof hd hs0 hsd V hV βm βp hβm hββ
  obtain ⟨Lam, hLam⟩ := MD.EQStat.eqstat_thermal_setup hd hs0 hsd V hV βm βp hβm hββ
  have hSpos : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * M)) :=
    tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos _).le _
  refine ⟨2 * C₀ * (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * M))) + 1, by positivity, ?_⟩
  intro β hβ ρβ hρ N hN
  obtain ⟨hρs, hΛ, hP⟩ := hLam β hβ ρβ hρ
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
  have hev := hC β hβ ρβ hρ N hN f hfm hf2
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

end HRS.MD.EQInit
