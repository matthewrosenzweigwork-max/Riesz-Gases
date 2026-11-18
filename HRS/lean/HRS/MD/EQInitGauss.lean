import HRS.MD.EQInitBase
import HRS.MD.EQStatQuadratic
import HRS.Sections.Q41Aux20
import HRS.PDE.MeanField
import HRS.Equilibrium.ResponseVariance
import HRS.Sections.Sec3

/-!
# EQ-INITMOM (Gaussian): `eq_init_gauss`

`E‖Z_β^0‖²_{E_M} ≤ C_M` for every stationary Gaussian field.  Coordinatewise `E ⟨Z^0,e_k⟩² = C_β(e_k,e_k) ≤ ‖P_μ e_k‖²_{L²(μ)} ≤ 8`
(`susceptibilityCov_le_variance`, the contraction property of the response inverse), then sum `⟨k⟩^{-2M}`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQInit

variable {d : ℕ}

/-- A centred Gaussian vector in `ℝ²`: the product of coordinates is integrable. -/
theorem eqinit_gauss_prod_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : Ω → EuclideanSpace ℝ (Fin 2)) (hW : AEMeasurable W P) (S : Matrix (Fin 2) (Fin 2) ℝ)
    (h : Measure.map W P = multivariateGaussian 0 S) :
    Integrable (fun ω => W ω 0 * W ω 1) P := by
  have hmem : ∀ i : Fin 2, MemLp (fun x : EuclideanSpace ℝ (Fin 2) => x i) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S) := by
    intro i
    have := (IsGaussian.memLp_two_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S))
    exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).comp_memLp' this
  have hi : Integrable (fun x : EuclideanSpace ℝ (Fin 2) => x 0 * x 1)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) S) := (hmem 0).integrable_mul (hmem 1)
  rw [← h] at hi
  exact (integrable_map_measure hi.aestronglyMeasurable hW).1 hi

theorem eqinit_projMean_idem {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (ψ : Torus d → ℝ) :
    projMean μ (projMean μ ψ) = projMean μ ψ := by
  funext x
  unfold projMean
  have := PDE.MFSemigroup.pair_projMean μ ψ
  unfold projMean at this
  rw [this, sub_zero]

theorem eqinit_responseInverse_projMean {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (g : Torus d → ℝ) (β : ℝ) (ψ : Torus d → ℝ) :
    responseInverse g μ β (projMean μ ψ) = responseInverse g μ β ψ := by
  have hI : IsResponse g μ β (projMean μ ψ) = IsResponse g μ β ψ := by
    funext h
    unfold IsResponse
    rw [eqinit_projMean_idem]
  unfold responseInverse
  rw [hI]

theorem eqinit_susc_semigroup_zero_le (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (k : NonzeroLattice d) :
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β (Torus.realMode k)
      (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ 0 (Torus.realMode k)) ≤ 8 := by
  obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ hV hρβ
  have hρs : SmoothPosDensity ρβ := ⟨hρβ.1, hsm, hpos⟩
  have hμ : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρβ.1
  obtain ⟨Λ, -, hΛ⟩ := PoleCavityAux.exists_density_bound hρs
  have h0 := (PDE.equilibriumSemigroup_generator (by omega) s hs0 hsd β hβ V hV ρβ hρβ hsm hpos
    (Torus.realMode k) (q38b_isSmooth_realMode k)).1
  rw [h0]
  unfold susceptibilityCov
  rw [eqinit_responseInverse_projMean]
  have hφc : Continuous (Torus.realMode k) := continuous_realMode' k
  have hφL2 : MemLp (Torus.realMode k) 2 (withDensityReal ρβ) :=
    MemLp.of_bound hφc.aestronglyMeasurable (Real.sqrt 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact Torus.abs_realMode_le k x)
  have hle := susceptibilityCov_le_variance hd hs0 hsd ρβ hρβ.1 Λ hΛ β hβ.le (Torus.realMode k) hφL2
  unfold susceptibilityCov at hle
  refine hle.trans ?_
  unfold l2Inner
  have hm : |pair (withDensityReal ρβ) (Torus.realMode k)| ≤ Real.sqrt 2 := by
    have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρβ) (f := Torus.realMode k)
      (C := Real.sqrt 2) (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact Torus.abs_realMode_le k x)
    simpa [pair, Measure.real] using this
  have hb : ∀ x, |projMean (withDensityReal ρβ) (Torus.realMode k) x *
      projMean (withDensityReal ρβ) (Torus.realMode k) x| ≤ 8 := by
    intro x
    have h1 := Torus.abs_realMode_le k x
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h3 : |projMean (withDensityReal ρβ) (Torus.realMode k) x| ≤ 2 * Real.sqrt 2 := by
      unfold projMean
      calc _ ≤ |Torus.realMode k x| + |pair (withDensityReal ρβ) (Torus.realMode k)| := abs_sub _ _
        _ ≤ _ := by linarith
    rw [← sq, abs_pow]
    have h4 : 0 ≤ |projMean (withDensityReal ρβ) (Torus.realMode k) x| := abs_nonneg _
    nlinarith [Real.sqrt_nonneg 2]
  have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρβ)
    (f := fun x => projMean (withDensityReal ρβ) (Torus.realMode k) x *
      projMean (withDensityReal ρβ) (Torus.realMode k) x) (C := 8)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] at this
  exact (le_abs_self _).trans this

theorem eq_init_gauss_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (M : ℝ) (hM : (d : ℝ) / 2 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d M),
        IsStationaryGaussianField P' s β hs0 hsd (hβm.trans_le hβ.1) V ρβ M Z →
        ∫⁻ ω, ‖Z 0 ω‖ₑ ^ 2 ∂P' ≤ ENNReal.ofReal C := by
  have hM2 : (d : ℝ) < 2 * M := by linarith
  have hSpos : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * M)) :=
    tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos _).le _
  refine ⟨8 * (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * M))) + 1, by positivity, ?_⟩
  intro β hβ ρβ hρ Ω' _ P' _ Z hZ
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
  have hpsd := Q41.q41_lagcov_psd hd hs0 hsd hβ0 hV hρ (PoleCavityAux.continuous_of_smoothPos ⟨hρ.1, hsm, hpos⟩) hpos τ hτ0 φ hφs
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

end HRS.MD.EQInit
