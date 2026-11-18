import HRS.Main.EqBiasAux1

/-!
# EQ-BIAS / EQ-POS, S2: operator theory at `μ = ρ dx`

* `eqbias_KS`: the Schur-test hypotheses `MFLinear.KS` for `g = periodicRiesz d s`, `s < d`.
* `eqbias_Kop_nonneg`, `eqbias_coercive`: `⟨w, K w⟩ ≥ 0` and `‖w‖² ≤ ⟨w, w + βKw⟩` for `w ∈ L²_0(μ)`.
* `eqbias_response`: `responseInverse` is an `IsResponse` solution.
* `eqbias_bias_pos`: `⟨h, ρ⟩ > 0` for the response `h` of a continuous nonconstant density
  (`A:eq:strict-coefficient`), the content of `supercriticalBias_pos`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

open HRS.PDE

/-- The Schur-test hypotheses for the periodic Riesz kernel and a smooth positive density. -/
theorem eqbias_KS (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) : ∃ Λ : ℝ, MFLinear.KS (periodicRiesz d s) ρ Λ := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  exact ⟨Λ, ⟨MFOneLe.integrable_periodicRiesz (by omega) s hs0 hsd,
    fun x => periodicRiesz_neg x, hρ.density, hΛ⟩⟩

theorem eqbias_cont {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) : Continuous ρ :=
  PoleCavityAux.continuous_of_smoothPos hρ

/-- `⟨K w, w⟩ ≥ 0` for centered `w ∈ L²(μ)`. -/
theorem eqbias_Kop_nonneg (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {w : Torus d → ℝ} (hm : MemLp w 2 (withDensityReal ρ))
    (hp : pair (withDensityReal ρ) w = 0) :
    0 ≤ l2Inner (withDensityReal ρ) (Kop (periodicRiesz d s) (withDensityReal ρ) w) w := by
  obtain ⟨Λ, H⟩ := eqbias_KS hd hs0 hsd hρ
  have hρc := eqbias_cont hρ
  set u : Lp ℝ 2 (withDensityReal ρ) := hm.toLp w with hu
  have huw : ⇑u =ᵐ[withDensityReal ρ] w := MemLp.coeFn_toLp hm
  have hpu : pair (withDensityReal ρ) ⇑u = 0 := (integral_congr_ae huw).trans hp
  have hnn := MFLinear.TLp_inner_nonneg (by omega) s hs0 hsd H hρc u
  rw [MFLinear.inner_TLp_eq_l2Inner] at hnn
  refine le_of_le_of_eq hnn ?_
  unfold l2Inner
  refine integral_congr_ae ?_
  have hproj : MFLinear.projMean_of_pair_zero hpu = MFLinear.projMean_of_pair_zero hpu := rfl
  filter_upwards [huw] with x hx
  rw [MFLinear.projMean_of_pair_zero hpu, MFLinear.Kop_congr huw, hx]

/-- Coercivity of `I + βK` on `L²_0(μ)`. -/
theorem eqbias_coercive (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {β : ℝ} (hβ : 0 ≤ β) {w : Torus d → ℝ}
    (hm : MemLp w 2 (withDensityReal ρ)) (hp : pair (withDensityReal ρ) w = 0) :
    ∫ x, w x ^ 2 ∂(withDensityReal ρ) ≤
      l2Inner (withDensityReal ρ) w
        (fun x => w x + β * Kop (periodicRiesz d s) (withDensityReal ρ) w x) := by
  obtain ⟨Λ, H⟩ := eqbias_KS hd hs0 hsd hρ
  have hP := H.isProb
  have hK := eqbias_Kop_nonneg hd hs0 hsd hρ hm hp
  have hKm := (MFLinear.memLp_Kop H hm).1
  have h1 : Integrable (fun x => w x * w x) (withDensityReal ρ) := hm.integrable_mul hm
  have h2 : Integrable (fun x => Kop (periodicRiesz d s) (withDensityReal ρ) w x * w x)
      (withDensityReal ρ) := hKm.integrable_mul hm
  unfold l2Inner at hK ⊢
  have e : ∫ x, w x * (w x + β * Kop (periodicRiesz d s) (withDensityReal ρ) w x)
        ∂(withDensityReal ρ) =
      ∫ x, w x * w x ∂(withDensityReal ρ) +
        β * ∫ x, Kop (periodicRiesz d s) (withDensityReal ρ) w x * w x ∂(withDensityReal ρ) := by
    have hpt : ∀ x, w x * (w x + β * Kop (periodicRiesz d s) (withDensityReal ρ) w x) =
        w x * w x + β * (Kop (periodicRiesz d s) (withDensityReal ρ) w x * w x) :=
      fun x => by ring
    simp_rw [hpt]
    rw [integral_add h1 (h2.const_mul β), integral_const_mul]
  rw [e]
  have : ∫ x, w x ^ 2 ∂(withDensityReal ρ) = ∫ x, w x * w x ∂(withDensityReal ρ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
  rw [this]
  nlinarith [mul_nonneg hβ hK]

/-- A response solution exists for the density `ρ` itself, and `responseInverse` is one. -/
theorem eqbias_response (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {β : ℝ} (hβ : 0 ≤ β) :
    IsResponse (periodicRiesz d s) (withDensityReal ρ) β ρ
      (responseInverse (periodicRiesz d s) (withDensityReal ρ) β ρ) := by
  have hP := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  have hψ : MemLp ρ 2 (withDensityReal ρ) :=
    MemLp.of_bound (eqbias_cont hρ).aestronglyMeasurable Λ
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (hρ.pos x)]; exact hΛ x)
  obtain ⟨h, hh, -⟩ := MFLinear.exists_unique_response_of_one_le (by omega) s hs0 hsd ρ hρ.density
    (eqbias_cont hρ) β hβ ρ hψ
  have hex : ∃ h, IsResponse (periodicRiesz d s) (withDensityReal ρ) β ρ h := ⟨h, hh⟩
  unfold responseInverse
  rw [dif_pos hex]
  exact hex.choose_spec

theorem eqbias_memLp_rho {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    MemLp ρ 2 (withDensityReal ρ) := by
  have hP := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  exact MemLp.of_bound (eqbias_cont hρ).aestronglyMeasurable Λ
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (hρ.pos x)]; exact hΛ x)

/-- `⟨h, ρ⟩_{L²(μ)} > 0` for the response `h = R P ρ` of a nonconstant smooth positive density
(`A:eq:strict-coefficient`). -/
theorem eqbias_bias_pos (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {β : ℝ} (hβ : 0 ≤ β) (hnc : ∃ x y, ρ x ≠ ρ y) :
    0 < ∫ x, responseInverse (periodicRiesz d s) (withDensityReal ρ) β ρ x * ρ x
      ∂(withDensityReal ρ) := by
  have hP := PoleCavityAux.isProbabilityMeasure_mu hρ
  set μ := withDensityReal ρ with hμ
  set h := responseInverse (periodicRiesz d s) μ β ρ with hh
  obtain ⟨hm, hp, he⟩ : MemLp h 2 μ ∧ pair μ h = 0 ∧
      ∀ᵐ x ∂μ, h x + β * Kop (periodicRiesz d s) μ h x = projMean μ ρ x :=
    eqbias_response hd hs0 hsd hρ hβ
  have hcoer := eqbias_coercive hd hs0 hsd hρ hβ hm hp
  have hρm := eqbias_memLp_rho hρ
  have hhi : Integrable h μ := hm.integrable one_le_two
  have hhρ : Integrable (fun x => h x * ρ x) μ := hm.integrable_mul hρm
  have hl2 : l2Inner μ h (fun x => h x + β * Kop (periodicRiesz d s) μ h x) =
      ∫ x, h x * ρ x ∂μ := by
    unfold l2Inner
    have : ∫ x, h x * (h x + β * Kop (periodicRiesz d s) μ h x) ∂μ =
        ∫ x, h x * projMean μ ρ x ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [he] with x hx
      rw [hx]
    rw [this]
    have hpt : ∀ x, h x * projMean μ ρ x = h x * ρ x - pair μ ρ * h x := fun x => by
      unfold projMean; ring
    simp_rw [hpt]
    rw [integral_sub hhρ (hhi.const_mul _), integral_const_mul]
    have : ∫ x, h x ∂μ = 0 := hp
    rw [this]; ring
  rw [hl2] at hcoer
  have hh2 : Integrable (fun x => h x ^ 2) μ := hm.integrable_sq
  have hnn : 0 ≤ ∫ x, h x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  refine lt_of_lt_of_le ?_ hcoer
  refine lt_of_le_of_ne hnn fun h0 => ?_
  have hz : (fun x => h x ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hh2).1 h0.symm
  have hh0 : h =ᵐ[μ] 0 := by
    filter_upwards [hz] with x hx
    simpa using hx
  have hK0 : Kop (periodicRiesz d s) μ h = Kop (periodicRiesz d s) μ 0 :=
    (eqbias_KS hd hs0 hsd hρ).elim fun Λ H => MFLinear.Kop_congr hh0
  have hK00 : Kop (periodicRiesz d s) μ (0 : Torus d → ℝ) = 0 := by
    funext x
    simp [Kop, projMean, pair]
  have hρc : ∀ᵐ x ∂μ, ρ x = pair μ ρ := by
    filter_upwards [he, hh0] with x hx h0x
    rw [hK0, hK00] at hx
    simp only [h0x, Pi.zero_apply, mul_zero, add_zero] at hx
    unfold projMean at hx
    linarith
  have hac : (volume : Measure (Torus d)) ≪ μ :=
    withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp
      hρ.density.measurable).aemeasurable
      (Filter.Eventually.of_forall fun x => (ENNReal.ofReal_pos.2 (hρ.pos x)).ne')
  have hρv : ρ =ᵐ[volume] fun _ => pair μ ρ := hac hρc
  have hfun : ρ = fun _ => pair μ ρ :=
    (Continuous.ae_eq_iff_eq (volume : Measure (Torus d)) (eqbias_cont hρ) continuous_const).1 hρv
  obtain ⟨x, y, hxy⟩ := hnc
  exact hxy (by rw [hfun])

end Main

end HRS

end
