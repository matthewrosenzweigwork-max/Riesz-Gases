import HRS.Main.MixEnt6

/-!
# MIXENT 7: the density of the mixture preparation against `Q_N^0` and its `L^p` moment (lemma M5)

TeX L6957-6962 (the logarithmic `L^p` assumption: "In the integral of `(r_N dμ^{⊗N}/dQ)^{p₀}` under `Q`,
apply Hölder under the product law. Choose `p₀ - 1` sufficiently small that the remaining positive
exponential of `N F_N` is covered by the same small-attractive logarithmic partition bound.
Thus `J_N = O(1)`").

* `mx_pressure_data`: integrability and two-sided bounds of `K_{N,β}`;
* `mx_lintegral_rnDeriv_rpow`: exact identity
  `∫ (dmix/dQ)^p dQ = K^{p-1} ∫ R^p e^{(p-1) β N F_N} dπ`;
* Hölder with exponents `(3/2, 3)` and `log_prep_small_negative` (`s = 0`).
-/

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- The real normaliser `K_{N,β}` of the reference `Q_N^0`. -/
def mxK (S : PreparedData d) (N : ℕ) : ℝ :=
  ∫ X : Config d N, Real.exp (-S.β * N * modulatedEnergyKernel (periodicRiesz d S.s) X S.μ0)
    ∂(Measure.pi fun _ : Fin N => S.μ0)

/-- Pressure data for `Q_N^0` (`t25_press` at `γ = β`): integrability of `e^{-β N F_N}` under `π`
and `exp(-C N δ_N) ≤ K_{N,β} ≤ exp(C N δ_N)`. -/
theorem mx_pressure_data (S : PreparedData d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      Integrable (fun X : Config d N =>
        Real.exp (-S.β * N * modulatedEnergyKernel (periodicRiesz d S.s) X S.μ0))
        (Measure.pi fun _ : Fin N => S.μ0) ∧
      Real.exp (-(C * N * deltaN d S.s N)) ≤ mxK S N ∧ mxK S N ≤ Real.exp (C * N * deltaN d S.s N) := by
  obtain ⟨C, hC0, hCp⟩ := HRS.T25.t25_press S S.β S.β S.hβ
  refine ⟨C, hC0, fun N hN => ?_⟩
  haveI := isProb_withDensityReal S.hρ0.density
  haveI hprob : IsProbabilityMeasure S.μ0 := by unfold PreparedData.μ0; infer_instance
  have hF : Measurable (fun X : Config d N => modulatedEnergyKernel (periodicRiesz d S.s) X S.μ0) :=
    measurable_modulatedEnergy (HRS.T25.t25_rowOK S)
  have hfm : Measurable (fun X : Config d N =>
      -S.β * N * modulatedEnergyKernel (periodicRiesz d S.s) X S.μ0) := measurable_const.mul hF
  have hp := hCp N hN S.β ⟨le_rfl, le_rfl⟩
  exact HRS.T25.t25_K_of_E (Measure.pi fun _ : Fin N => S.μ0) hfm (A := C * N * deltaN d S.s N)
    (by simpa [modNormalizerE, modulatedEnergyKernel] using hp.1)
    (by simpa [modNormalizerE, modulatedEnergyKernel] using hp.2)

/-- The real identity behind the change of measure. -/
theorem mx_exp_identity {f K p : ℝ} (hK : 0 < K) :
    Real.exp f / K * (Real.exp (-f) * K) ^ p = K ^ (p - 1) * Real.exp ((p - 1) * (-f)) := by
  rw [Real.mul_rpow (Real.exp_pos _).le hK.le, ← Real.exp_mul, Real.rpow_sub_one hK.ne']
  have : Real.exp (-f * p) * Real.exp f = Real.exp ((p - 1) * (-f)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← this]
  field_simp

/-- **Change of measure**: for `p ≥ 0`,
`∫ (dmix/dQ)^p dQ = K^{p-1} ∫ R^p exp((p-1) β N F_N) dπ`
(`Q = π.tilted(-β N F_N)`, `dmix/dπ = R`). -/
theorem mx_lintegral_rnDeriv_rpow (S : PreparedData d) {b : Torus d → ℝ} (hb : Measurable b)
    {M : ℝ} (hM : ∀ x, |b x| ≤ M) (hb0 : pair S.μ0 b = 0) (a₀ : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (hB : ∀ x, |a₀ * b x| ≤ Real.sqrt N / 2)
    (hKi : Integrable (fun X : Config d N =>
        Real.exp (-S.β * N * modulatedEnergyKernel (periodicRiesz d S.s) X S.μ0))
        (Measure.pi fun _ : Fin N => S.μ0)) {p : ℝ} (hp : 0 ≤ p) :
    ∫⁻ X, ((mixturePrep S.μ0 b a₀ N).rnDeriv (S.refMeasure N 0) X) ^ p ∂(S.refMeasure N 0) =
      ENNReal.ofReal (mxK S N ^ (p - 1)) *
        ∫⁻ X, ENNReal.ofReal (mxR b a₀ N X) ^ p *
          ENNReal.ofReal (Real.exp ((p - 1) * (S.β * mxW S N X)))
          ∂(Measure.pi fun _ : Fin N => S.μ0) := by
  haveI := isProb_withDensityReal S.hρ0.density
  haveI hprob : IsProbabilityMeasure S.μ0 := by unfold PreparedData.μ0; infer_instance
  have hN1 : 1 ≤ N := by omega
  set π : Measure (Config d N) := Measure.pi fun _ : Fin N => S.μ0 with hπ
  set Fm : Config d N → ℝ := fun X => modulatedEnergyKernel (periodicRiesz d S.s) X S.μ0 with hFm
  set f : Config d N → ℝ := fun X => -S.β * N * Fm X with hf
  have hQ : S.refMeasure N 0 = π.tilted f :=
    (HRS.T25.t25_ref0 S N).trans (HRS.T25.t25_tilted S N hN S.hβ.le)
  have hKdef : mxK S N = ∫ x, Real.exp (f x) ∂π := rfl
  have hKpos : 0 < mxK S N := by rw [hKdef]; exact integral_exp_pos hKi
  have hmixeq := mx_mixturePrep_eq_withDensity_real S.μ0 b hb a₀ N hN1 hB
  have hRm : Measurable (fun X : Config d N => mxR b a₀ N X) := by
    unfold mxR mxRp mxRm
    refine Measurable.div_const (Measurable.add ?_ ?_) _
    · exact Finset.measurable_prod _ fun i _ => by
        have := hb.comp (measurable_pi_apply (X := fun _ : Fin N => Torus d) i); fun_prop
    · exact Finset.measurable_prod _ fun i _ => by
        have := hb.comp (measurable_pi_apply (X := fun _ : Fin N => Torus d) i); fun_prop
  have hrn : (mixturePrep S.μ0 b a₀ N).rnDeriv π =ᵐ[π] fun X => ENNReal.ofReal (mxR b a₀ N X) := by
    rw [hmixeq]
    exact Measure.rnDeriv_withDensity π (ENNReal.measurable_ofReal.comp hRm)
  have hbi : Integrable b S.μ0 :=
    Integrable.of_bound hb.aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hM x)
  haveI := mx_isProb_mixturePrep S.μ0 b hb hbi hb0 a₀ N hN1 hB
  have hrt := rnDeriv_tilted_right (mixturePrep S.μ0 b a₀ N) π hKi
  rw [hQ, lintegral_tilted f]
  rw [← hKdef]
  have hcongr : ∀ᵐ X ∂π,
      ENNReal.ofReal (Real.exp (f X) / mxK S N) *
        ((mixturePrep S.μ0 b a₀ N).rnDeriv (π.tilted f) X) ^ p =
      ENNReal.ofReal (mxK S N ^ (p - 1)) *
        (ENNReal.ofReal (mxR b a₀ N X) ^ p *
          ENNReal.ofReal (Real.exp ((p - 1) * (S.β * mxW S N X)))) := by
    filter_upwards [hrn, hrt] with X h1 h2
    rw [h2, h1, ← hKdef, ENNReal.mul_rpow_of_nonneg _ _ hp,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp,
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mx_exp_identity hKpos,
      ENNReal.ofReal_mul (by positivity)]
    have : (p - 1) * -f X = (p - 1) * (S.β * mxW S N X) := by
      simp only [hf, hFm, mxW]; ring
    rw [this]
    ring
  rw [lintegral_congr_ae hcongr, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The exponential factor cubed is the (attractive-side) normaliser at inverse temperature
`-3εβ`: `∫ (e^{ε β N F_N})^3 dπ = K_{N,-3εβ}`. -/
theorem mx_lintegral_exp_cube (S : PreparedData d) (N : ℕ) (ε : ℝ) :
    ∫⁻ X : Config d N, (ENNReal.ofReal (Real.exp (ε * (S.β * mxW S N X)))) ^ (3 : ℝ)
        ∂(Measure.pi fun _ : Fin N => S.μ0) =
      modNormalizerE (periodicRiesz d S.s) N (-3 * ε * S.β) S.μ0 := by
  unfold modNormalizerE
  refine lintegral_congr fun X => ?_
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
  simp only [mxW]
  have : ε * (S.β * (↑N * modulatedEnergyKernel (periodicRiesz d S.s) X S.μ0)) * 3 =
      -(-3 * ε * S.β) * ↑N * modulatedEnergyKernel (periodicRiesz d S.s) X S.μ0 := by ring
  rw [this]

/-- Hölder with exponents `(3/2, 3)`:
`∫ R^{1+ε} e^{εβW} dπ ≤ (∫ R^{(1+ε)3/2} dπ)^{2/3} (∫ e^{3εβW} dπ)^{1/3}`. -/
theorem mx_holder (S : PreparedData d) {b : Torus d → ℝ} (hb : Measurable b) (a₀ : ℝ) (N : ℕ)
    (ε : ℝ) :
    ∫⁻ X : Config d N, ENNReal.ofReal (mxR b a₀ N X) ^ (1 + ε) *
        ENNReal.ofReal (Real.exp (ε * (S.β * mxW S N X))) ∂(Measure.pi fun _ : Fin N => S.μ0) ≤
      (∫⁻ X : Config d N, ENNReal.ofReal (mxR b a₀ N X) ^ ((1 + ε) * (3 / 2 : ℝ))
          ∂(Measure.pi fun _ : Fin N => S.μ0)) ^ (1 / (3 / 2 : ℝ)) *
        (modNormalizerE (periodicRiesz d S.s) N (-3 * ε * S.β) S.μ0) ^ (1 / (3 : ℝ)) := by
  haveI := isProb_withDensityReal S.hρ0.density
  haveI hprob : IsProbabilityMeasure S.μ0 := by unfold PreparedData.μ0; infer_instance
  have hpq : (3 / 2 : ℝ).HolderConjugate 3 := by
    rw [Real.holderConjugate_iff]; constructor <;> norm_num
  have hRm : Measurable (fun X : Config d N => mxR b a₀ N X) := by
    unfold mxR mxRp mxRm
    refine Measurable.div_const (Measurable.add ?_ ?_) _
    · exact Finset.measurable_prod _ fun i _ => by
        have := hb.comp (measurable_pi_apply (X := fun _ : Fin N => Torus d) i); fun_prop
    · exact Finset.measurable_prod _ fun i _ => by
        have := hb.comp (measurable_pi_apply (X := fun _ : Fin N => Torus d) i); fun_prop
  have hF : Measurable (fun X : Config d N => modulatedEnergyKernel (periodicRiesz d S.s) X S.μ0) :=
    measurable_modulatedEnergy (HRS.T25.t25_rowOK S)
  have hWm : Measurable (mxW S N) := measurable_const.mul hF
  have hf : Measurable fun X : Config d N => ENNReal.ofReal (mxR b a₀ N X) ^ (1 + ε) :=
    (ENNReal.measurable_ofReal.comp hRm).pow_const _
  have hg : Measurable fun X : Config d N => ENNReal.ofReal (Real.exp (ε * (S.β * mxW S N X))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      (measurable_const.mul hWm)))
  have := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.pi fun _ : Fin N => S.μ0) hpq
    hf.aemeasurable hg.aemeasurable
  rw [mx_lintegral_exp_cube S N ε] at this
  have e : ∀ X : Config d N, (ENNReal.ofReal (mxR b a₀ N X) ^ (1 + ε)) ^ (3 / 2 : ℝ) =
      ENNReal.ofReal (mxR b a₀ N X) ^ ((1 + ε) * (3 / 2 : ℝ)) := fun X => by
    rw [← ENNReal.rpow_mul]
  simp only [e, Pi.mul_apply] at this
  exact this

end Main

end HRS
