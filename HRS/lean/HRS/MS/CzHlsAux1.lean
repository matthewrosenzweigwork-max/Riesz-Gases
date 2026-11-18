import HRS.Commutator.Whole.ExternalAuxHLS3
import HRS.Commutator.Whole.ExternalAuxHLS5

/-!
# HLS-GLUE, part 1: the Riesz potential `I_σ` on `L^q → L^p` for measurable-representative data

Packet HLSG (CZ development).  Infrastructure lemma `riesz_pot_Lp`, a glue over `cmxHLS_kernel`
(`HRS/Commutator/Whole/ExternalAuxHLS3.lean`): for `0 < σ`, `1 < q < p` and `1/p = 1/q - σ/d` there is `C > 0` with

`(∫⁻ x, (I_σ |u|)(x)^p)^{1/p} ≤ C * ‖u‖_{L^q}` for every `u` a.e. strongly measurable,

where `I_σ |u| (x) = ∫⁻ y, ofReal(|x-y|^{σ-d}) * ‖u y‖ₑ` is `cmxHLS_I σ (fun y => ‖u y‖ₑ) x` (the `ENNReal`
Riesz potential; no Bochner junk values: if `‖u‖_q = ∞` the right side is `⊤`).

Adjustments with respect to the packet sketch (all harmless): the hypothesis `u ∈ MemLp q` is weakened to
`AEStronglyMeasurable u` (so the statement also covers `u ∉ L^q`, where the right side is `⊤`); the bound is
stated for the `ENNReal`-valued potential, and then in the two forms used downstream:
* `riesz_pot_Lp_of_le`: any `v` (a.e. strongly measurable) with `‖v x‖ₑ ≤ I_σ|u|(x)` a.e. satisfies
  `eLpNorm v p ≤ C‖u‖_q`;
* `riesz_pot_Lp_real`: the real Bochner form `x ↦ ∫ z, |z|^{σ-d} |u(x-z)| dz` (measurability of this function
  is part of the conclusion's hypothesis; when the integrand is not integrable the Bochner integral is `0`, which
  is still `≤ I_σ|u|(x)`, so no junk-value problem arises for an upper bound).

Helper lemmas are prefixed `hlsg_`.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.CZ.Hls

open HRS.Commutator.Whole

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- `cmxHLS_I` only depends on the a.e.-class of the integrand. -/
lemma hlsg_pot_congr (σ : ℝ) {F G : 𝔼 → ℝ≥0∞} (h : F =ᵐ[volume] G) (x : 𝔼) :
    cmxHLS_I σ F x = cmxHLS_I σ G x := by
  unfold cmxHLS_I
  exact lintegral_congr_ae (by filter_upwards [h] with y hy; simp [hy])

/-- **HLS for `L^q → L^p` (potential form, `ENNReal`)**. -/
theorem riesz_pot_Lp (hd : 1 ≤ d) {σ p q : ℝ} (hσ : 0 < σ) (hq : 1 < q) (hqp : q < p)
    (hrel : 1 / p = 1 / q - σ / d) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : 𝔼 → ℝ, AEStronglyMeasurable u volume →
      (∫⁻ x, cmxHLS_I σ (fun y => ‖u y‖ₑ) x ^ p) ^ (1 / p) ≤
        ENNReal.ofReal C * eLpNorm u (ENNReal.ofReal q) volume := by
  obtain ⟨C, hC, hK⟩ := cmxHLS_kernel hd hσ hq hqp hrel
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  refine ⟨C ^ (1 / p), Real.rpow_pos_of_pos hC _, fun u hu => ?_⟩
  obtain ⟨u', hu'm, hu'ae⟩ : ∃ u' : 𝔼 → ℝ, Measurable u' ∧ u =ᵐ[volume] u' :=
    ⟨hu.aemeasurable.mk u, hu.aemeasurable.measurable_mk, hu.aemeasurable.ae_eq_mk⟩
  set f : 𝔼 → ℝ≥0 := fun y => ‖u' y‖₊ with hf
  have hfm : Measurable f := hu'm.nnnorm
  have hae : (fun y => ‖u y‖ₑ) =ᵐ[volume] fun y => (f y : ℝ≥0∞) := by
    filter_upwards [hu'ae] with y hy
    simp only [hf, hy]; rfl
  have hK' := hK f hfm
  have h1 : ∀ x, cmxHLS_I σ (fun y => ‖u y‖ₑ) x = cmxHLS_I σ (fun y => (f y : ℝ≥0∞)) x :=
    fun x => hlsg_pot_congr σ hae x
  have h2 : (∫⁻ y, (f y : ℝ≥0∞) ^ q) = ∫⁻ y, ‖u y‖ₑ ^ q := by
    refine (lintegral_congr_ae ?_).symm
    filter_upwards [hae] with y hy
    rw [hy]
  have hnorm : eLpNorm u (ENNReal.ofReal q) volume = (∫⁻ y, ‖u y‖ₑ ^ q) ^ (1 / q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hq0) ENNReal.ofReal_ne_top hu,
      ENNReal.toReal_ofReal hq0.le]
  simp_rw [h1]
  rw [hnorm, ← h2]
  calc (∫⁻ x, cmxHLS_I σ (fun y => (f y : ℝ≥0∞)) x ^ p) ^ (1 / p)
      ≤ (ENNReal.ofReal C * (∫⁻ y, (f y : ℝ≥0∞) ^ q) ^ (p / q)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hK' (by positivity)
    _ = ENNReal.ofReal (C ^ (1 / p)) * (∫⁻ y, (f y : ℝ≥0∞) ^ q) ^ (1 / q) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          ENNReal.ofReal_rpow_of_pos hC]
        congr 2
        field_simp


/-- Convolution against a measurable kernel preserves a.e. strong measurability of the argument:
`x ↦ ∫ z, K z * u (x - z)` is a.e. strongly measurable when `K` is measurable and `u` is a.e. strongly measurable
(no integrability is needed; the Bochner integral of a non-integrable function is `0`, which is measurable). -/
lemma hlsg_aesm_conv {K : 𝔼 → ℝ} (hK : Measurable K) {u : 𝔼 → ℝ} (hu : AEStronglyMeasurable u volume) :
    AEStronglyMeasurable (fun x => ∫ z, K z * u (x - z)) volume := by
  obtain ⟨u', hu'm, hu'ae⟩ : ∃ u' : 𝔼 → ℝ, Measurable u' ∧ u =ᵐ[volume] u' :=
    ⟨hu.aemeasurable.mk u, hu.aemeasurable.measurable_mk, hu.aemeasurable.ae_eq_mk⟩
  have hpt : ∀ x, ∫ z, K z * u (x - z) = ∫ z, K z * u' (x - z) := by
    intro x
    refine integral_congr_ae ?_
    have : (fun z : 𝔼 => u (x - z)) =ᵐ[volume] fun z => u' (x - z) :=
      (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae_eq_comp hu'ae
    filter_upwards [this] with z hz
    rw [hz]
  have hmeas : Measurable (fun p : 𝔼 × 𝔼 => K p.2 * u' (p.1 - p.2)) :=
    (hK.comp measurable_snd).mul (hu'm.comp (measurable_fst.sub measurable_snd))
  have := hmeas.stronglyMeasurable.integral_prod_right'  (ν := (volume : Measure 𝔼))
  simp_rw [hpt]
  exact this.aestronglyMeasurable

/-- `L^q → L^p` bound for any a.e.-strongly-measurable `v` dominated a.e. by `I_σ|u|`. -/
theorem riesz_pot_Lp_of_le (hd : 1 ≤ d) {σ p q : ℝ} (hσ : 0 < σ) (hq : 1 < q) (hqp : q < p)
    (hrel : 1 / p = 1 / q - σ / d) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : 𝔼 → ℝ, AEStronglyMeasurable u volume → AEStronglyMeasurable v volume →
      (∀ᵐ x ∂volume, ‖v x‖ₑ ≤ cmxHLS_I σ (fun y => ‖u y‖ₑ) x) →
      eLpNorm v (ENNReal.ofReal p) volume ≤ ENNReal.ofReal C * eLpNorm u (ENNReal.ofReal q) volume := by
  obtain ⟨C, hC, hK⟩ := riesz_pot_Lp hd hσ hq hqp hrel
  have hp0 : 0 < p := by linarith
  refine ⟨C, hC, fun u v hu hv hle => (le_trans ?_ (hK u hu))⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top hv,
    ENNReal.toReal_ofReal hp0.le]
  exact ENNReal.rpow_le_rpow (lintegral_mono_ae (hle.mono fun x hx => ENNReal.rpow_le_rpow hx hp0.le))
    (by positivity)

/-- The Riesz potential in the variable `z = x - y`. -/
lemma hlsg_pot_eq_z (σ : ℝ) (F : 𝔼 → ℝ≥0∞) (x : 𝔼) :
    cmxHLS_I σ F x = ∫⁻ z, ENNReal.ofReal (‖z‖ ^ (σ - (d : ℝ))) * F (x - z) := by
  unfold cmxHLS_I cmxHLS_k
  rw [← lintegral_sub_left_eq_self (fun y => ENNReal.ofReal (‖x - y‖ ^ (σ - (d : ℝ))) * F y) x]
  simp

/-- **HLS for `L^q → L^p`, real Bochner form**: `‖x ↦ ∫ |z|^{σ-d} |u(x-z)| dz‖_p ≤ C ‖u‖_q`. -/
theorem riesz_pot_Lp_real (hd : 1 ≤ d) {σ p q : ℝ} (hσ : 0 < σ) (hq : 1 < q) (hqp : q < p)
    (hrel : 1 / p = 1 / q - σ / d) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : 𝔼 → ℝ, AEStronglyMeasurable u volume →
      eLpNorm (fun x => ∫ z, ‖z‖ ^ (σ - (d : ℝ)) * |u (x - z)|) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm u (ENNReal.ofReal q) volume := by
  obtain ⟨C, hC, hK⟩ := riesz_pot_Lp_of_le hd hσ hq hqp hrel
  refine ⟨C, hC, fun u hu => hK u _ hu ?_ (Eventually.of_forall fun x => ?_)⟩
  · have hK0 : Measurable (fun z : 𝔼 => ‖z‖ ^ (σ - (d : ℝ))) := measurable_norm.pow_const _
    exact hlsg_aesm_conv hK0 (u := fun y => |u y|) (by simpa using hu.norm)
  · rw [hlsg_pot_eq_z]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun z => ?_
    rw [enorm_mul, Real.enorm_eq_ofReal (by positivity)]
    simp

/-- The potential `I_σ|u|` is finite a.e. for `u ∈ L^q` (`1 < q < p`, `1/p = 1/q - σ/d`). -/
theorem riesz_pot_ae_lt_top (hd : 1 ≤ d) {σ p q : ℝ} (hσ : 0 < σ) (hq : 1 < q) (hqp : q < p)
    (hrel : 1 / p = 1 / q - σ / d) {u : 𝔼 → ℝ} (hu : MemLp u (ENNReal.ofReal q) volume) :
    ∀ᵐ x ∂volume, cmxHLS_I σ (fun y => ‖u y‖ₑ) x < ⊤ := by
  obtain ⟨C, hC, hK⟩ := riesz_pot_Lp hd hσ hq hqp hrel
  have hp0 : 0 < p := by linarith
  obtain ⟨u', hu'm, hu'ae⟩ : ∃ u' : 𝔼 → ℝ, Measurable u' ∧ u =ᵐ[volume] u' :=
    ⟨hu.aestronglyMeasurable.aemeasurable.mk u, hu.aestronglyMeasurable.aemeasurable.measurable_mk, hu.aestronglyMeasurable.aemeasurable.ae_eq_mk⟩
  have hae : (fun y => ‖u y‖ₑ) =ᵐ[volume] fun y => ‖u' y‖ₑ := by
    filter_upwards [hu'ae] with y hy; rw [hy]
  have hIm : Measurable (fun x => cmxHLS_I σ (fun y => ‖u' y‖ₑ) x) :=
    cmxHLS_I_measurable σ hu'm.enorm
  have hfin := hK u hu.aestronglyMeasurable
  have hlt : (∫⁻ x, cmxHLS_I σ (fun y => ‖u y‖ₑ) x ^ p) ^ (1 / p) < ⊤ := by
    refine lt_of_le_of_lt hfin (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    exact hu.eLpNorm_lt_top
  have hlt2 : ∫⁻ x, cmxHLS_I σ (fun y => ‖u y‖ₑ) x ^ p < ⊤ := by
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.top_rpow_of_pos (by positivity)] at hlt
    exact lt_irrefl _ hlt
  have hmeas : Measurable (fun x => cmxHLS_I σ (fun y => ‖u' y‖ₑ) x ^ p) := hIm.pow_const p
  have hcongr : ∀ x, cmxHLS_I σ (fun y => ‖u y‖ₑ) x = cmxHLS_I σ (fun y => ‖u' y‖ₑ) x :=
    fun x => hlsg_pot_congr σ hae x
  simp_rw [hcongr] at hlt2 ⊢
  have := ae_lt_top hmeas hlt2.ne
  filter_upwards [this] with x hx
  by_contra h
  rw [not_lt, top_le_iff] at h
  rw [h, ENNReal.top_rpow_of_pos hp0] at hx
  exact lt_irrefl _ hx

end HRS.CZ.Hls
