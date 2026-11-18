/-
# HRS.MD.DOMFinal — packet DOM: assembly of `normal_form_domain_proof`

Approximants `Fn = χ_{1/(n+1)} · (F_N(ψ) - c)`, `c = E F_N(ψ)`.
-/
import HRS.MD.DOMDct
import HRS.MD.DOMMeas
import HRS.MD.DOMSpec

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MD.DOMProof

open HRS.Q84d HRS.MD.DOM

section Aux

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem domp_measurable_chi (ε : ℝ) : Measurable (chi ε : Config d N → ℝ) := by
  unfold chi
  refine Finset.measurable_prod _ fun p _ => ?_
  have h1 : Continuous (fun X : Config d N => ε⁻¹ * sT (X p.1 - X p.2)) :=
    continuous_const.mul (domp_continuous_sT.comp ((continuous_apply p.1).sub (continuous_apply p.2)))
  exact (domp_th_smooth.continuous.comp h1).measurable

theorem domp_isOpen_noncollision : IsOpen ((collisionSet d N)ᶜ) := by
  have : (collisionSet d N) = ⋃ a : Fin N, ⋃ b : Fin N, ⋃ (_ : a ≠ b), {X : Config d N | X a = X b} := by
    ext X; simp [collisionSet]
  rw [isOpen_compl_iff, this]
  refine isClosed_iUnion_of_finite fun a => isClosed_iUnion_of_finite fun b =>
    isClosed_iUnion_of_finite fun _ => ?_
  exact isClosed_eq (continuous_apply a) (continuous_apply b)

theorem domp_aestronglyMeasurable_particleGen (V : Torus d → ℝ) (β : ℝ) (hsd : s < d)
    {μ : Measure (Config d N)} (hnc : ∀ᵐ X ∂μ, X ∉ collisionSet d N) {Φ : Config d N → ℝ}
    (hΦ : Measurable Φ)
    (hsm : ∀ X : Config d N, X ∉ collisionSet d N → ∀ i, ContDiffAt ℝ 2 (slice Φ X i) 0) :
    AEStronglyMeasurable (particleGen d s V β Φ) μ := by
  have h := domp_measurable_particleGen (s := s) V β hsd hΦ
    (domp_isOpen_noncollision (d := d) (N := N)) (fun X hX i => hsm X hX i)
  refine (h.aemeasurable.congr ?_).aestronglyMeasurable
  filter_upwards [hnc] with X hX
  exact Set.indicator_of_mem (show X ∈ (collisionSet d N)ᶜ from hX) _

theorem domp_configGrad_centered {μ : Measure (Config d N)} (Φ : Config d N → ℝ) (X : Config d N)
    (i : Fin N) : configGrad (centeredUnder μ Φ) X i = configGrad Φ X i := by
  unfold configGrad centeredUnder
  exact domp_gradient_sub_const _ _ _

theorem domp_enorm_sq_le {E : Type*} [NormedAddCommGroup E] {v : E} {B : ℝ} (h : ‖v‖ ≤ B) :
    ‖v‖ₑ ^ 2 ≤ ENNReal.ofReal (B ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h 2)

end Aux

variable {d : ℕ}

/-- **4.16-DOM, proved.** -/
theorem normal_form_domain_proof {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∀ (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ), Torus.IsSmooth f →
      IsPairCorrector d s V β ρ f K₁ ψ → ∀ N : ℕ, 2 ≤ N →
        IsInClosedGenerator d s V β (canonicalGibbs (periodicRiesz d s) V N β)
          (centeredUnder (canonicalGibbs (periodicRiesz d s) V N β) (Fstat ψ))
          (particleGen d s V β (Fstat (N := N) ψ)) := by
  intro f K₁ ψ hf hψ N hN
  have hN1 : 1 ≤ N := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  set μ := canonicalGibbs (periodicRiesz d s) V N β with hμ
  set c : ℝ := ∫ X, Fstat (N := N) ψ X ∂μ with hc
  obtain ⟨C, hC0, hC⟩ := domp_diff_bounds hd hcrit hV hβ hN1 hψ c
  obtain ⟨Xc, hXc0, hXc⟩ := domp_chi_deriv hs1 (d := d) (N := N)
  set ε : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹ with hε
  have hεpos : ∀ n, 0 < ε n := fun n => by simp only [hε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hac : μ ≪ (volume : Measure (Config d N)) := q84d_gibbs_ac
  have hnc : ∀ᵐ X ∂μ, X ∉ collisionSet d N :=
    hac.ae_le (q84d_ae_not_collision (d := d) (N := N) (by omega))
  have hint8 : Integrable (fun X : Config d N => Pw s X ^ 8) μ :=
    domp_integrable_Pw_pow hd hcrit hV hβ hN1 8
  have hFm : Measurable (Fstat (N := N) ψ) := Q84e.q84e_measurable_Fstat hψ.measurable
  have hFem : ∀ n, Measurable (Fe (ε n) c (Fstat (N := N) ψ)) := fun n =>
    (domp_measurable_chi _).mul (hFm.sub_const c)
  have hslF : ∀ X : Config d N, X ∉ collisionSet d N → ∀ i, ContDiffAt ℝ 2 (slice (Fstat ψ) X i) 0 :=
    fun X hX i => domp_Fstat_slice hψ.symm hψ.size.smooth X
      (fun a b hab hXab => hX ⟨a, b, hab, hXab⟩) i
  have hslFe : ∀ n, ∀ X : Config d N, X ∉ collisionSet d N → ∀ i,
      ContDiffAt ℝ 2 (slice (Fe (ε n) c (Fstat ψ)) X i) 0 := fun n X hX i => by
    have h1 := (hXc (ε n) (hεpos n) X hX i).1
    have h2 := hslF X hX i
    exact h1.mul (h2.sub contDiffAt_const)
  have hGm : AEStronglyMeasurable (particleGen d s V β (Fstat (N := N) ψ)) μ :=
    domp_aestronglyMeasurable_particleGen V β hsd hnc hFm hslF
  have hGem : ∀ n, AEStronglyMeasurable (particleGen d s V β (Fe (ε n) c (Fstat (N := N) ψ))) μ :=
    fun n => domp_aestronglyMeasurable_particleGen V β hsd hnc (hFem n) (hslFe n)
  refine ⟨fun n => Fe (ε n) c (Fstat ψ), fun n => ⟨domp_contDiff_Fe_lift hψ.size.smooth (hεpos n) c,
    Kset (ε n) d N, domp_isCompact_Kset _, domp_Kset_disjoint (hεpos n),
    fun X hX => domp_Fe_zero_outside (hεpos n) c _ X hX⟩, ?_, ?_, ?_⟩
  · -- `Fn → F` in `L²`
    have key := domp_tendsto_eLpNorm hint8 hnc hεlim
      (h := fun n X => Fe (ε n) c (Fstat (N := N) ψ) X - (Fstat ψ X - c))
      (fun n => ((hFem n).sub (hFm.sub_const c)).aestronglyMeasurable) (C := C) (fun n => by
        filter_upwards [hnc] with X hX
        have hb := hC (ε n) (hεpos n) X hX
        refine ⟨by simpa [Real.norm_eq_abs] using hb.2.1, fun hN' => (hb.1 hN').1⟩)
    exact key
  · -- `𝓛 Fn → 𝓛 F` in `L²`
    have key := domp_tendsto_eLpNorm hint8 hnc hεlim
      (h := fun n X => particleGen d s V β (Fe (ε n) c (Fstat (N := N) ψ)) X -
        particleGen d s V β (Fstat (N := N) ψ) X)
      (fun n => (hGem n).sub hGm) (C := C) (fun n => by
        filter_upwards [hnc] with X hX
        have hb := hC (ε n) (hεpos n) X hX
        refine ⟨by simpa [Real.norm_eq_abs] using hb.2.2.2, fun hN' => (hb.1 hN').2.2⟩)
    exact key
  · -- `∇ Fn → ∇ F` in `L²`
    have hK : (0 : ℝ) ≤ N * C ^ 2 := by positivity
    have key := domp_tendsto_lintegral hint8 hnc hεlim hK
      (fun n X => ∑ i, ‖configGrad (Fe (ε n) c (Fstat (N := N) ψ)) X i -
        configGrad (Fstat (N := N) ψ) X i‖ₑ ^ 2) (fun n => by
        filter_upwards [hnc] with X hX
        have hb := hC (ε n) (hεpos n) X hX
        refine ⟨?_, fun hN' => ?_⟩
        · calc ∑ i, ‖configGrad (Fe (ε n) c (Fstat (N := N) ψ)) X i -
                configGrad (Fstat (N := N) ψ) X i‖ₑ ^ 2
              ≤ ∑ _i : Fin N, ENNReal.ofReal (C ^ 2 * Pw s X ^ 8) := by
                refine Finset.sum_le_sum fun i _ => ?_
                have := domp_enorm_sq_le (hb.2.2.1 i)
                refine this.trans (le_of_eq ?_)
                congr 1; ring
            _ = ENNReal.ofReal (N * C ^ 2 * Pw s X ^ 8) := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                  ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
                congr 1; ring
        · refine Finset.sum_eq_zero fun i _ => ?_
          rw [(hb.1 hN').2.1 i]; simp)
    simpa only [domp_configGrad_centered] using key

end HRS.MD.DOMProof
