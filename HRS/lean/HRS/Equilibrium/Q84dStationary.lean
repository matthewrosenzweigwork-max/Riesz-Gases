/-
# HRS.Equilibrium.Q84dStationary — packet Q84d: analytic inputs of Proposition 4.16 (`normal_form`)

Statements under the standing hypotheses of `normal_form` (`d ≥ 2`, `s = d/2`, `β > 0`, `V`
smooth, `ρ` the thermal density, `ρ` smooth positive) for every `N ≥ 2` and every kernel `ψ` with
`IsPairCorrector d s V β ρ f K₁ ψ` (`f` smooth):

* D1 `q84d_stationarity`: `𝓛F_N(ψ)` is `P_{N,β}`-integrable with mean zero;
* D2 `q84d_quadStat_integrable`, `q84d_Fstat_integrable`, `q84d_errStat_integrable`: the three
  integrability conjuncts of `normal_form`;
* D3 `q84d_jpair_aesm` (a.e. joint measurability of `𝒥ψ`; strict measurability of the
  `fderiv`-defined kernels `𝒥ψ`, `B_ψ`, `G_ψ` is not available, their diagonal values are junk) and
  `q84d_modified_kernels` (strictly measurable modifications `Jt`, `Bt`, `Gt` with exactly the
  hypotheses of `pair_moments`, equal to the originals `P_{N,β}`-a.s. inside `errStat`);
* D4 `q84d_zeta_bound`: `N⁻¹‖ζ_N(a_f)‖_{L²(P)} ≤ C|f|_K N^{-1/2}` (via `‖a_f‖_∞ ≤ C|f|_K`; the
  canonical linear-variance bound without the factor `√N` is not needed for the rate).
-/
import HRS.Equilibrium.Q84dAuxL
import HRS.Equilibrium.Q84dAuxW
import HRS.Equilibrium.Q84dAuxX
import HRS.Equilibrium.Q84dAuxAC

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ}

/-- **D2 (first conjunct of `normal_form`).**  `quadStat h_f μ` is `P_{N,β}`-integrable. -/
theorem q84d_quadStat_integrable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (_hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ)
    (f : Torus d → ℝ) (hf : Torus.IsSmooth f) (N : ℕ) (hN : 2 ≤ N) :
    Integrable (quadStat (hTransport d s f) (withDensityReal ρ))
      (canonicalGibbs (periodicRiesz d s) V N β) :=
  q84d_integrable_quadStat hd hcrit hV hβ (by omega) hρs hf

/-- **D2 (second conjunct of `normal_form`).**  `F_N(ψ)` is `P_{N,β}`-integrable. -/
theorem q84d_Fstat_integrable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (_hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (_hρs : SmoothPosDensity ρ)
    (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ) (_hf : Torus.IsSmooth f)
    (hψ : IsPairCorrector d s V β ρ f K₁ ψ) (N : ℕ) (hN : 2 ≤ N) :
    Integrable (Fstat (N := N) ψ) (canonicalGibbs (periodicRiesz d s) V N β) :=
  q84d_integrable_Fstat hd hcrit hV hβ (by omega) hψ

/-- **D2 (third conjunct of `normal_form`).**  `E_N(ψ)` is `P_{N,β}`-integrable. -/
theorem q84d_errStat_integrable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ)
    (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ) (hf : Torus.IsSmooth f)
    (hψ : IsPairCorrector d s V β ρ f K₁ ψ) (N : ℕ) (hN : 2 ≤ N) :
    Integrable (errStat d s ρ (N := N) ψ) (canonicalGibbs (periodicRiesz d s) V N β) := by
  obtain ⟨C, hC⟩ := Q84a.q84a_estimates hd hcrit β hβ V hV ρ hρ hρs
  obtain ⟨hG, hB⟩ := hC f K₁ ψ hf hψ
  have h1 := q84d_integrable_FstatJ hd hcrit hV hβ (by omega : 1 ≤ N) hρs hf hψ
  have h2 := q84d_integrable_tripleG hd hcrit hV hβ (by omega : 1 ≤ N) hρs hf hψ hG
  have h3 := q84d_integrable_pairB hd hcrit hV hβ (by omega : 1 ≤ N) hψ hB
  unfold errStat
  exact ((h1.const_mul (-(2 / (N : ℝ)))).add h2).sub h3

/-- **D3.**  `𝒥ψ` is a.e.-jointly measurable for Haar measure on `𝕋^d × 𝕋^d` (and therefore
along the pair marginals of every law absolutely continuous with respect to Haar measure on
configuration space).  Strict joint measurability of `Jpair` is not provable: `Jop` is defined with
`fderiv` (junk values where non-differentiable); see `q84d_modified_kernels` for strictly
measurable modifications. -/
theorem q84d_jpair_aesm (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (ρ : Torus d → ℝ)
    (hρs : SmoothPosDensity ρ) (V : Torus d → ℝ) (β : ℝ) (f : Torus d → ℝ) (K₁ : ℝ)
    (ψ : Torus d → Torus d → ℝ) (hf : Torus.IsSmooth f) (hψ : IsPairCorrector d s V β ρ f K₁ ψ) :
    AEStronglyMeasurable (fun p : Torus d × Torus d => Jpair d s ρ ψ p.1 p.2) volume := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by rw [hcrit]; linarith
  exact q84d_jpair_aestronglyMeasurable (by omega) hsd hρs hf hψ

/-- **D1: stationarity.**  For every kernel `ψ` with the conclusions of Proposition 4.13 and every
`N ≥ 2`, `𝓛F_N(ψ)` is `P_{N,β}`-integrable and has mean zero (integration by parts against the
Gibbs density `exp(-βH_N)`, whose drift is the particle drift; the collision set is invisible to
integration along coordinate lines for `d ≥ 2`).  This is the stationarity input of `normal_form`
(centering of the identity `(√N/2) D_μ(h_f) = -𝓛F_N + E_N - (2/N)ζ_N(a_f)`). -/
theorem q84d_stationarity (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (_hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (_hρs : SmoothPosDensity ρ)
    (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ) (_hf : Torus.IsSmooth f)
    (hψ : IsPairCorrector d s V β ρ f K₁ ψ) (N : ℕ) (hN : 2 ≤ N) :
    Integrable (particleGen d s V β (Fstat (N := N) ψ))
        (canonicalGibbs (periodicRiesz d s) V N β) ∧
      ∫ X, particleGen d s V β (Fstat (N := N) ψ) X ∂(canonicalGibbs (periodicRiesz d s) V N β) = 0 := by
  have hN1 : 1 ≤ N := by omega
  obtain ⟨c, hc⟩ := q84d_hlow hd hcrit hV hN1
  have hgm := q84d_measurable_g hd hcrit
  have hVm := q84d_measurable_V hV
  have hsm := hψ.size.smooth
  have hsymm := hψ.symm
  -- the divergence field
  set Sv : Config d N → ℝ := fun X => ∑ i, ∑ k, vik d s V β ψ i k X with hSv
  have hSvi : Integrable Sv volume :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
      q84d_vik_integrable hd hcrit hV hβ hN1 hψ i k
  have hSv0 : ∫ X, Sv X = 0 := by
    rw [hSv]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
      q84d_vik_integrable hd hcrit hV hβ hN1 hψ i k]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_finsetSum _ fun k _ => q84d_vik_integrable hd hcrit hV hβ hN1 hψ i k]
    refine Finset.sum_eq_zero fun k _ => ?_
    refine q84d_ibp i k (w := uik d s V β ψ i k)
      (q84d_measurable_vik hd hcrit hV ψ i k) (q84d_vik_integrable hd hcrit hV hβ hN1 hψ i k) ?_
    filter_upwards [q84d_ae_line_free hd i k] with Y hY t
    exact q84d_u_line_deriv hd hcrit hV hsm i k Y hY t
  -- the identity `β q 𝓛F = Sv` a.e.
  have hid : ∀ᵐ X ∂(volume : Measure (Config d N)),
      Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) *
        particleGen d s V β (Fstat (N := N) ψ) X = β⁻¹ * Sv X := by
    filter_upwards [q84d_ae_not_collision (N := N) (d := d) (by omega)] with X hX
    have hXne : ∀ a b : Fin N, a ≠ b → X a ≠ X b := fun a b hab hXab => hX ⟨a, b, hab, hXab⟩
    have := q84d_gen_identity (s := s) (V := V) hβ hsymm hsm X hXne
    unfold qd at this
    rw [hSv]
    show _ = β⁻¹ * ∑ i, ∑ k, vik d s V β ψ i k X
    rw [← this]
    field_simp
  have hint : Integrable (fun X => Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) *
      particleGen d s V β (Fstat (N := N) ψ) X) volume :=
    (hSvi.const_mul β⁻¹).congr (hid.mono fun X hX => hX.symm)
  refine ⟨(q84d_integrable_gibbs_iff hgm hVm hc hβ.le).2 hint, ?_⟩
  rw [q84d_integral_gibbs hgm hVm hc hβ.le, integral_congr_ae hid, integral_const_mul, hSv0]
  simp

/-- Elementary bound: if `|a| ≤ M` everywhere then
`‖√N · (μ_N(a) - E μ_N(a))‖_{L²(P)} ≤ 2 M √N` for any probability law `P`. -/
theorem q84d_zeta_trivial {N : ℕ} (hN : 1 ≤ N) {P : Measure (Config d N)} [IsProbabilityMeasure P]
    (a : Torus d → ℝ) (hm : Measurable a) {M : ℝ} (ha : ∀ x, |a x| ≤ M) :
    eLpNorm (fun X : Config d N => Real.sqrt N * centeredUnder P
        (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, a (Y i)) X) 2 P ≤
      ENNReal.ofReal (2 * M * Real.sqrt N) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (ha (0 : Torus d))
  have hF : ∀ Y : Config d N, ‖(1 / (N : ℝ)) * ∑ i, a (Y i)‖ ≤ M := by
    intro Y
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
    have : |∑ i, a (Y i)| ≤ N * M := by
      calc |∑ i, a (Y i)| ≤ ∑ i, |a (Y i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, M := Finset.sum_le_sum fun i _ => ha _
        _ = N * M := by simp
    calc 1 / (N : ℝ) * |∑ i, a (Y i)| ≤ 1 / (N : ℝ) * (N * M) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = M := by field_simp
  have hInt : ‖∫ Y, (1 / (N : ℝ)) * ∑ i, a (Y i) ∂P‖ ≤ M := by
    have := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, a (Y i)) (C := M)
      (Filter.Eventually.of_forall hF)
    simpa using this
  have hFm : Measurable (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, a (Y i)) :=
    measurable_const.mul (Finset.measurable_sum _ fun i _ => hm.comp (measurable_pi_apply i))
  have hmeas : AEStronglyMeasurable (fun X : Config d N => Real.sqrt N * centeredUnder P
      (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, a (Y i)) X) P := by
    unfold centeredUnder
    exact (measurable_const.mul (hFm.sub measurable_const)).aestronglyMeasurable
  have hpt : ∀ X : Config d N, ‖Real.sqrt N * centeredUnder P
      (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, a (Y i)) X‖ ≤ ‖2 * M * Real.sqrt N‖ := by
    intro X
    unfold centeredUnder
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * M * Real.sqrt N)]
    have h1 := hF X
    have h2 : ‖(1 / (N : ℝ)) * ∑ i, a (X i) - ∫ Y, (1 / (N : ℝ)) * ∑ i, a (Y i) ∂P‖ ≤ 2 * M :=
      (norm_sub_le _ _).trans (by linarith)
    rw [Real.norm_eq_abs] at h2
    calc Real.sqrt N * |(1 / (N : ℝ)) * ∑ i, a (X i) - ∫ Y, (1 / (N : ℝ)) * ∑ i, a (Y i) ∂P|
        ≤ Real.sqrt N * (2 * M) := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
      _ = 2 * M * Real.sqrt N := by ring
  calc eLpNorm (fun X : Config d N => Real.sqrt N * centeredUnder P
        (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, a (Y i)) X) 2 P
      ≤ eLpNorm (fun _ : Config d N => 2 * M * Real.sqrt N) 2 P :=
        eLpNorm_mono_ae hmeas (Filter.Eventually.of_forall hpt)
    _ = ENNReal.ofReal (2 * M * Real.sqrt N) := by
        rw [eLpNorm_const _ (by norm_num) (NeZero.ne P)]
        simp [Real.enorm_eq_ofReal (by positivity : (0 : ℝ) ≤ 2 * M * Real.sqrt N)]

/-- **D4 (fourth summand of `normal_form`).**  For every smooth `f` and `N ≥ 2`,
`N⁻¹ ‖ζ_N(a_f)‖_{L²(P_{N,β})} ≤ C |f|_K N^{-1/2}`, `ζ_N(a) = √N (μ_N(a) - E μ_N(a))`, with `C`
independent of `f` and `N`.  Proof: `‖a_f‖_∞ ≤ C |f|_K` (mean value theorem for `∇f` and
`|∇g| ≲ r^{-s-1}`, `q84d_aCoef_bound`) and the elementary `q84d_zeta_trivial`; this is weaker
than the canonical linear-variance bound `‖ζ_N(a)‖_2 ≤ C‖a‖_{L²(μ)}` (which needs the
resampling inequality of the calibrated reference) but gives exactly the rate required. -/
theorem q84d_zeta_bound (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (_hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Torus d → ℝ), Torus.IsSmooth f → ∀ N : ℕ, 2 ≤ N →
      ENNReal.ofReal (1 / (N : ℝ)) *
        eLpNorm (fun X : Config d N => Real.sqrt N *
          centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
            (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρ f (Y i)) X) 2
          (canonicalGibbs (periodicRiesz d s) V N β) ≤
        ENNReal.ofReal (C * posSeminorm (8 * d + 80) f * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨Ca, hCa0, hCa⟩ := q84d_aCoef_bound hd hcrit hρs
  refine ⟨2 * Ca, by positivity, fun f hf N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by rw [hcrit]; linarith
  haveI := q84d_isProb hd hcrit hV hβ hN1 (N := N)
  have hD0 := q84d_posSeminorm_nonneg (8 * d + 80) f
  have h1 := q84d_zeta_trivial hN1 (P := canonicalGibbs (periodicRiesz d s) V N β)
    (aCoef d s ρ f) (q84d_measurable_aCoef hsd hρs.density hf) (M := Ca * posSeminorm (8 * d + 80) f) (fun x => hCa hf x)
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have e : (1 / (N : ℝ)) * (2 * (Ca * posSeminorm (8 * d + 80) f) * Real.sqrt N) =
      2 * Ca * posSeminorm (8 * d + 80) f * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hNp.le, ← Real.sqrt_eq_rpow]
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
    have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNp.le
    have h3 : (1 / (N : ℝ)) * Real.sqrt N = (Real.sqrt N)⁻¹ := by
      have h4 : 1 / (N : ℝ) * Real.sqrt N * Real.sqrt N = (1 / (N : ℝ)) * (Real.sqrt N * Real.sqrt N) := by ring
      have h5 : 1 / (N : ℝ) * Real.sqrt N * Real.sqrt N = 1 := by rw [h4, hss]; field_simp
      exact eq_inv_of_mul_eq_one_left h5
    calc (1 / (N : ℝ)) * (2 * (Ca * posSeminorm (8 * d + 80) f) * Real.sqrt N)
        = 2 * (Ca * posSeminorm (8 * d + 80) f) * ((1 / (N : ℝ)) * Real.sqrt N) := by ring
      _ = _ := by rw [h3]; ring
  calc ENNReal.ofReal (1 / (N : ℝ)) * eLpNorm _ 2 (canonicalGibbs (periodicRiesz d s) V N β)
      ≤ ENNReal.ofReal (1 / (N : ℝ)) * ENNReal.ofReal (2 * (Ca * posSeminorm (8 * d + 80) f) * Real.sqrt N) :=
        by gcongr
    _ = ENNReal.ofReal ((1 / (N : ℝ)) * (2 * (Ca * posSeminorm (8 * d + 80) f) * Real.sqrt N)) := by
        exact (ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))).symm
    _ = _ := by rw [e]

/-- Almost surely under `P_{N,β}` no particle lies in a given Haar-null set. -/
theorem q84d_ae_not_mem_null {E : Set (Torus d)} (hE0 : (volume : Measure (Torus d)) E = 0)
    {V : Torus d → ℝ} {β : ℝ} {N : ℕ} (g : Torus d → ℝ) :
    ∀ᵐ X ∂(canonicalGibbs g V N β), ∀ i : Fin N, X i ∉ E := by
  have h1 : ∀ᵐ X ∂(volume : Measure (Config d N)), ∀ i : Fin N, X i ∉ E := by
    rw [ae_all_iff]
    intro i
    have hmp : MeasurePreserving (fun X : Config d N => X i) volume (volume : Measure (Torus d)) :=
      measurePreserving_eval (fun _ : Fin N => (volume : Measure (Torus d))) i
    have hE' : ∀ᵐ y ∂(volume : Measure (Torus d)), y ∉ E := by
      rw [ae_iff]; simpa using hE0
    exact hmp.quasiMeasurePreserving.ae hE'
  exact q84d_gibbs_ac.ae_le h1

/-- **D3 (bundled strictly measurable modifications).**  For `ψ` with `IsPairCorrector` and
canonical `G_ψ` (the canonicity clause of `triple_canonical`, passed as `hGcan`), there are
strictly measurable kernels `Jt`, `Bt`, `Gt` with exactly the hypotheses of `pair_moments`
(symmetric, canonical for `Jt`, `Gt`; size bounds `K₁ w`, `K w²`, `K·(triple envelope)`), such that
`E_N(ψ) = -(2/N) F_N(Jt) + N^{-5/2}∑ Gt - N^{-5/2}∑ Bt` holds `P_{N,β}`-almost surely for every
`N ≥ 2` (the originals contain `fderiv`-junk on the diagonal, so are not strictly measurable;
the modifications differ only on `E × 𝕋 ∪ 𝕋 × E ∪ {collisions}` for a Haar-null `E`, which is
invisible to `P_{N,β}`). -/
theorem q84d_modified_kernels (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ)
    (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ) (hf : Torus.IsSmooth f)
    (hψ : IsPairCorrector d s V β ρ f K₁ ψ)
    (hGcan : IsCanonicalTriple (withDensityReal ρ) (Gpsi d s ρ ψ)) :
    ∃ (Jt Bt : Torus d → Torus d → ℝ) (Gt : Torus d → Torus d → Torus d → ℝ) (K : ℝ), 0 ≤ K ∧
      (Measurable (fun p : Torus d × Torus d => Jt p.1 p.2) ∧ IsSymmPair Jt ∧
        IsCanonicalPair (withDensityReal ρ) Jt ∧
        ∀ x y, x ≠ y → |Jt x y| ≤ K₁ * wEnv s x y) ∧
      (Measurable (fun p : Torus d × Torus d => Bt p.1 p.2) ∧ IsSymmPair Bt ∧
        ∀ x y, x ≠ y → |Bt x y| ≤ K * wEnv s x y ^ 2) ∧
      (Measurable (fun p : Torus d × Torus d × Torus d => Gt p.1 p.2.1 p.2.2) ∧ IsSymmTriple Gt ∧
        IsCanonicalTriple (withDensityReal ρ) Gt ∧
        ∀ x y z, x ≠ y → x ≠ z → y ≠ z → |Gt x y z| ≤
          K * (wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z)) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ᵐ X ∂(canonicalGibbs (periodicRiesz d s) V N β),
        errStat d s ρ (N := N) ψ X =
          -(2 / (N : ℝ)) * Fstat (N := N) Jt X + (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum Gt X -
            (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered Bt X := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by rw [hcrit]; linarith
  have hK₁ := q84d_K_nonneg hd hcrit hψ
  have hsm := hψ.size.smooth
  have hsymm := hψ.symm
  obtain ⟨C, hC⟩ := Q84a.q84a_estimates hd hcrit β hβ V hV ρ hρ hρs
  obtain ⟨hG, hB⟩ := hC f K₁ ψ hf hψ
  obtain ⟨E, Jh, hE, hE0, hJh, hgood⟩ := q84d_jpair_modification (by omega) hsd hρs hf hψ
  have hJsymm : IsSymmPair (Jpair d s ρ ψ) := fun x y => Q84.q84_Jpair_symm hsymm x y
  obtain ⟨hJm, hJs, hJc, hJb, hJeq⟩ := q84d_Jtil_props (s := s) (by omega) hρs hE hE0 hJsymm hJh hgood
    hψ.jpair_canonical hK₁ hψ.jpair_bound
  have hK : 0 ≤ |C * K₁| := abs_nonneg _
  have hB' : ∀ x y : Torus d, x ≠ y → |Bpsi d s ρ ψ x y| ≤ |C * K₁| * wEnv s x y ^ 2 := fun x y hxy =>
    (hB x y hxy).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hG' : ∀ x y z : Torus d, x ≠ y → x ≠ z → y ≠ z → |Gpsi d s ρ ψ x y z| ≤
      |C * K₁| * (wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z) := by
    intro x y z hxy hxz hyz
    have w0 : ∀ a b : Torus d, 0 ≤ wEnv s a b := fun a b => zero_le_one.trans (PairCorrAux.one_le_wEnv s a b)
    exact (hG x y z hxy hxz hyz).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
      (add_nonneg (add_nonneg (mul_nonneg (w0 _ _) (w0 _ _)) (mul_nonneg (w0 _ _) (w0 _ _)))
        (mul_nonneg (w0 _ _) (w0 _ _))))
  obtain ⟨hBm, hBs, hBb, hBeq⟩ := q84d_Btil_props hsd hsymm hsm hK hB'
  obtain ⟨hGc, hGb⟩ := q84d_Gtil_props (s := s) (by omega) hsd hsymm hsm hE0 hgood hGcan hK hG'
  refine ⟨Jtil E Jh, Btil d s ρ ψ, Gtil d s ρ ψ E Jh, |C * K₁|, hK, ⟨hJm, hJs, hJc, hJb⟩,
    ⟨hBm, hBs, hBb⟩, ⟨q84d_measurable_Gtil hsd ρ ψ hE hJh, q84d_Gtil_symm ρ ψ E Jh, hGc, hGb⟩, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  filter_upwards [q84d_gibbs_ac.ae_le (q84d_ae_not_collision (N := N) (d := d) (by omega)),
    q84d_ae_not_mem_null (V := V) (β := β) (N := N) hE0 (periodicRiesz d s)] with X hX hXE
  have hXne : ∀ a b : Fin N, a ≠ b → X a ≠ X b := fun a b hab hXab => hX ⟨a, b, hab, hXab⟩
  have e1 : pairSumOrdered (Jpair d s ρ ψ) X = pairSumOrdered (Jtil E Jh) X := by
    unfold pairSumOrdered
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    exact (hJeq _ _ (hXE i) (hXE j) (hXne i j (Finset.ne_of_mem_erase hj).symm)).symm
  have e2 : tripleSum (Gpsi d s ρ ψ) X = tripleSum (Gtil d s ρ ψ E Jh) X := by
    unfold tripleSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    exact (q84d_Gtil_eq hsymm hsm hsd hgood (hXE i) (hXE j) (hXE k) (hXne i j hji.symm)
      (hXne i k hki.symm) (hXne j k hkj.symm)).symm
  have e3 : pairSumOrdered (Bpsi d s ρ ψ) X = pairSumOrdered (Btil d s ρ ψ) X := by
    unfold pairSumOrdered
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    exact (hBeq _ _ (hXne i j (Finset.ne_of_mem_erase hj).symm)).symm
  unfold errStat Fstat
  rw [e1, e2, e3]

end HRS.Q84d

end
