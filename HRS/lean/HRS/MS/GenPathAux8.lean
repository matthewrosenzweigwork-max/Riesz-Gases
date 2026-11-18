import HRS.MS.GenPathAux7
import HRS.Main.A34Aux20

/-!
# S5.6 packet P9a, part 3: the smooth comparison of `𝒦`-valued martingale paths after reconstruction

`s56_smoothDist_coupling_ae`: `d_{C_b²}(Law X, Law G) ≤ E‖X - G‖` for a.e.-measurable `X, G` (`ℝ≥0∞` form).
`s56_smooth_abstract`: Proposition 3.21 (`smooth_path_comparison_proof`) applied to the `𝒦`-valued martingales
`k₀ + M_·` and `k₀ + G_·` with the identity evolution (`s56_idEvol`), followed by the bounded reconstruction map `𝒯`
(`s56_reconCLM`) and the remainder `R` (1-Lipschitz perturbation):
`d_{C_b²}(Law(A(k₀) + 𝒯M + R), Law(A(k₀) + 𝒯G)) ≤ C E∫_0^T‖Σ_r - C̄_r‖_{𝔖₁}dr + E‖R‖_{C_tℓ²}`,
`A(k₀)(t) = (k₀).evalA t` the initial path (an `H¹_tℓ²` path), `C` depending only on `T`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.U9

theorem s56_smoothDist_coupling_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [SecondCountableTopology B] (X G : Ω → B) (hX : AEMeasurable X P) (hG : AEMeasurable G P) :
    ENNReal.ofReal (smoothDist 2 (P.map X) (P.map G)) ≤ ∫⁻ ζ, ‖X ζ - G ζ‖ₑ ∂P := by
  set X' := hX.mk X with hX'
  set G' := hG.mk G with hG'
  have e1 : P.map X = P.map X' := Measure.map_congr hX.ae_eq_mk
  have e2 : P.map G = P.map G' := Measure.map_congr hG.ae_eq_mk
  have hae : (fun ζ => ‖X ζ - G ζ‖ₑ) =ᵐ[P] fun ζ => ‖X' ζ - G' ζ‖ₑ := by
    filter_upwards [hX.ae_eq_mk, hG.ae_eq_mk] with ζ h1 h2
    rw [h1, h2]
  rw [e1, e2, lintegral_congr_ae hae]
  by_cases htop : ∫⁻ ζ, ‖X' ζ - G' ζ‖ₑ ∂P = ⊤
  · rw [htop]; exact le_top
  have hmX : Measurable X' := hX.measurable_mk
  have hmG : Measurable G' := hG.measurable_mk
  have hint' : Integrable (fun ζ => X' ζ - G' ζ) P := by
    refine ⟨(hmX.sub hmG).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    exact lt_top_iff_ne_top.2 htop
  have hint : Integrable (fun ζ => ‖X' ζ - G' ζ‖) P := hint'.norm
  have h := HRS.A34.a34_smoothDist_coupling P X' G' hmX hmG hint
  calc ENNReal.ofReal (smoothDist 2 (P.map X') (P.map G')) ≤ ENNReal.ofReal (∫ ζ, ‖X' ζ - G' ζ‖ ∂P) :=
        ENNReal.ofReal_le_ofReal h
    _ = ∫⁻ ζ, ‖X' ζ - G' ζ‖ₑ ∂P := ofReal_integral_norm_eq_lintegral_enorm hint'

end HRS.MS.GenPath
