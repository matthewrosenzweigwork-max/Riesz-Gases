import HRS.MS.SA16Y4Id2

/-!
# S.A.16 (SA16Y4) Id3: the `eq` and `integrable_σ` fields of `IsForwardSolutionRd` from the limit identity

`sa16y4_eq_field`: from `ℓ_ψ(G τ) = ∫φψ + ∫_0^τ forwardWeakTerm` (interval integral) the frozen form
`∫ F τ ψ = ∫ φ ψ + ∫_{[0,τ]} forwardWeakTerm` for `F τ = wrep (G τ)`.
`sa16y4_integrableOn_limit`: a pointwise limit of continuous, uniformly bounded functions on `[0,t]` is integrable there
(the `integrable_σ` field: the weak term is the pointwise limit of the integrands `f_n`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Id3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y4_eq_field {m : ℕ} (C : WholeCoeff d) (t : ℝ) (G : ℝ → WmpSpace d m p)
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ)
    (hid : ∀ τ ∈ Icc (0 : ℝ) t, sa16r_ell d m p hψ (G τ) = (∫ x, φ x * ψ x) +
      ∫ σ in (0 : ℝ)..τ, forwardWeakTerm C t (fun τ x => wrep d m p (G τ) x) ψ σ) :
    ∀ τ ∈ Icc (0 : ℝ) t, ∫ x, (fun τ x => wrep d m p (G τ) x) τ x * ψ x = (∫ x, φ x * ψ x) +
      ∫ σ in Icc (0 : ℝ) τ, forwardWeakTerm C t (fun τ x => wrep d m p (G τ) x) ψ σ := by
  intro τ hτ
  have := hid τ hτ
  rw [sa16r_ell_apply, intervalIntegral.integral_of_le hτ.1] at this
  rw [integral_Icc_eq_integral_Ioc]
  exact this

theorem sa16y4_integrableOn_limit {t Lf : ℝ} (f : ℕ → ℝ → ℝ) (flim : ℝ → ℝ)
    (hfc : ∀ n, ContinuousOn (f n) (Icc 0 t)) (hfb : ∀ n, ∀ σ ∈ Icc (0 : ℝ) t, |f n σ| ≤ Lf)
    (hf : ∀ σ ∈ Icc (0 : ℝ) t, Tendsto (fun n => f n σ) atTop (𝓝 (flim σ))) :
    IntegrableOn flim (Icc 0 t) := by
  have hmeas : AEStronglyMeasurable flim (volume.restrict (Icc 0 t)) := by
    refine aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := f) (g := flim) ?_ ?_
    · exact fun n => (hfc n).aestronglyMeasurable measurableSet_Icc
    · rw [ae_restrict_iff' measurableSet_Icc]
      exact Eventually.of_forall hf
  show Integrable flim (volume.restrict (Icc 0 t))
  refine Integrable.mono' (g := fun _ => Lf) (integrable_const Lf) hmeas ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Eventually.of_forall fun σ hσ => ?_
  rw [Real.norm_eq_abs]
  exact le_of_tendsto' (hf σ hσ).abs fun n => hfb n σ hσ

end Id3

end HRS.Whole.AppendixA.Phase2SA16R
