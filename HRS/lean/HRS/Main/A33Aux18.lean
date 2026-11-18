import Mathlib
import HRS.Main.A33Aux17

/-!
# Packet A33, helper 18: the centred Gaussian noise field (part (1) of Proposition A.33)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A33

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

theorem a33_noise_exists (S : A33Setup d) (q : ℝ) (hq : 0 ≤ q) {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) :
    ∃ νG : Measure (NegSobolev d (S.J : ℝ)), IsProbabilityMeasure νG ∧ IsCenteredGaussian νG ∧
      ∀ φ ψ : Torus d → ℝ, Torus.IsSmooth φ → Torus.IsSmooth ψ →
        ∫ F, NegSobolev.eval F φ * NegSobolev.eval F ψ ∂νG = noiseCovariance S.D S.ρ q t φ ψ := by
  classical
  obtain ⟨e⟩ := a33_exists_equiv S.hd
  obtain ⟨Ω, mΩ, P, hP, W, hm, h2, hl, hf, hi, hs1, hg⟩ :=
    a33_isonormal (Lp (Euc d) 2 (a33_nu d S.T S.ρ))
  have hI : A33Iso P W := ⟨hm, h2, hl, hf, hi, hs1, hg⟩
  haveI := hP
  have hGm := a33_Gfield_meas S q W e hI t
  refine ⟨P.map (a33_Gfield S q W t), (Measure.isProbabilityMeasure_map_iff hGm.aemeasurable).2 inferInstance, ?_, ?_⟩
  · have hG : IsGaussian (P.map (a33_Gfield S q W t)) := by
      refine isGaussian_of_map_eq_gaussianReal fun L => ?_
      obtain ⟨v, hv⟩ := a33_noise_map_gaussian S q W hI e ht L
      exact ⟨0, v, hv⟩
    refine ⟨hG, fun L => ?_⟩
    obtain ⟨v, hv⟩ := a33_noise_map_gaussian S q W hI e ht L
    have h1 : ∫ z, L z ∂(P.map (a33_Gfield S q W t)) =
        ∫ x, x ∂((P.map (a33_Gfield S q W t)).map L) :=
      (integral_map L.continuous.measurable.aemeasurable aestronglyMeasurable_id).symm
    rw [h1, hv, integral_id_gaussianReal]
  · intro φ ψ hφ hψ
    have hfm : Measurable fun F : NegSobolev d (S.J : ℝ) => NegSobolev.eval F φ * NegSobolev.eval F ψ :=
      (a33_eval_measurable e (a33_ws_smooth (S.J : ℝ) hφ)).mul
        (a33_eval_measurable e (a33_ws_smooth (S.J : ℝ) hψ))
    rw [integral_map hGm.aemeasurable hfm.aestronglyMeasurable]
    have hae : ∀ᵐ ω ∂P, NegSobolev.eval (a33_Gfield S q W t ω) φ *
        NegSobolev.eval (a33_Gfield S q W t ω) ψ =
        W (a33_vec S q t φ) ω * W (a33_vec S q t ψ) ω := by
      filter_upwards [a33_eval_ae S q W e hI ht hφ, a33_eval_ae S q W e hI ht hψ] with ω h1 h2
      rw [h1, h2]
    rw [integral_congr_ae hae, hI.inner, S.gram q hq ht ht hφ hψ, min_self]
    rfl

end HRS.A33
