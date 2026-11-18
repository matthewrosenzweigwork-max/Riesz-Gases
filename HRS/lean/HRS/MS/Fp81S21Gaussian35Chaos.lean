import HRS.MS.Fp81S21Gaussian35SourceAgreement
import HRS.MS.Fp81S21GaussianSourceChaosZ
import HRS.MS.Fp81S21GaussianDChaos
import HRS.MS.Fp81S21GaussianCovChaos
import HRS.MS.Fp81S21GaussianCovPhysical

/-! Packet 35, unit 5: the literal selected totals have chaos certificates
for one and the same measurable retained source.

Binder adjustment: as in unit 2, `qsG` and `hcanon` are the realization-local
`canon.q src.G0` and `canon.payload src.G0`. This avoids importing the full
canonical-family module and its documented WindowSup/WickFam11 instance-name
collision. No family is reselected. Charts precede the trajectory and all
operator constants precede the window start. With selected data no radius is
needed: the conditional Z producer consumes the retained source evaluation
certificate directly. Unit 2 supplies coordinate chaos; the canonical payload
supplies the weak MomentRep. Thus neither is an additional analytic premise.

The covariance observation is the covariance operator composed with timeL2L1;
its agreement with Jcum is definitional. J remains projective-tensor-valued.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

local instance fp81s21_Gaussian35Chaos_measurableSpace (H : ℝ) :
    MeasurableSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := borel _
local instance fp81s21_Gaussian35Chaos_borelSpace (H : ℝ) :
    BorelSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- Same-source Gaussian law and vector-valued chaos for the selected window,
origin-zero drift total, and projective covariance total. -/
theorem fp81s21_gaussian35_chaos
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    {δ : ℝ} (R : Trajectory p δ)
    (hμ₀ : IsProbabilityMeasure (r26t3_mu R 0))
    (src : fp81s21_gaussian_source_retained_data p R hμ₀)
    (MUG : ℝ) (εG εB : ℕ → ℝ)
    (qsG : ℝ → src.G0.Ω → r26t6_Coeff)
    (hcanon : fp81s21_gaussian_canonical_time_payload p Es E src.G0.P
      (fun u ω f => OscDual.eval (src.G0.Z u ω) f) MUG qsG
      (fp81s21_gaussian_embedFamily p Es E qsG) εG)
    (S : fp81s21_QuadraticPhysical31 p R Es E εB)
    (cD KD cJ KJ : ℝ)
    (OD : ∀ a : ℝ, 0 ≤ a → r26t6_IntervalOperators E (r26t3_coeff R) p.T a cD KD)
    (OJ : ∀ a : ℝ, 0 ≤ a → r26t6_IntervalOperators E (r26t3_coeff R) p.T a cJ KJ)
    (UB UG : ∀ a : ℝ, 0 ≤ a → src.G0.Ω →
      Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T))))
    (hUB : ∀ a ha, fp81s21_TimeL2Rep src.G0.P (S.qe src.G0)
      (S.Kstar ^ 4 * S.B / 2) 0 (a + p.T) (UB a ha))
    (hUG : ∀ a ha, fp81s21_TimeL2Rep src.G0.P
      (fp81s21_gaussian_embedFamily p Es E qsG) MUG 0 (a + p.T) (UG a ha)) :
    let ξ' := fp81s21_gaussian_source_measurableXi src
    ∀ (a : ℝ) (ha : 0 ≤ a),
      IsCenteredGaussian (law src.G0.P (r26t3_Zpath src.G0 a)) ∧
      InFirstChaos src.G0.P ξ' 2 (r26t3_Zpath src.G0 a) ∧
      InSecondChaos src.G0.P ξ' 3
        (fp81s21_gaussian_Dcum (OD a ha) (add_nonneg ha p.hT.le) (UB a ha) (a + p.T)) ∧
      InFirstChaos src.G0.P ξ' 2
        (fun ω => (fp81s21_gaussian_Jcum (OJ a ha) (add_nonneg ha p.hT.le)
          (UG a ha) (a + p.T) ω : projTensor (Window p) 2)) := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ₀
  obtain ⟨hm, hξ, hsrc⟩ := fp81s21_gaussian_source_measurable_hsrc src
  have hcoord := (fp81s21_gaussian35_source_agreement p Es E R hμ₀ src
    MUG εG εB qsG hcanon S).2
  dsimp only
  intro a ha
  have hZ := fp81s21_retained_Z_firstChaos_conditional p R src.G0
    (fp81s21_gaussian_source_measurableXi src) hξ hm src.hK src.J src.W hsrc a ha
  refine ⟨hZ.2, hZ.1, ?_, ?_⟩
  · exact fp81s21_gaussian_Dcum_secondChaos src S
      (add_nonneg ha p.hT.le) (OD a ha) (UB a ha) (hUB a ha)
  · exact (fp81s21_gaussian_J_firstChaos E
      (fun u ω f => OscDual.eval (src.G0.Z u ω) f)
      (fp81s21_gaussian_embedFamily p Es E qsG) MUG (a + p.T)
      (add_nonneg ha p.hT.le) (UG a ha)
      (fp81s21_gaussian_source_measurableXi src) hξ hm
      hcanon.coefficients.weak_momentRep hcoord (hUG a ha)
      (((OJ a ha).covariance 0 (a + p.T)).comp
        (fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le)))
      (fp81s21_gaussian_Jcum (OJ a ha) (add_nonneg ha p.hT.le) (UG a ha)) rfl).2

#print axioms fp81s21_gaussian35_chaos
end HRS.Fp81.S21
end
