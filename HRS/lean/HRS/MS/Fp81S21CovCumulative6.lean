import HRS.MS.Fp81S21CovCumulative5
import HRS.MS.Fp81S21DriftCumulative6
import HRS.MS.S21G2_K06

/-!
# HRS S2.1(iii), packet 19c-i: measurable covariance cumulative contract

This stage records the full measurable-in-particle cumulative contract and
upgrades any selected covariance cumulative with measurable time sections to a
measurable continuous version.  The physical fixed-time measurability proof is
left as the remaining bridge.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas

/-- The full packet 19c-i contract, including a jointly measurable-in-time
choice of cumulative sections.  The origin is fixed for every sample; all
other path and covariance assertions hold almost surely. -/
def fp81s21_rawEtaCovarianceMeasurableCumulativeSpec (p : Parameters) : Prop :=
  ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
        fp81s21_moving_heat_full_clause p R future ∧
        ∀ a (ha : 0 ≤ a) N (hN : 2 ≤ N) (A : Particle R N),
          let H := a + p.T
          let B_H := OscPath p.d (wholeSpaceIndex p.d : ℝ) H
          ∃ Fj : A.Ω → ℝ → projTensor B_H 2,
            ∃ V : A.Ω → ℝ,
              (∀ t : ℝ, Measurable (fun ω => Fj ω t)) ∧
              Integrable V A.P ∧
              (∀ ω, Fj ω 0 = 0) ∧
              ∀ᵐ ω ∂A.P,
                (∀ q r : ℝ, 0 ≤ q → q ≤ r → r ≤ H →
                  IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
                    (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
                    (((Fj ω r - Fj ω q : projTensor B_H 2) : TensorDual B_H 2))) ∧
                ContinuousOn (Fj ω) (Icc 0 H) ∧
                BoundedVariationOn (Fj ω) (Icc 0 H) ∧
                (eVariationOn (Fj ω) (Icc 0 H)).toReal ≤ V ω

/-- If the selected raw covariance cumulative has a.e. continuous BV paths,
measurable fixed-time sections, and an integrable variation majorant, then it
has a measurable continuous version preserving every physical interval value. -/
theorem fp81s21_covariance_measurable_continuous_version_of_sections
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ) (hH : 0 < H)
    {N : ℕ} (A : Particle R N)
    (F : A.Ω → ℝ → projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2)
    (V : A.Ω → ℝ)
    (hsections : ∀ t : ℝ, AEMeasurable (fun ω => F ω t) A.P)
    (hV : Integrable V A.P)
    (hraw : ∀ᵐ ω ∂A.P,
      F ω 0 = 0 ∧
      (∀ q r : ℝ, 0 ≤ q → q ≤ r → r ≤ H →
        IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
          (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
          (((F ω r - F ω q : projTensor
            (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2) : TensorDual
            (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2))) ∧
      ContinuousOn (F ω) (Icc 0 H) ∧
      BoundedVariationOn (F ω) (Icc 0 H) ∧
      (eVariationOn (F ω) (Icc 0 H)).toReal ≤ V ω) :
    ∃ Fj : A.Ω → ℝ → projTensor
        (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2,
      (∀ t : ℝ, Measurable (fun ω => Fj ω t)) ∧
      Integrable V A.P ∧
      (∀ ω, Fj ω 0 = 0) ∧
      ∀ᵐ ω ∂A.P,
        (∀ q r : ℝ, 0 ≤ q → q ≤ r → r ≤ H →
          IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
            (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
            (((Fj ω r - Fj ω q : projTensor
              (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2) : TensorDual
              (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2))) ∧
        ContinuousOn (Fj ω) (Icc 0 H) ∧
        BoundedVariationOn (Fj ω) (Icc 0 H) ∧
        (eVariationOn (Fj ω) (Icc 0 H)).toReal ≤ V ω := by
  classical
  let E := projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2
  haveI : SecondCountableTopology E :=
    HRS.MS.R26T3.s21g2_k06_sc
      (B := OscPath p.d (wholeSpaceIndex p.d : ℝ) H) 2
  obtain ⟨s, hs, hd⟩ : ∃ s : Set (Icc (0 : ℝ) H), s.Countable ∧ Dense s :=
    TopologicalSpace.exists_countable_dense _
  have hm : ∀ t ∈ s, AEMeasurable (fun ω => F ω t) A.P := by
    intro t ht
    exact hsections t
  have hc : ∀ᵐ ω ∂A.P, ContinuousOn (F ω) (Icc 0 H) :=
    hraw.mono fun ω hω => hω.2.2.1
  obtain ⟨G, hG, hGc, hGe⟩ :=
    fp81s21_dense_measurable_continuous_version A.P H F s hs hd hm hc
  let Fj : A.Ω → ℝ → E := fun ω t => G ω t - G ω 0
  have hFjmeas : ∀ t : ℝ, Measurable (fun ω => Fj ω t) := by
    intro t
    exact (hG t).sub (hG 0)
  have hFjcont : ∀ ω, ContinuousOn (Fj ω) (Icc 0 H) := by
    intro ω
    exact (hGc ω).sub continuousOn_const
  have hFjeq : ∀ᵐ ω ∂A.P, ∀ t ∈ Icc (0 : ℝ) H, Fj ω t = F ω t := by
    filter_upwards [hGe, hraw] with ω he hω
    intro t ht
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) H := ⟨le_rfl, hH.le⟩
    simp [Fj, he t ht, he 0 h0, hω.1]
  refine ⟨Fj, hFjmeas, hV, ?_, ?_⟩
  · intro ω
    simp [Fj]
  · filter_upwards [hFjeq, hraw] with ω he hω
    have heq : EqOn (Fj ω) (F ω) (Icc (0 : ℝ) H) := fun t ht => he t ht
    have hvar : eVariationOn (Fj ω) (Icc 0 H) =
        eVariationOn (F ω) (Icc 0 H) := eVariationOn.congr heq
    refine ⟨?_, hFjcont ω, ?_, ?_⟩
    · intro q r hq hqr hr
      rw [he r ⟨hq.trans hqr, hr⟩, he q ⟨hq, hqr.trans hr⟩]
      exact hω.2.1 q r hq hqr hr
    · unfold BoundedVariationOn at *
      rw [hvar]
      exact hω.2.2.2.1
    · rw [hvar]
      exact hω.2.2.2.2

#print axioms HRS.Fp81.S21.fp81s21_rawEtaCovarianceMeasurableCumulativeSpec
#print axioms HRS.Fp81.S21.fp81s21_covariance_measurable_continuous_version_of_sections

end HRS.Fp81.S21

end
