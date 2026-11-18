import HRS.Uniform.Q45Gauss

/-!
# Q45 (Lemma 3.20): covariances of martingale increments
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

section Orth

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}

/-- Orthogonality of a martingale increment to the past (in `L²`). -/
lemma martingale_orth {f : ℝ → Ω → ℝ} (hf : Martingale f ℱ P) {a b : ℝ} (hab : a ≤ b)
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ a] ξ) (hξ2 : MemLp ξ 2 P) (hfb : MemLp (f b) 2 P)
    (hfa : MemLp (f a) 2 P) :
    ∫ ω, ξ ω * (f b ω - f a ω) ∂P = 0 := by
  have h1 : Integrable (fun ω => ξ ω * f b ω) P := hξ2.integrable_mul hfb
  have h2 : Integrable (fun ω => ξ ω * f a ω) P := hξ2.integrable_mul hfa
  have h3 : ∫ ω, ξ ω * f b ω ∂P = ∫ ω, ξ ω * f a ω ∂P := by
    calc ∫ ω, ξ ω * f b ω ∂P = ∫ ω, (P[(fun ω => ξ ω * f b ω) | ℱ a]) ω ∂P :=
          (integral_condExp (ℱ.le a)).symm
      _ = ∫ ω, (ξ * P[f b | ℱ a]) ω ∂P :=
          integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hξ h1 (hf.integrable b))
      _ = ∫ ω, ξ ω * f a ω ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hf.condExp_ae_eq hab] with ω hω
          simp [hω]
  simp_rw [mul_sub]
  rw [integral_sub h1 h2, h3, sub_self]

end Orth

section HilbertM

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {T : ℝ} {M : ℝ → Ω → H} {Dd : ℝ → H →L[ℝ] H →L[ℝ] ℝ}

lemma HM_memLp (hM : IsHilbertMartingaleWithCovariation P ℱ T M (fun r _ => Dd r)) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) T) (x : H) : MemLp (fun ω => inner ℝ (M τ ω) x) 2 P :=
  (hM.sq_int τ hτ).inner_const (𝕜 := ℝ) x

lemma HM_adapted (hM : IsHilbertMartingaleWithCovariation P ℱ T M (fun r _ => Dd r)) (x : H) (τ : ℝ) :
    StronglyMeasurable[ℱ τ] (fun ω => inner ℝ (M τ ω) x) :=
  (hM.martingale x).1 τ

/-- Increments over disjoint intervals are orthogonal. -/
lemma HM_incr_orth (hM : IsHilbertMartingaleWithCovariation P ℱ T M (fun r _ => Dd r))
    {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hdT : d ≤ T) (x y : H) :
    ∫ ω, (inner ℝ (M b ω) x - inner ℝ (M a ω) x) * (inner ℝ (M d ω) y - inner ℝ (M c ω) y) ∂P = 0 := by
  have hb : b ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans hab, hbc.trans (hcd.trans hdT)⟩
  have hamem : a ∈ Set.Icc (0 : ℝ) T := ⟨ha, hab.trans (hbc.trans (hcd.trans hdT))⟩
  have hc : c ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans (hab.trans hbc), hcd.trans hdT⟩
  have hd : d ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans (hab.trans (hbc.trans hcd)), hdT⟩
  refine martingale_orth (hM.martingale y) hcd ?_ ?_ (HM_memLp hM hd y) (HM_memLp hM hc y)
  · have h1 : StronglyMeasurable[ℱ c] (fun ω => inner ℝ (M b ω) x) :=
      (HM_adapted hM x b).mono (ℱ.mono hbc)
    have h2 : StronglyMeasurable[ℱ c] (fun ω => inner ℝ (M a ω) x) :=
      (HM_adapted hM x a).mono (ℱ.mono (hab.trans hbc))
    exact h1.sub h2
  · exact (HM_memLp hM hb x).sub (HM_memLp hM hamem x)

end HilbertM

end HRS.Uniform.Q45
