import HRS.MS.FinNoiseAux14
import HRS.Whole.Q09AAux2

/-!
# S8.6 `finite_noise`, final assembly modulo the covariance-root cost (S86)

`S86Cost` is the one remaining analytic input (Pro packet S8.6.07, the countable-chart bound for the symmetric
roots): for `r ∈ [0,H]` and any symmetric roots `S_r = (Σ_r)^{1/2}` of the empirical covariance form and
`Sb_r = Cdet_r^{1/2}` of the deterministic reference, `E ‖S_r - Sb_r‖²_{HS} ≤ C (N⁻¹ + δ_N²)`.

`s86_finite_noise_of_cost`: the frozen `HRS.Whole.finite_noise` follows from `S86Cost` (the features, their
measurability and boundedness, `IsHSIntegrand` on every horizon, `Cdet`, the adapted polar coupling and the
reconstruction estimate are all proved, packets P1-P2, 03-06, 08).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.FinNoise

open HRS HRS.Whole

/-- The covariance-root cost bound (open; Pro packet S8.6.07). -/
def S86Cost (d : ℕ) (a β m H Cin : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ → ∀ N : ℕ, 2 ≤ N →
    ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
      IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
    ∀ ℱ : Filtration ℝ mΩ,
      (∀ i : Fin N, IsProgressive ℱ (fun r z => X (Real.toNNReal r) z i)) →
      (∀ t ∈ Set.Icc (0 : ℝ) H, LinearInputBounds d ((d : ℝ) / 2) N (HRS.Whole.withDensityReal ρ) Cin P
        (X (Real.toNNReal t))) →
    ∀ r ∈ Set.Icc (0 : ℝ) H,
    ∀ D : KSpace d m H →L[ℝ] KSpace d m H →L[ℝ] ℝ,
      (∀ u v, D u v = featureForm m H β⁻¹
        (fun i => gradFeature (critCoeff d a β ρ) m H i r) (HRS.Whole.withDensityReal ρ) u v) →
    ∀ (ι : Type) [Countable ι] (e : HilbertBasis ι ℝ (KSpace d m H))
      (S : Ω → KSpace d m H →L[ℝ] KSpace d m H) (Sb : KSpace d m H →L[ℝ] KSpace d m H),
      (∀ z, IsSqrtOfForm (S z) (hsCovForm (fun ia : Fin N × Fin d =>
        Real.sqrt (2 / (N * β)) •
          gradFeature (critCoeff d a β ρ) m H ia.2 r (X (Real.toNNReal r) z ia.1)))) →
      IsSqrtOfForm Sb D →
      (∫⁻ z, ∑' j, ‖(S z - Sb) (e j)‖ₑ ^ 2 ∂P) ≤
        ENNReal.ofReal (C * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2))

theorem s86_sqrt_le (x δ : ℝ) (hx : 0 ≤ x) (hδ : 0 ≤ δ) :
    Real.sqrt (x + δ ^ 2) ≤ Real.sqrt x + δ := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hx, mul_nonneg (Real.sqrt_nonneg x) hδ]

theorem s86_deltaN_nonneg (d N : ℕ) (hN : 1 ≤ N) : 0 ≤ deltaN d ((d : ℝ) / 2) N := by
  unfold deltaN
  simp only [lt_irrefl, ite_false, ite_true]
  refine mul_nonneg (by positivity) (Real.log_nonneg ?_)
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith [Real.add_one_le_exp (1 : ℝ)]

theorem s86_finite_noise_of_cost
    (hcost : ∀ {d : ℕ}, 2 ≤ d → ∀ (a β : ℝ), 0 < a → 0 < β → ∀ (m : ℝ),
      (wholeSpaceIndex d : ℝ) ≤ m → ∀ (Hz : ℝ), 0 < Hz → ∀ Cin : ℝ, S86Cost d a β m Hz Cin) :
    type_of% @HRS.Whole.finite_noise := by
  intro d hd a β ha hβ m hm Hz hHz Cin
  obtain ⟨B, hB0, hdata⟩ := s86_feat_data hd a β ha hβ m hm Hz hHz
  obtain ⟨Ccost, hC0, hcostC⟩ := hcost hd a β ha hβ m hm Hz hHz Cin
  obtain ⟨K, hK0, hK⟩ := s86_coupling_maximal d m Hz hHz.le
  refine ⟨K * Real.sqrt Ccost, ?_⟩
  intro ρβ hρβ N hN Ω mΩ P hP X₀ W X hreal ℱ hW hprog hlin
  obtain ⟨hfeat, hbnd⟩ := hdata ρβ hρβ
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := HRS.Whole.Q09A.measure_isProb hρβ.1.1
  set Γ : Fin d → ℝ → Euc d → KSpace d m Hz := fun i r x =>
    gradFeature (critCoeff d a β ρβ) m Hz i (max r 0) x with hΓ
  have hΓm : ∀ i, Measurable (fun p : ℝ × Euc d => Γ i p.1 p.2) := fun i =>
    s86_feat_meas _ hfeat hHz.le i
  have hΓb : ∀ (i : Fin d) (r : ℝ) (x : Euc d), ‖Γ i r x‖ ≤ B := hbnd
  intro Φ
  have hHS : ∀ T : ℝ, IsHSIntegrand P ℱ T Φ :=
    s86_hs_all_horizons d N m Hz β B hB0 Γ hΓm hΓb P ℱ X hprog
  refine ⟨hHS Hz, fun M hM => ?_⟩
  obtain ⟨Cdet, hCdet, hform, -⟩ := s86_reference_density d m Hz β B hβ (HRS.Whole.withDensityReal ρβ) Γ hΓm hΓb
  have hformr : ∀ r ∈ Set.Icc (0 : ℝ) Hz, ∀ u v, Cdet r u v = featureForm m Hz β⁻¹
      (fun i => gradFeature (critCoeff d a β ρβ) m Hz i r) (HRS.Whole.withDensityReal ρβ) u v := by
    intro r hr u v
    rw [hform]
    simp only [hΓ, max_eq_left hr.1]
  refine ⟨Cdet, hformr, ?_⟩
  have hδ := s86_deltaN_nonneg d N (by omega)
  set A : ℝ := Ccost * ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2) with hA
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨Ω', mΩ', P', π, ℱ', ι, hι, e, B', S, Sb, G, hcoup, hbound⟩ :=
    hK P ℱ (Fin N × Fin d) (fun t z (ia : Fin N × Fin d) => W t z ia.1 ia.2) hW Φ hHS M hM Cdet hCdet
      A hA0 (by
        intro r hr ι hι e S Sb hS hSb
        refine hcostC ρβ hρβ N hN P X₀ W X hreal ℱ hprog hlin r hr (Cdet r) (hformr r hr) ι e S Sb ?_ hSb
        intro z
        have := hS z
        simp only [Φ, max_eq_left hr.1] at this
        exact this)
  refine ⟨Ω', mΩ', P', π, ℱ', ι, hι, e, B', S, Sb, G, hcoup, ?_⟩
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : Real.sqrt A = Real.sqrt Ccost * Real.sqrt ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2) :=
    Real.sqrt_mul hC0 _
  have h2 := s86_sqrt_le ((N : ℝ)⁻¹) (deltaN d ((d : ℝ) / 2) N) (by positivity) hδ
  have h3 : Real.sqrt ((N : ℝ)⁻¹) = (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (by positivity), Real.inv_rpow (by positivity)]
  rw [h3] at h2
  calc K * Real.sqrt A = K * Real.sqrt Ccost *
        Real.sqrt ((N : ℝ)⁻¹ + deltaN d ((d : ℝ) / 2) N ^ 2) := by rw [h1]; ring
    _ ≤ K * Real.sqrt Ccost * ((N : ℝ) ^ (-(1 / 2 : ℝ)) + deltaN d ((d : ℝ) / 2) N) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

end HRS.MS.FinNoise
