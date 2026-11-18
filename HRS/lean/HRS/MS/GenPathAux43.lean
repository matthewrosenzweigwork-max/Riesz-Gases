import HRS.MS.GenPathAux42

/-!
# S5.6 packet P8b: a Hilbert martingale with deterministic covariation does not move in a direction
that is invisible to the covariation density
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem s56_incr_zero {T : ℝ} {G : ℝ → Ω → H} {C : ℝ → H →L[ℝ] H →L[ℝ] ℝ}
    (hG : IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => C r)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (v : H) (hv : ∀ σ ∈ Set.Ioc t T, C σ v v = 0) :
    (fun ζ => inner ℝ (G T ζ) v) =ᵐ[P] fun ζ => inner ℝ (G t ζ) v := by
  set f : ℝ → Ω → ℝ := fun τ ζ => inner ℝ (G τ ζ) v with hf
  have hT : (T : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.trans ht.2, le_rfl⟩
  have hL2 : ∀ τ ∈ Set.Icc (0 : ℝ) T, MemLp (f τ) 2 P := fun τ hτ => (hG.sq_int τ hτ).inner_const v
  have hmart := hG.martingale v
  have hcov := hG.covariation v v
  obtain ⟨ω₀, hω₀⟩ := hG.sigma_entry_int.exists
  have hCint : IntegrableOn (fun σ => C σ v v) (Set.Icc 0 T) := hω₀ v v
  -- (1) orthogonality of the increment
  have hle : (ℱ t) ≤ mΩ := ℱ.le t
  have h1 : ∫ ζ, f t ζ * f T ζ ∂P = ∫ ζ, f t ζ * f t ζ ∂P := by
    haveI : SigmaFinite (P.trim hle) := inferInstance
    have hmt : StronglyMeasurable[ℱ t] (f t) := hmart.stronglyAdapted t
    have hint : Integrable (f t * f T) P := (hL2 t ht).integrable_mul (hL2 T hT)
    have e1 := condExp_mul_of_stronglyMeasurable_left hmt hint ((hL2 T hT).integrable one_le_two)
    have e2 := hmart.condExp_ae_eq ht.2
    calc ∫ ζ, f t ζ * f T ζ ∂P = ∫ ζ, (P[f t * f T | ℱ t]) ζ ∂P := (integral_condExp hle).symm
      _ = ∫ ζ, (f t * P[f T | ℱ t]) ζ ∂P := integral_congr_ae e1
      _ = ∫ ζ, f t ζ * f t ζ ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [e2] with ζ hζ
          simp only [Pi.mul_apply]
          rw [show (P[f T | ℱ t]) ζ = inner ℝ (G t ζ) v from hζ]
  -- (2) the covariation martingale
  have hcm : ∫ ζ, (f T ζ * f T ζ - ∫ σ in Set.Icc 0 T, C σ v v) ∂P =
      ∫ ζ, (f t ζ * f t ζ - ∫ σ in Set.Icc 0 t, C σ v v) ∂P := by
    have := hcov.setIntegral_eq ht.2 (MeasurableSet.univ : MeasurableSet[ℱ t] Set.univ)
    simp only [Measure.restrict_univ] at this
    exact this.symm
  have hI1 : Integrable (fun ζ => f T ζ * f T ζ) P := (hL2 T hT).integrable_mul (hL2 T hT)
  have hI2 : Integrable (fun ζ => f t ζ * f t ζ) P := (hL2 t ht).integrable_mul (hL2 t ht)
  rw [integral_sub hI1 (integrable_const _), integral_sub hI2 (integrable_const _)] at hcm
  simp only [integral_const, smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one, one_mul] at hcm
  -- (3) the covariation increment vanishes
  have hsplit : ∫ σ in Set.Icc 0 T, C σ v v = (∫ σ in Set.Icc 0 t, C σ v v) + ∫ σ in Set.Ioc t T, C σ v v := by
    rw [← Set.Icc_union_Ioc_eq_Icc ht.1 ht.2, setIntegral_union (Set.disjoint_left.2 fun a ha hb =>
      absurd ha.2 (not_le.2 hb.1)) measurableSet_Ioc
      (hCint.mono_set (Set.Icc_subset_Icc le_rfl ht.2)) (hCint.mono_set (Set.Ioc_subset_Icc_self.trans
        (Set.Icc_subset_Icc ht.1 le_rfl)))]
  have hzero : ∫ σ in Set.Ioc t T, C σ v v = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun σ hσ => hv σ hσ
  -- (4) the second moment of the increment
  have hsq : ∫ ζ, (f T ζ - f t ζ) ^ 2 ∂P = 0 := by
    have hexp : ∀ ζ, (f T ζ - f t ζ) ^ 2 = f T ζ * f T ζ - 2 * (f t ζ * f T ζ) + f t ζ * f t ζ := fun ζ => by ring
    simp_rw [hexp]
    have hI3 : Integrable (fun ζ => f t ζ * f T ζ) P := (hL2 t ht).integrable_mul (hL2 T hT)
    have hA : Integrable (fun ζ => f T ζ * f T ζ - 2 * (f t ζ * f T ζ)) P := hI1.sub (hI3.const_mul 2)
    have hB : Integrable (fun ζ => 2 * (f t ζ * f T ζ)) P := hI3.const_mul 2
    rw [integral_add hA hI2, integral_sub hI1 hB, integral_const_mul, h1]
    rw [hsplit, hzero, add_zero] at hcm
    linarith
  have hnn : 0 ≤ᵐ[P] fun ζ => (f T ζ - f t ζ) ^ 2 := Filter.Eventually.of_forall fun ζ => sq_nonneg _
  have hint : Integrable (fun ζ => (f T ζ - f t ζ) ^ 2) P := by
    have := ((hL2 T hT).sub (hL2 t ht)).integrable_sq
    exact this
  have := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 hsq
  filter_upwards [this] with ζ hζ
  have : f T ζ - f t ζ = 0 := by
    simpa using hζ
  linarith

end HRS.MS.GenPath
