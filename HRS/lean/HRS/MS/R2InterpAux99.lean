import HRS.MS.R2InterpAux98

/-!
# S10.2 (worker S10R), part 99 (packet F5n): coordinates of the drift integral of the Itô representation
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ}

theorem s102_bd_integral_coord (hT : 0 < T) (L : ℕ) (sQ : ℝ) (μ : Measure (Euc d)) {N : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) (u : ℝ)
    (hint : ∀ i, IntegrableOn (fun s => s102_bdc C m hT L sQ μ P X i s ζ) (Icc 0 u)) (i : Fin (s102_q d L)) :
    (∫ s in Icc 0 u, s102_bdE C m hT L sQ μ P X s ζ) i = ∫ s in Icc 0 u, s102_bdc C m hT L sQ μ P X i s ζ := by
  have hI : IntegrableOn (fun s => s102_bdE C m hT L sQ μ P X s ζ) (Icc 0 u) :=
    s102_integrableOn_E _ hint
  have := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hI
  exact this.symm

theorem s102_bdc_integral (hT : 0 < T) (L : ℕ) (sQ : ℝ) (μ : Measure (Euc d)) {N : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) {u : ℝ} (hu : 0 ≤ u)
    (i : Fin (s102_q d L)) :
    ∫ s in Icc 0 u, s102_bdc C m hT L sQ μ P X i s ζ =
      ∫ s in Icc 0 (min u (s102_tk hT L i)),
        (-(Real.sqrt N)⁻¹ * r2QuadField sQ μ P X s ζ (s102_orb C m hT L i s)) := by
  have h1 : ∀ s ∈ Icc (0 : ℝ) u, s102_bdc C m hT L sQ μ P X i s ζ =
      (Iic (s102_tk hT L i)).indicator
        (fun s => -(Real.sqrt N)⁻¹ * r2QuadField sQ μ P X s ζ (s102_orb C m hT L i s)) s := by
    intro s hs
    unfold s102_bdc s102_hh
    rw [if_pos hs.1]
    by_cases hst : s ≤ s102_tk hT L i
    · rw [indicator_of_mem (show s ∈ Iic _ from hst), indicator_of_mem (show s ∈ Iic (s102_tauk hT L i : ℝ) from hst)]
      rfl
    · rw [indicator_of_notMem (show s ∉ Iic _ from hst), indicator_of_notMem (show s ∉ Iic (s102_tauk hT L i : ℝ) from hst)]
      simp
  have hset : Icc (0 : ℝ) u ∩ Iic (s102_tk hT L i) = Icc 0 (min u (s102_tk hT L i)) := by
    ext s
    simp only [mem_inter_iff, mem_Icc, mem_Iic, le_min_iff]
    tauto
  rw [setIntegral_congr_fun measurableSet_Icc h1, setIntegral_indicator measurableSet_Iic, hset]

end HRS.MS.R2Interp

end
