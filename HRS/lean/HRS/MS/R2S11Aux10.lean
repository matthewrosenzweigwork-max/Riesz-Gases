import HRS.MS.R2S11Aux9

/-!
# S11.4 item (5), measurability: a jointly measurable version of the particle path, and the joint measurability of
the pair energy in (time, configuration) for time-dependent kernels and densities
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2S11

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- A jointly measurable modification of a process with a.s. continuous paths and measurable time slices. -/
theorem s11_X_joint {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}
    {X : ℝ≥0 → Ω → EucConfig d N} (hm : ∀ t, Measurable (X t))
    (hc : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ζ i) :
    ∃ X' : ℝ × Ω → EucConfig d N, Measurable X' ∧ ∀ᵐ ζ ∂P, ∀ t : ℝ, X' (t, ζ) = X t.toNNReal ζ := by
  classical
  obtain ⟨S, hSsub, hSm, hS0⟩ := exists_measurable_superset_of_null (ae_iff.1 hc)
  set u : ℝ → Ω → EucConfig d N := fun t ζ => if ζ ∈ S then 0 else X t.toNNReal ζ with hu
  have hcont : ∀ ζ, Continuous fun t : ℝ => u t ζ := by
    intro ζ
    by_cases hζ : ζ ∈ S
    · simp only [hu, hζ, if_true]; exact continuous_const
    · simp only [hu, hζ, if_false]
      have : ∀ i, Continuous fun t : ℝ≥0 => X t ζ i := by
        by_contra hcon
        exact hζ (hSsub (by simpa using hcon))
      exact continuous_pi fun i => (this i).comp continuous_real_toNNReal
  have hmeas : ∀ t, Measurable (u t) := fun t => by
    simp only [hu]
    exact Measurable.ite hSm measurable_const (hm _)
  refine ⟨Function.uncurry u, measurable_uncurry_of_continuous_of_measurable hcont hmeas, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hS0] with ζ hζ t
  simp [Function.uncurry, hu, hζ]

/-- The pair energy is jointly measurable in (time, configuration) for time-dependent kernels and densities. -/
theorem s11_pairEnergy_meas {N : ℕ} (h : ℝ → Euc d → Euc d → ℝ)
    (hh : Measurable fun p : ℝ × Euc d × Euc d => h p.1 p.2.1 p.2.2)
    (ρ : ℝ → Euc d → ℝ) (hρ : Measurable fun p : ℝ × Euc d => ρ p.1 p.2) :
    Measurable fun p : ℝ × EucConfig d N => pairEnergy (h p.1) p.2 (HRS.Whole.withDensityReal (ρ p.1)) := by
  have hw : ∀ t : ℝ, (∀ᵐ y : Euc d ∂volume, ENNReal.ofReal (ρ t y) < ⊤) := fun t =>
    Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top
  have hconv : ∀ (t : ℝ) (g : Euc d → ℝ), ∫ y, g y ∂(HRS.Whole.withDensityReal (ρ t)) =
      ∫ y, (ENNReal.ofReal (ρ t y)).toReal * g y := fun t g => by
    have hmt : Measurable fun y => ENNReal.ofReal (ρ t y) :=
      ENNReal.measurable_ofReal.comp (hρ.comp (measurable_const.prodMk measurable_id))
    unfold HRS.Whole.withDensityReal
    rw [integral_withDensity_eq_integral_toReal_smul hmt (hw t) g]
    simp only [smul_eq_mul]
  have hρ' : Measurable fun p : ℝ × Euc d => (ENNReal.ofReal (ρ p.1 p.2)).toReal :=
    (ENNReal.measurable_ofReal.comp hρ).ennreal_toReal
  -- G1(t, x) = ∫ y, h t x y dμ_t(y)
  have hG1 : Measurable fun q : ℝ × Euc d => ∫ y, h q.1 q.2 y ∂(HRS.Whole.withDensityReal (ρ q.1)) := by
    have hF : Measurable fun z : (ℝ × Euc d) × Euc d =>
        (ENNReal.ofReal (ρ z.1.1 z.2)).toReal * h z.1.1 z.1.2 z.2 := by
      refine Measurable.mul ?_ ?_
      · exact hρ'.comp (measurable_fst.fst.prodMk measurable_snd)
      · exact hh.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
    have h1 := (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Euc d)))).measurable
    have e : (fun q : ℝ × Euc d => ∫ y, h q.1 q.2 y ∂(HRS.Whole.withDensityReal (ρ q.1))) =
        fun q => ∫ y, (ENNReal.ofReal (ρ q.1 y)).toReal * h q.1 q.2 y := funext fun q => hconv q.1 _
    rw [e]
    exact h1
  have hG2 : Measurable fun t : ℝ => ∫ x, ∫ y, h t x y ∂(HRS.Whole.withDensityReal (ρ t))
      ∂(HRS.Whole.withDensityReal (ρ t)) := by
    have hF : Measurable fun z : ℝ × Euc d =>
        (ENNReal.ofReal (ρ z.1 z.2)).toReal * ∫ y, h z.1 z.2 y ∂(HRS.Whole.withDensityReal (ρ z.1)) :=
      hρ'.mul hG1
    have h1 := (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Euc d)))).measurable
    have e : (fun t : ℝ => ∫ x, ∫ y, h t x y ∂(HRS.Whole.withDensityReal (ρ t))
        ∂(HRS.Whole.withDensityReal (ρ t))) = fun t => ∫ x, (ENNReal.ofReal (ρ t x)).toReal *
          ∫ y, h t x y ∂(HRS.Whole.withDensityReal (ρ t)) := funext fun t => hconv t _
    rw [e]
    exact h1
  have hXi : ∀ i : Fin N, Measurable fun p : ℝ × EucConfig d N => p.2 i := fun i =>
    (measurable_pi_apply i).comp measurable_snd
  have T1 : Measurable fun p : ℝ × EucConfig d N =>
      ∑ i, ∑ j ∈ Finset.univ.erase i, h p.1 (p.2 i) (p.2 j) := by
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact hh.comp (measurable_fst.prodMk ((hXi i).prodMk (hXi j)))
  have T2 : Measurable fun p : ℝ × EucConfig d N =>
      ∑ i, ∫ y, h p.1 (p.2 i) y ∂(HRS.Whole.withDensityReal (ρ p.1)) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    exact Measurable.comp (g := fun q : ℝ × Euc d => ∫ y, h q.1 q.2 y ∂(HRS.Whole.withDensityReal (ρ q.1)))
      (f := fun p : ℝ × EucConfig d N => (p.1, p.2 i)) hG1 (measurable_fst.prodMk (hXi i))
  have T3 : Measurable fun p : ℝ × EucConfig d N =>
      ∫ x, ∫ y, h p.1 x y ∂(HRS.Whole.withDensityReal (ρ p.1)) ∂(HRS.Whole.withDensityReal (ρ p.1)) :=
    Measurable.comp (g := fun t : ℝ => ∫ x, ∫ y, h t x y ∂(HRS.Whole.withDensityReal (ρ t)) ∂(HRS.Whole.withDensityReal (ρ t)))
      (f := fun p : ℝ × EucConfig d N => p.1) hG2 measurable_fst
  exact ((measurable_const.mul T1).sub (measurable_const.mul T2)).add (measurable_const.mul T3)

end HRS.MS.R2S11
