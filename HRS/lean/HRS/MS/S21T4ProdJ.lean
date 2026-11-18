import HRS.MS.S21T4ProdI

/-! S13: a.e. linearity of the singular pair statistic across L² kernels. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ]

/-- For square-integrable kernels, pair energy is additive on particle configurations
outside a set of product probability zero. It need not be pointwise additive at
exceptional configurations because the underlying Bochner integrals have junk values. -/
theorem s21t4_pairEnergy_sub_ae {N : ℕ} (h h' : Euc d → Euc d → ℝ)
    (hm : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hm' : MemLp (fun z : Euc d × Euc d => h' z.1 z.2) 2 (μ.prod μ)) :
    (fun X : EucConfig d N => pairEnergy (fun x y => h x y - h' x y) X μ)
      =ᵐ[Measure.pi fun _ : Fin N => μ]
    (fun X => pairEnergy h X μ - pairEnergy h' X μ) := by
  let ν : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ
  have hslice : ∀ᵐ x ∂μ, Integrable (fun y => h x y) μ ∧
      Integrable (fun y => h' x y) μ := by
    filter_upwards [s21h2_slice_memLp μ hm, s21h2_slice_memLp μ hm'] with x h1 h2
    exact ⟨h1.integrable one_le_two, h2.integrable one_le_two⟩
  have hmL : MemLp (fun x => ∫ y, h x y ∂μ) 2 μ := s21h2_m_memLp μ hm
  have hmL' : MemLp (fun x => ∫ y, h' x y ∂μ) 2 μ := s21h2_m_memLp μ hm'
  have hc : ∫ x, ∫ y, (h x y - h' x y) ∂μ ∂μ =
      (∫ x, ∫ y, h x y ∂μ ∂μ) -
        ∫ x, ∫ y, h' x y ∂μ ∂μ := by
    rw [← integral_sub (hmL.integrable one_le_two) (hmL'.integrable one_le_two)]
    refine integral_congr_ae ?_
    filter_upwards [hslice] with x hx
    exact integral_sub hx.1 hx.2
  have hae : ∀ᵐ X ∂ν, ∀ i : Fin N,
      Integrable (fun y => h (X i) y) μ ∧ Integrable (fun y => h' (X i) y) μ :=
    ae_all_iff.2 fun i =>
      (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae hslice
  filter_upwards [hae] with X hX
  unfold pairEnergy
  have e1 : ∀ i : Fin N,
      ∫ y, (h (X i) y - h' (X i) y) ∂μ =
        (∫ y, h (X i) y ∂μ) - ∫ y, h' (X i) y ∂μ :=
    fun i => integral_sub (hX i).1 (hX i).2
  simp only [e1, hc, Finset.sum_sub_distrib, mul_sub]
  ring

end HRS.MS.R26T3
