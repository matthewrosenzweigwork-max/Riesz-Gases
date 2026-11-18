import HRS.MC.CepH2Mom3
import HRS.Appendix.B15BAux1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# CEPH2, compactification of the cylinder and lower semicontinuity of `klDiv`

`π z = (z_0 mod 1, (z_k - z_0)/(1 + |z_k - z_0|))_k` maps the cylinder `Ch N / ℤ d` injectively into the compact
metric space `UnitAddCircle × (Fin N → [-1,1])`, with a measurable left inverse on the cell.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- The compact target. -/
abbrev H2Alpha (N : ℕ) := UnitAddCircle × (Fin N → Icc (-1 : ℝ) 1)

/-- Squashing `ℝ → [-1,1]`. -/
def h2_sq (x : ℝ) : Icc (-1 : ℝ) 1 :=
  ⟨x / (1 + |x|), by
    have h : 0 < 1 + |x| := by positivity
    have h1 : |x / (1 + |x|)| ≤ 1 := by
      rw [abs_div, abs_of_pos h, div_le_one h]; linarith
    exact abs_le.1 h1⟩

theorem h2_continuous_sq : Continuous h2_sq := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_id.div (continuous_const.add continuous_abs) fun x => by positivity

/-- Inverse of the squashing on `(-1,1)`. -/
def h2_isq (y : Icc (-1 : ℝ) 1) : ℝ := (y : ℝ) / (1 - |(y : ℝ)|)

theorem h2_isq_sq (x : ℝ) : h2_isq (h2_sq x) = x := by
  unfold h2_isq h2_sq
  simp only
  have h : 0 < 1 + |x| := by positivity
  have h2 : 1 - |x / (1 + |x|)| = 1 / (1 + |x|) := by
    rw [abs_div, abs_of_pos h]; field_simp; ring
  rw [h2]
  field_simp

/-- The compactification map. -/
def h2_pi (z : Ch N) : H2Alpha N := (((z 0 : ℝ) : UnitAddCircle), fun k => h2_sq (z k - z 0))

theorem h2_continuous_pi : Continuous (h2_pi : Ch N → H2Alpha N) := by
  have h0 : Continuous fun z : Ch N => z 0 := (EuclideanSpace.proj (0 : Fin N)).continuous
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_quotient_mk').comp h0
  · refine continuous_pi fun k => h2_continuous_sq.comp ?_
    exact ((EuclideanSpace.proj k).continuous).sub h0

theorem h2_pi_periodic (z : Ch N) : h2_pi (z + cep_diag N) = h2_pi z := by
  unfold h2_pi
  refine Prod.ext ?_ (funext fun k => ?_)
  · show (((z + cep_diag N) 0 : ℝ) : UnitAddCircle) = ((z 0 : ℝ) : UnitAddCircle)
    simp only [PiLp.add_apply, cep_diag_apply]
    exact AddCircle.coe_add_period 1 (z 0)
  · simp only [PiLp.add_apply, cep_diag_apply]
    congr 1
    ring

/-- Left inverse of `h2_pi` on the cell. -/
def h2_pinv (a : H2Alpha N) : Ch N :=
  WithLp.toLp 2 fun k => ((AddCircle.equivIco (1 : ℝ) 0 a.1 : Ico (0 : ℝ) (0 + 1)) : ℝ) + h2_isq (a.2 k)

theorem h2_measurable_pinv : Measurable (h2_pinv : H2Alpha N → Ch N) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).measurable.comp ?_
  refine measurable_pi_iff.2 fun k => ?_
  have h1 : Measurable fun a : H2Alpha N => ((AddCircle.equivIco (1 : ℝ) 0 a.1 : Ico (0 : ℝ) (0 + 1)) : ℝ) :=
    measurable_subtype_coe.comp ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp measurable_fst)
  have h2 : Measurable fun a : H2Alpha N => h2_isq (a.2 k) := by
    unfold h2_isq
    have hy : Measurable fun a : H2Alpha N => ((a.2 k : Icc (-1 : ℝ) 1) : ℝ) :=
      measurable_subtype_coe.comp ((measurable_pi_apply k).comp measurable_snd)
    exact hy.div (measurable_const.sub hy.abs)
  exact h1.add h2

theorem h2_pinv_pi {z : Ch N} (hz : z ∈ cep_cell N) : h2_pinv (h2_pi z) = z := by
  ext k
  simp only [h2_pinv, h2_pi]
  have : (AddCircle.equivIco (1 : ℝ) 0 ((z 0 : ℝ) : UnitAddCircle) : Ico (0 : ℝ) (0 + 1)) = ⟨z 0, by
      have := hz; simp only [zero_add]; exact ⟨hz.1, hz.2⟩⟩ :=
    AddCircle.equivIco_coe_eq _
  rw [this]
  simp only [h2_isq_sq]
  ring


theorem h2_ae_cell {μ : Measure (Ch N)} (hμ : μ (cep_cell N)ᶜ = 0) : ∀ᵐ z ∂μ, z ∈ cep_cell N := by
  have := (measure_eq_zero_iff_ae_notMem.1 hμ)
  filter_upwards [this] with z hz
  simpa using hz

theorem h2_map_pinv_pi {μ : Measure (Ch N)} (hμ : μ (cep_cell N)ᶜ = 0) :
    (μ.map h2_pi).map h2_pinv = μ := by
  rw [Measure.map_map h2_measurable_pinv h2_continuous_pi.measurable]
  have : μ.map (h2_pinv ∘ h2_pi) = μ.map id := by
    refine Measure.map_congr ?_
    filter_upwards [h2_ae_cell hμ] with z hz
    exact h2_pinv_pi hz
  rw [this, Measure.map_id]

/-- Pushing forward by `h2_pi` does not change `klDiv` for measures carried by the cell. -/
theorem h2_klDiv_map_pi {μ ν : Measure (Ch N)} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : μ (cep_cell N)ᶜ = 0) (hν : ν (cep_cell N)ᶜ = 0) :
    klDiv μ ν = klDiv (μ.map h2_pi) (ν.map h2_pi) := by
  refine le_antisymm ?_ (klDiv_map_le μ ν h2_continuous_pi.measurable)
  have h := klDiv_map_le (μ.map h2_pi) (ν.map h2_pi) h2_measurable_pinv
  rwa [h2_map_pinv_pi hμ, h2_map_pinv_pi hν] at h

/-- Lower semicontinuity of `klDiv` along sequences of measures on the cell converging against periodic
bounded continuous functions, with a fixed reference. -/
theorem h2_klDiv_liminf_cell {μ ν : Measure (Ch N)} {μn : ℕ → Measure (Ch N)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [∀ n, IsProbabilityMeasure (μn n)]
    (hμ : μ (cep_cell N)ᶜ = 0) (hν : ν (cep_cell N)ᶜ = 0) (hμn : ∀ n, μn n (cep_cell N)ᶜ = 0)
    (hconv : ∀ ψ : Ch N → ℝ, Continuous ψ → (∀ z, ψ (z + cep_diag N) = ψ z) → (∃ C, ∀ z, |ψ z| ≤ C) →
      Tendsto (fun n => ∫ z, ψ z ∂(μn n)) atTop (𝓝 (∫ z, ψ z ∂μ))) :
    klDiv μ ν ≤ liminf (fun n => klDiv (μn n) ν) atTop := by
  haveI : IsProbabilityMeasure (μ.map h2_pi) := (Measure.isProbabilityMeasure_map_iff h2_continuous_pi.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure (ν.map h2_pi) := (Measure.isProbabilityMeasure_map_iff h2_continuous_pi.aemeasurable).2 inferInstance
  haveI : ∀ n, IsProbabilityMeasure ((μn n).map h2_pi) := fun n =>
    (Measure.isProbabilityMeasure_map_iff h2_continuous_pi.aemeasurable).2 inferInstance
  have hP : ∀ φ : H2Alpha N → ℝ, Continuous φ →
      Tendsto (fun n => ∫ x, φ x ∂((μn n).map h2_pi)) atTop (𝓝 (∫ x, φ x ∂(μ.map h2_pi))) := by
    intro φ hφ
    have hc : Continuous (φ ∘ h2_pi) := hφ.comp h2_continuous_pi
    have hb : ∃ C, ∀ z, |(φ ∘ h2_pi) z| ≤ C := by
      obtain ⟨C, hC⟩ := (isCompact_univ (X := H2Alpha N)).exists_bound_of_continuousOn hφ.continuousOn
      exact ⟨C, fun z => by simpa using hC (h2_pi z) (mem_univ _)⟩
    have := hconv (φ ∘ h2_pi) hc (fun z => by simp only [Function.comp, h2_pi_periodic]) hb
    have e : ∀ m : Measure (Ch N), ∫ x, φ x ∂(m.map h2_pi) = ∫ z, (φ ∘ h2_pi) z ∂m := fun m =>
      integral_map h2_continuous_pi.aemeasurable hφ.aestronglyMeasurable
    simp only [e]
    exact this
  have hQ : ∀ φ : H2Alpha N → ℝ, Continuous φ →
      Tendsto (fun _ : ℕ => ∫ x, φ x ∂(ν.map h2_pi)) atTop (𝓝 (∫ x, φ x ∂(ν.map h2_pi))) :=
    fun φ _ => tendsto_const_nhds
  have h1 := b15b_klDiv_liminf_le (Qn := fun _ : ℕ => ν.map h2_pi) hP hQ
  rw [h2_klDiv_map_pi hμ hν]
  refine h1.trans (liminf_le_liminf (Eventually.of_forall fun n => ?_))
  exact klDiv_map_le (μn n) ν h2_continuous_pi.measurable

end HRS.MC.CepH2
