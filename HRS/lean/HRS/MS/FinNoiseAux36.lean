import HRS.Whole.Basic
import HRS.Torus.Basic

/-!
# S8.6 `finite_noise`: the chart density on the torus (Pro FR04) (S86b)

For an affine chart `F(u) = xc + A u` (`det A ≠ 0`), the half-open cube `Q₀ = (-1/2,1/2]^d` and
`U = F(Q₀)`, `ψ(x) = mk(A⁻¹(x - xc))`: if `lo ≤ ρ(F u)|det A| ≤ hi` on `Q₀`, then the chart image of the reference measure
`(ρ dx|_U) ∘ ψ⁻¹` is squeezed between `lo·vol` and `hi·vol` on the torus (`vol` = Haar probability measure).  The closed
and half-open cube differ by a null set, which is why `Q₀` suffices.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.FinNoise

open HRS

variable {d : ℕ}

/-- The half-open cube `(-1/2,1/2]^d`. -/
def s86_cube0 (d : ℕ) : Set (Euc d) := {u | ∀ i, u i ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2)}

theorem s86_cube0_meas : MeasurableSet (s86_cube0 d) := by
  have : s86_cube0 d = ⋂ i : Fin d, (fun u : Euc d => u i) ⁻¹' Set.Ioc (-1 / 2 : ℝ) (1 / 2) := by
    ext u; simp [s86_cube0]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_Ioc).preimage (EuclideanSpace.proj i).continuous.measurable

theorem s86_cube0_sub_closed : s86_cube0 d ⊆ {u : Euc d | ∀ i, |u i| ≤ 1 / 2} := by
  intro u hu i
  have := hu i
  rw [abs_le]
  constructor <;> linarith [this.1, this.2]

theorem s86_interior_sub_cube0 {u : Euc d} (hu : ∀ i, |u i| < 1 / 2) : u ∈ s86_cube0 d := by
  intro i
  have := abs_lt.mp (hu i)
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

theorem s86_cube0_pushforward {E : Set (Torus d)} (hE : MeasurableSet E) :
    (volume : Measure (Euc d)) (s86_cube0 d ∩ Torus.mk ⁻¹' E) = (volume : Measure (Torus d)) E := by
  classical
  have h1 := UnitAddTorus.lintegral_preimage (d := Fin d) (E.indicator (fun _ => (1 : ℝ≥0∞)))
    (fun _ => (-1 / 2 : ℝ))
  rw [lintegral_indicator_const hE, one_mul] at h1
  have h1' : (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) E = ∫⁻ (x : Fin d → ℝ) in
      {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)},
      E.indicator (fun _ => (1 : ℝ≥0∞)) (fun i => (x i : UnitAddCircle)) := h1
  rw [Torus.volume_eq_pi_haar]
  refine Eq.trans ?_ h1'.symm
  have hmp := PiLp.volume_preserving_ofLp (Fin d)
  have hemb : MeasurableEmbedding (@WithLp.ofLp 2 (Fin d → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
  have h2 := hmp.setLIntegral_comp_preimage_emb hemb
    (fun y : Fin d → ℝ => E.indicator (fun _ => (1 : ℝ≥0∞)) (fun i => (y i : UnitAddCircle)))
    {y : Fin d → ℝ | ∀ i, y i ∈ Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)}
  have hset : (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' {y : Fin d → ℝ | ∀ i, y i ∈ Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)}
      = s86_cube0 d := by
    ext u
    simp only [s86_cube0, mem_preimage, mem_setOf_eq]
    norm_num
  rw [hset] at h2
  rw [← h2]
  have h3 : ∀ u : Euc d, E.indicator (fun _ => (1 : ℝ≥0∞)) (fun i => ((u.ofLp i : ℝ) : UnitAddCircle)) =
      (Torus.mk ⁻¹' E).indicator (fun _ => (1 : ℝ≥0∞)) u := by
    intro u
    by_cases h : Torus.mk u ∈ E
    · rw [Set.indicator_of_mem (show (fun i => ((u.ofLp i : ℝ) : UnitAddCircle)) ∈ E from h),
        Set.indicator_of_mem (show u ∈ Torus.mk ⁻¹' E from h)]
    · rw [Set.indicator_of_notMem (show (fun i => ((u.ofLp i : ℝ) : UnitAddCircle)) ∉ E from h),
        Set.indicator_of_notMem (show u ∉ Torus.mk ⁻¹' E from h)]
  simp_rw [h3]
  rw [lintegral_indicator_const (Torus.continuous_mk.measurable hE), one_mul,
    Measure.restrict_apply (Torus.continuous_mk.measurable hE)]
  rw [Set.inter_comm]

theorem s86_chart_density (ρ : Euc d → ℝ) (_hρ : Measurable ρ) (xc : Euc d)
    (A : Euc d →L[ℝ] Euc d) (hdet : LinearMap.det (A : Euc d →ₗ[ℝ] Euc d) ≠ 0) (lo hi : ℝ)
    (hl : ∀ u ∈ s86_cube0 d, lo ≤ ρ (xc + A u) * |LinearMap.det (A : Euc d →ₗ[ℝ] Euc d)|)
    (hh : ∀ u ∈ s86_cube0 d, ρ (xc + A u) * |LinearMap.det (A : Euc d →ₗ[ℝ] Euc d)| ≤ hi) :
    ∃ (U : Set (Euc d)) (ψ : Euc d → Torus d), MeasurableSet U ∧ Measurable ψ ∧
      U = (fun u => xc + A u) '' s86_cube0 d ∧ (∀ u, ψ (xc + A u) = Torus.mk u) ∧
      ENNReal.ofReal lo • (volume : Measure (Torus d)) ≤
        ((HRS.Whole.withDensityReal ρ).restrict U).map ψ ∧
      ((HRS.Whole.withDensityReal ρ).restrict U).map ψ ≤
        ENNReal.ofReal hi • (volume : Measure (Torus d)) := by
  classical
  set e : Euc d ≃L[ℝ] Euc d := A.toContinuousLinearEquivOfDetNeZero hdet with he
  have heA : ∀ u, e u = A u := fun u => by
    have := ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero A hdet
    exact congrArg (fun f : Euc d →L[ℝ] Euc d => f u) this
  set F : Euc d → Euc d := fun u => xc + A u with hF
  have hFinj : Function.Injective F := fun u v h => by
    have h2 := add_left_cancel h
    rw [← heA, ← heA] at h2
    exact e.injective h2
  set ψ : Euc d → Torus d := fun x => Torus.mk (e.symm (x - xc)) with hψ
  have hψm : Measurable ψ :=
    Torus.continuous_mk.measurable.comp (e.symm.continuous.measurable.comp
      (measurable_id.sub measurable_const))
  have hψF : ∀ u, ψ (F u) = Torus.mk u := by
    intro u
    simp only [hψ, hF, add_sub_cancel_left]
    rw [← heA u, e.symm_apply_apply]
  set U : Set (Euc d) := F '' s86_cube0 d with hU
  have hUeq : U = (fun x => e.symm (x - xc)) ⁻¹' s86_cube0 d := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      show e.symm (F u - xc) ∈ s86_cube0 d
      simp only [hF, add_sub_cancel_left]
      rwa [← heA u, e.symm_apply_apply]
    · intro hx
      refine ⟨e.symm (x - xc), hx, ?_⟩
      simp only [hF]
      rw [← heA, e.apply_symm_apply]
      abel
  have hUm : MeasurableSet U := by
    rw [hUeq]
    exact s86_cube0_meas.preimage (e.symm.continuous.measurable.comp (measurable_id.sub measurable_const))
  -- the key computation
  have hkey : ∀ E : Set (Torus d), MeasurableSet E →
      (((HRS.Whole.withDensityReal ρ).restrict U).map ψ) E =
        ∫⁻ u in s86_cube0 d ∩ Torus.mk ⁻¹' E,
          ENNReal.ofReal (ρ (xc + A u) * |LinearMap.det (A : Euc d →ₗ[ℝ] Euc d)|) := by
    intro E hE
    rw [Measure.map_apply hψm hE, Measure.restrict_apply (hψm hE)]
    have hT : MeasurableSet (s86_cube0 d ∩ Torus.mk ⁻¹' E) :=
      s86_cube0_meas.inter (Torus.continuous_mk.measurable hE)
    have hS : ψ ⁻¹' E ∩ U = F '' (s86_cube0 d ∩ Torus.mk ⁻¹' E) := by
      ext x
      constructor
      · rintro ⟨hxE, ⟨u, hu, rfl⟩⟩
        refine ⟨u, ⟨hu, ?_⟩, rfl⟩
        have : ψ (F u) ∈ E := hxE
        rwa [hψF] at this
      · rintro ⟨u, ⟨hu, huE⟩, rfl⟩
        refine ⟨?_, ⟨u, hu, rfl⟩⟩
        show ψ (F u) ∈ E
        rwa [hψF]
    have hSm : MeasurableSet (ψ ⁻¹' E ∩ U) := (hψm hE).inter hUm
    unfold HRS.Whole.withDensityReal
    rw [withDensity_apply _ hSm, hS]
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hT
      (f' := fun _ => A) (fun u _ => (A.hasFDerivAt.const_add xc).hasFDerivWithinAt)
      (hFinj.injOn)]
    refine lintegral_congr fun u => ?_
    rw [← ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
  refine ⟨U, ψ, hUm, hψm, rfl, hψF, ?_, ?_⟩
  · refine Measure.le_iff.2 fun E hE => ?_
    rw [hkey E hE, Measure.smul_apply, smul_eq_mul, ← s86_cube0_pushforward hE]
    have hT : MeasurableSet (s86_cube0 d ∩ Torus.mk ⁻¹' E) :=
      s86_cube0_meas.inter (Torus.continuous_mk.measurable hE)
    rw [← setLIntegral_const]
    refine setLIntegral_mono' hT fun u hu => ?_
    exact ENNReal.ofReal_le_ofReal (hl u hu.1)
  · refine Measure.le_iff.2 fun E hE => ?_
    rw [hkey E hE, Measure.smul_apply, smul_eq_mul, ← s86_cube0_pushforward hE]
    have hT : MeasurableSet (s86_cube0 d ∩ Torus.mk ⁻¹' E) :=
      s86_cube0_meas.inter (Torus.continuous_mk.measurable hE)
    rw [← setLIntegral_const]
    refine setLIntegral_mono' hT fun u hu => ?_
    exact ENNReal.ofReal_le_ofReal (hh u hu.1)

end HRS.MS.FinNoise
