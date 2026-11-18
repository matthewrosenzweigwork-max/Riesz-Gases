import HRS.MS.SA12BuildC20
import HRS.MS.Ker1
import HRS.MS.ToriCoefBAux1
import HRS.Kernel.GradBasic

/-!
# S.A.12 C17, toolkit: periodic cells, periodic integration by parts, evenness of the kernel

* centred-box and period-box integrals of a periodic function agree;
* a continuous periodic function (with a compact parameter) is bounded;
* `∫_{[0,L)^d} ∂_i u = 0` for a periodic `C^1` function, and the periodic integration by parts;
* every `IsPeriodicRieszKernel` is even.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

/-- The centred period cell and the period box have the same integral of a periodic function. -/
theorem sa12v_centered_eq (L : ℝ) (hL : 0 < L) {Φ : Euc d → ℝ}
    (hper : ∀ (x : Euc d) (k : Fin d → ℤ), Φ (x + L • latticePt k) = Φ x) :
    ∫ z in centeredBox d L, Φ z = ∫ z in periodBox d L, Φ z := by
  have h := sa12c20_cell_shift L hL hper (WithLp.toLp 2 fun _ : Fin d => -(L / 2))
  have hset : centeredBox d L =
      {z : Euc d | ∀ i, (WithLp.toLp 2 fun _ : Fin d => -(L / 2) : Euc d) i ≤ z i ∧
        z i < (WithLp.toLp 2 fun _ : Fin d => -(L / 2) : Euc d) i + L} := by
    ext z
    simp only [centeredBox]
    refine forall_congr' fun i => ?_
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> simp at * <;> linarith
  rw [hset]
  exact h

theorem sa12v_centered_meas (L : ℝ) : MeasurableSet (centeredBox d L) := by
  have hproj : ∀ i : Fin d, Measurable fun z : Euc d => z i := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable
  have : centeredBox d L = ⋂ i, ({z : Euc d | -(L / 2) ≤ z i} ∩ {z : Euc d | z i < L / 2}) := by
    ext z; simp [centeredBox]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_le measurable_const (hproj i)).inter (measurableSet_lt (hproj i) measurable_const)

/-- Every point is congruent mod `L ℤ^d` to a point of the closed cube `[0,L]^d`. -/
theorem sa12v_reduce (L : ℝ) (hL : 0 < L) (x : Euc d) :
    ∃ k : Fin d → ℤ, ∀ i, x i + L * (k i : ℝ) ∈ Icc (0 : ℝ) L := by
  refine ⟨fun i => -⌊x i / L⌋, fun i => ?_⟩
  have h1 := Int.floor_le (x i / L)
  have h2 := Int.lt_floor_add_one (x i / L)
  rw [le_div_iff₀ hL] at h1
  rw [div_lt_iff₀ hL] at h2
  push_cast
  constructor <;> nlinarith

/-- A function on `[a,b] × ℝ^d`, continuous and `L`-periodic in the second variable, is bounded. -/
theorem sa12v_bdd_param {E : Type*} [NormedAddCommGroup E] (a b L : ℝ) (hL : 0 < L)
    (f : ℝ × Euc d → E) (hc : ContinuousOn f (Icc a b ×ˢ univ))
    (hper : ∀ σ ∈ Icc a b, ∀ (x : Euc d) (k : Fin d → ℤ), f (σ, x + L • latticePt k) = f (σ, x)) :
    ∃ B : ℝ, ∀ σ ∈ Icc a b, ∀ x : Euc d, ‖f (σ, x)‖ ≤ B := by
  have hK : IsCompact (Icc a b ×ˢ {x : Euc d | ∀ i, x i ∈ Icc (0 : ℝ) L}) :=
    isCompact_Icc.prod (HRS.MS.ToriCoefB.tcb_compact_Icc 0 L)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hc.mono (prod_mono subset_rfl (subset_univ _)))
  refine ⟨B, fun σ hσ x => ?_⟩
  obtain ⟨k, hk⟩ := sa12v_reduce L hL x
  have hx : x + L • latticePt k ∈ {x : Euc d | ∀ i, x i ∈ Icc (0 : ℝ) L} := by
    intro i
    simpa [latticePt] using hk i
  rw [← hper σ hσ x k]
  exact hB (σ, x + L • latticePt k) ⟨hσ, hx⟩

theorem sa12v_bdd (L : ℝ) (hL : 0 < L) {E : Type*} [NormedAddCommGroup E] (f : Euc d → E)
    (hc : Continuous f)
    (hper : ∀ (x : Euc d) (k : Fin d → ℤ), f (x + L • latticePt k) = f x) :
    ∃ B : ℝ, ∀ x : Euc d, ‖f x‖ ≤ B := by
  obtain ⟨B, hB⟩ := sa12v_bdd_param 0 0 L hL (fun p => f p.2) (hc.comp continuous_snd).continuousOn
    (fun σ _ x k => hper x k)
  exact ⟨B, fun x => hB 0 ⟨le_rfl, le_rfl⟩ x⟩


theorem sa12v_box_finite (L : ℝ) : volume (periodBox d L) < ⊤ := by
  have hK : volume {x : Euc d | ∀ i, x i ∈ Icc (0 : ℝ) L} < ⊤ :=
    (HRS.MS.ToriCoefB.tcb_compact_Icc (d := d) 0 L).measure_lt_top
  refine lt_of_le_of_lt (measure_mono ?_) hK
  intro x hx i
  exact ⟨(hx i).1, (hx i).2.le⟩

instance sa12v_box_fin (L : ℝ) : IsFiniteMeasure (volume.restrict (periodBox d L)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact sa12v_box_finite L⟩

/-- Periodicity of the directional derivative of a periodic function. -/
theorem sa12v_fderiv_periodic (L : ℝ) {u : Euc d → ℝ}
    (hu : ∀ (x : Euc d) (k : Fin d → ℤ), u (x + L • latticePt k) = u x) (v : Euc d) :
    ∀ (y : Euc d) (k : Fin d → ℤ),
      fderiv ℝ u (y + L • latticePt k) v = fderiv ℝ u y v := by
  intro y k
  have : (fun y' => u (y' + L • latticePt (d := d) k)) = u := funext fun y' => hu y' k
  have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (L • latticePt (d := d) k) (x := y)
  rw [this] at h2
  rw [← h2]

/-- The integral over a period cell of the derivative of a periodic `C^1` function vanishes. -/
theorem sa12v_per_deriv_zero (L : ℝ) (hL : 0 < L) {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u)
    (hper : ∀ (x : Euc d) (k : Fin d → ℤ), u (x + L • latticePt k) = u x) (i : Fin d) :
    ∫ z in periodBox d L, fderiv ℝ u z (EuclideanSpace.single i (1 : ℝ)) = 0 := by
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
  set Φ : ℝ → ℝ := fun s => ∫ z in periodBox d L, u (z + s • e) with hΦ
  have hconst : ∀ s, Φ s = Φ 0 := by
    intro s
    have hset : (fun z : Euc d => z + s • e) ⁻¹'
        {y : Euc d | ∀ j, (s • e) j ≤ y j ∧ y j < (s • e) j + L} = periodBox d L := by
      ext z
      simp only [Set.mem_preimage, Set.mem_setOf_eq, periodBox, PiLp.add_apply]
      refine forall_congr' fun j => ?_
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    have h2 := (measurePreserving_add_right (volume : Measure (Euc d)) (s • e)).setIntegral_preimage_emb
      (measurableEmbedding_addRight (s • e)) u {y : Euc d | ∀ j, (s • e) j ≤ y j ∧ y j < (s • e) j + L}
    rw [hset] at h2
    have h3 := sa12c20_cell_shift L hL hper (s • e)
    simp only [hΦ, zero_smul, add_zero]
    rw [h2, h3]
  obtain ⟨B, hB⟩ := sa12v_bdd L hL (fun y => fderiv ℝ u y e)
    ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const)
    (sa12v_fderiv_periodic L hper e)
  obtain ⟨B0, hB0⟩ := sa12v_bdd L hL u hu.continuous hper
  have hcont : ∀ s : ℝ, Continuous fun z : Euc d => u (z + s • e) := fun s =>
    hu.continuous.comp (continuous_id.add continuous_const)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (periodBox d L)) (F := fun (s : ℝ) (z : Euc d) => u (z + s • e))
    (F' := fun (s : ℝ) (z : Euc d) => fderiv ℝ u (z + s • e) e) (x₀ := 0) (bound := fun _ => B) (s := univ) univ_mem
    (Filter.Eventually.of_forall fun s => (hcont s).aestronglyMeasurable)
    (by
      refine Integrable.mono' (integrable_const B0) (hcont 0).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ?_)
      simpa using hB0 (z + (0 : ℝ) • e))
    (((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
      (continuous_id.add continuous_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z s _ => hB _)
    (integrable_const _)
    (Filter.Eventually.of_forall fun z s _ => by
      have h0 : HasFDerivAt u (fderiv ℝ u (z + s • e)) (z + s • e) :=
        ((hu.differentiable one_ne_zero) (z + s • e)).hasFDerivAt
      have h1 : HasDerivAt (fun s : ℝ => z + s • e) e s := by
        simpa using ((hasDerivAt_id s).smul_const e).const_add z
      exact h0.comp_hasDerivAt s h1)
  have hΦc : Φ = fun _ => Φ 0 := funext hconst
  have hd' : HasDerivAt Φ (∫ z in periodBox d L, fderiv ℝ u (z + (0 : ℝ) • e) e) 0 := hd.2
  rw [hΦc] at hd'
  have := hd'.unique (hasDerivAt_const (0 : ℝ) (Φ 0))
  simpa using this


theorem sa12v_integrableOn_box (L : ℝ) {E : Type*} [NormedAddCommGroup E] {f : Euc d → E}
    (hf : Continuous f) : IntegrableOn f (periodBox d L) := by
  have hK := HRS.MS.ToriCoefB.tcb_compact_Icc (d := d) 0 L
  refine (hf.continuousOn.integrableOn_compact hK).mono_set ?_
  intro x hx i
  exact ⟨(hx i).1, (hx i).2.le⟩

/-- Periodic integration by parts over a period cell. -/
theorem sa12v_per_ibp (L : ℝ) (hL : 0 < L) {u w : Euc d → ℝ} (hu : ContDiff ℝ 1 u)
    (hw : ContDiff ℝ 1 w)
    (hup : ∀ (x : Euc d) (k : Fin d → ℤ), u (x + L • latticePt k) = u x)
    (hwp : ∀ (x : Euc d) (k : Fin d → ℤ), w (x + L • latticePt k) = w x) (i : Fin d) :
    ∫ z in periodBox d L, fderiv ℝ u z (EuclideanSpace.single i (1 : ℝ)) * w z =
      -∫ z in periodBox d L, u z * fderiv ℝ w z (EuclideanSpace.single i (1 : ℝ)) := by
  have hprod : ContDiff ℝ 1 (fun z => u z * w z) := hu.mul hw
  have h0 := sa12v_per_deriv_zero L hL hprod (fun x k => by simp only [hup, hwp]) i
  have hd : ∀ z, fderiv ℝ (fun z => u z * w z) z (EuclideanSpace.single i (1 : ℝ)) =
      fderiv ℝ u z (EuclideanSpace.single i (1 : ℝ)) * w z +
        u z * fderiv ℝ w z (EuclideanSpace.single i (1 : ℝ)) := by
    intro z
    have h2 := (hu.differentiable one_ne_zero z).hasFDerivAt.mul
      (hw.differentiable one_ne_zero z).hasFDerivAt
    have h3 : HasFDerivAt (fun z => u z * w z) (u z • fderiv ℝ w z + w z • fderiv ℝ u z) z := h2
    rw [h3.fderiv]
    simp [mul_comm, add_comm]
  simp_rw [hd] at h0
  have hc1 : Continuous fun z => fderiv ℝ u z (EuclideanSpace.single i (1 : ℝ)) * w z :=
    ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul hw.continuous
  have hc2 : Continuous fun z => u z * fderiv ℝ w z (EuclideanSpace.single i (1 : ℝ)) :=
    hu.continuous.mul ((hw.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  rw [integral_add (sa12v_integrableOn_box L hc1) (sa12v_integrableOn_box L hc2)] at h0
  linarith

/-- The periodic Riesz kernel is even off the lattice. -/
theorem sa12v_gamma_even (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L)
    {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ) (x : Euc d)
    (hx : ∀ z : Fin d → ℤ, x ≠ L • latticePt z) : γ (-x) = γ x := by
  have hx' : ∀ z : Fin d → ℤ, -x ≠ L • latticePt z := by
    intro z hz
    apply hx (-z)
    have : x = -(L • latticePt (d := d) z) := by rw [← hz]; simp
    rw [this]
    ext i; simp [latticePt]
  rw [HRS.MS.Ker1.ker1_eq_gam hd hs0 hsd hL hγ x hx, HRS.MS.Ker1.ker1_eq_gam hd hs0 hsd hL hγ (-x) hx']
  unfold HRS.MS.Ker1.ker1_gam HRS.MS.Ker1.ker1_g1
  rw [smul_neg, HRS.KernelGrad.mk_neg, periodicRiesz_neg]

/-- The periodic Riesz kernel is even almost everywhere. -/
theorem sa12v_gamma_even_ae (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L)
    {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ) :
    ∀ᵐ x ∂(volume : Measure (Euc d)), γ (-x) = γ x := by
  haveI : Nontrivial (Euc d) := ⟨⟨0, EuclideanSpace.single ⟨0, hd⟩ 1, by
    intro h
    have := congrArg (fun v : Euc d => v ⟨0, hd⟩) h
    simp at this⟩⟩
  have hcount : (Set.range fun z : Fin d → ℤ => L • latticePt (d := d) z).Countable :=
    Set.countable_range _
  have h0 : volume (Set.range fun z : Fin d → ℤ => L • latticePt (d := d) z) = 0 :=
    hcount.measure_zero _
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) h0
  by_contra hne
  apply hx
  exact sa12v_gamma_even hd hs0 hsd hL hγ x (fun z hz => hne ⟨z, hz.symm⟩)

end HRS.MH.AdjointRd.Phase2SA12Construction
