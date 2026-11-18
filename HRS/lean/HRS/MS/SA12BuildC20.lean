import HRS.MH.AdjointRdDefs

/-!
# S.A.12 C20: differentiation of the periodic convolution

`perConv L γ h x = ∫_{[0,L)^d} γ(x-y) h(y) dy`.  By periodicity of the integrand the period cell can be
translated, so `perConv L γ h x = ∫_{[0,L)^d} γ(-z) h(x+z) dz`; this form is differentiated under the integral
sign (only `h` is differentiated, never the singular kernel `γ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

/-- The lattice `L ℤ^d` as an additive subgroup of `ℝ^d`. -/
def sa12c20Lat (d : ℕ) (L : ℝ) : AddSubgroup (Euc d) :=
  AddMonoidHom.range
    ({ toFun := fun k : Fin d → ℤ => L • latticePt (d := d) k
       map_zero' := by ext i; simp [latticePt]
       map_add' := fun a b => by ext i; simp [latticePt, mul_add] } : (Fin d → ℤ) →+ Euc d)

theorem sa12c20_mem_lat {L : ℝ} {w : Euc d} :
    w ∈ sa12c20Lat d L ↔ ∃ k : Fin d → ℤ, L • latticePt (d := d) k = w := Iff.rfl

instance sa12c20_countable (L : ℝ) : Countable (sa12c20Lat d L) := by
  have : Function.Surjective (fun k : Fin d → ℤ =>
      (⟨L • latticePt (d := d) k, ⟨k, rfl⟩⟩ : sa12c20Lat d L)) := by
    rintro ⟨w, k, rfl⟩
    exact ⟨k, rfl⟩
  exact this.countable

/-- Every half-open cube of side `L` is a fundamental domain of `L ℤ^d`. -/
theorem sa12c20_fd (L : ℝ) (hL : 0 < L) (v : Euc d) :
    IsAddFundamentalDomain (sa12c20Lat d L) {z : Euc d | ∀ i, v i ≤ z i ∧ z i < v i + L} volume := by
  have hproj : ∀ i : Fin d, Measurable fun z : Euc d => z i := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable
  have hmeas : MeasurableSet {z : Euc d | ∀ i, v i ≤ z i ∧ z i < v i + L} := by
    have : {z : Euc d | ∀ i, v i ≤ z i ∧ z i < v i + L} =
        ⋂ i, ({z : Euc d | v i ≤ z i} ∩ {z : Euc d | z i < v i + L}) := by
      ext z; simp
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_le measurable_const (hproj i)).inter (measurableSet_lt (hproj i) measurable_const)
  refine IsAddFundamentalDomain.mk' hmeas.nullMeasurableSet fun x => ?_
  have key : ∀ i : Fin d, ∃ n : ℤ, v i ≤ x i + L * n ∧ x i + L * n < v i + L := by
    intro i
    refine ⟨⌈(v i - x i) / L⌉, ?_, ?_⟩
    · have := Int.le_ceil ((v i - x i) / L)
      rw [div_le_iff₀ hL] at this
      linarith
    · have := Int.ceil_lt_add_one ((v i - x i) / L)
      have h2 : (⌈(v i - x i) / L⌉ : ℝ) * L < ((v i - x i) / L + 1) * L :=
        mul_lt_mul_of_pos_right this hL
      have h3 : ((v i - x i) / L + 1) * L = v i - x i + L := by field_simp
      nlinarith
  choose n hn using key
  refine ⟨⟨L • latticePt (d := d) n, ⟨n, rfl⟩⟩, ?_, ?_⟩
  · intro i
    have := hn i
    show v i ≤ (L • latticePt (d := d) n + x) i ∧ (L • latticePt (d := d) n + x) i < v i + L
    simp only [PiLp.add_apply, PiLp.smul_apply, latticePt, smul_eq_mul]
    constructor <;> linarith [this.1, this.2]
  · rintro ⟨w, k, rfl⟩ hw
    have hk : ∀ i, v i ≤ L * (k i) + x i ∧ L * (k i) + x i < v i + L := by
      intro i
      have := hw i
      simpa [latticePt, add_comm] using this
    have hkn : k = n := by
      funext i
      have h1 := hk i
      have h2 := hn i
      have h3 : (k i : ℝ) < n i + 1 := by
        by_contra hcon
        push Not at hcon
        nlinarith [h1.1, h2.2, mul_le_mul_of_nonneg_left hcon hL.le]
      have h4 : (n i : ℝ) < k i + 1 := by
        by_contra hcon
        push Not at hcon
        nlinarith [h2.1, h1.2, mul_le_mul_of_nonneg_left hcon hL.le]
      have h5 : k i < n i + 1 := by exact_mod_cast h3
      have h6 : n i < k i + 1 := by exact_mod_cast h4
      omega
    subst hkn
    rfl

theorem sa12c20_box_meas (L : ℝ) : MeasurableSet (periodBox d L) := by
  have hproj : ∀ i : Fin d, Measurable fun z : Euc d => z i := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable
  have : periodBox d L = ⋂ i, ({z : Euc d | 0 ≤ z i} ∩ {z : Euc d | z i < L}) := by
    ext z; simp [periodBox]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_le measurable_const (hproj i)).inter (measurableSet_lt (hproj i) measurable_const)

/-- Translation invariance of cell integrals of `L ℤ^d`-periodic functions. -/
theorem sa12c20_cell_shift (L : ℝ) (hL : 0 < L) {Φ : Euc d → ℝ}
    (hper : ∀ (x : Euc d) (k : Fin d → ℤ), Φ (x + L • latticePt k) = Φ x) (v : Euc d) :
    ∫ z in {z : Euc d | ∀ i, v i ≤ z i ∧ z i < v i + L}, Φ z =
      ∫ z in periodBox d L, Φ z := by
  have h0 : periodBox d L = {z : Euc d | ∀ i, (0 : Euc d) i ≤ z i ∧ z i < (0 : Euc d) i + L} := by
    ext z; simp [periodBox]
  rw [h0]
  refine (sa12c20_fd L hL v).setIntegral_eq (sa12c20_fd L hL 0) ?_
  rintro ⟨w, k, rfl⟩ x
  show Φ (L • latticePt (d := d) k + x) = Φ x
  rw [add_comm]
  exact hper x k


/-- Unfolding of the periodic convolution with the translated cell. -/
theorem sa12c20_perConv_eq (L : ℝ) (hL : 0 < L) (γ h : Euc d → ℝ)
    (hγp : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x)
    (hhp : ∀ (x : Euc d) (k : Fin d → ℤ), h (x + L • latticePt k) = h x) (x : Euc d) :
    perConv L γ h x = ∫ z in periodBox d L, γ (-z) * h (x + z) := by
  set f : Euc d → ℝ := fun y => γ (x - y) * h y with hf
  have hper : ∀ (y : Euc d) (k : Fin d → ℤ), f (y + L • latticePt k) = f y := by
    intro y k
    simp only [hf]
    have e1 : x - (y + L • latticePt (d := d) k) = (x - y) + L • latticePt (d := d) (-k) := by
      ext i; simp [latticePt]; ring
    rw [e1, hγp, hhp]
  have h1 := sa12c20_cell_shift L hL hper x
  have h2 := (measurePreserving_add_right (volume : Measure (Euc d)) x).setIntegral_preimage_emb
    (measurableEmbedding_addRight x) f {y : Euc d | ∀ i, x i ≤ y i ∧ y i < x i + L}
  have hset : (fun z : Euc d => z + x) ⁻¹' {y : Euc d | ∀ i, x i ≤ y i ∧ y i < x i + L} =
      periodBox d L := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, periodBox, PiLp.add_apply]
    refine forall_congr' fun i => ?_
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  rw [hset] at h2
  unfold perConv
  show ∫ y in periodBox d L, f y = _
  rw [← h1, ← h2]
  refine setIntegral_congr_fun ?_ fun z _ => ?_
  · exact sa12c20_box_meas L
  · simp only [hf]
    have e : x - (z + x) = -z := by abel
    rw [e, add_comm z x]


theorem sa12c20_box_norm (L : ℝ) (z : Euc d) (hz : z ∈ periodBox d L) :
    ‖z‖ ≤ Real.sqrt (d * L ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖z i‖ ^ 2 ≤ ∑ _i : Fin d, L ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := hz i
        rw [Real.norm_eq_abs, abs_of_nonneg this.1]
        exact pow_le_pow_left₀ this.1 this.2.le 2
    _ = d * L ^ 2 := by simp

theorem sa12c20_integrableOn_neg {γ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume) (L : ℝ) :
    IntegrableOn (fun z => γ (-z)) (periodBox d L) volume := by
  set R : ℝ := Real.sqrt (d * L ^ 2) with hR
  have hsub : (fun w : Euc d => -w) ⁻¹' (periodBox d L) ⊆ Metric.closedBall (0 : Euc d) R := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    have := sa12c20_box_norm L (-w) hw
    rwa [norm_neg] at this
  have h1 : IntegrableOn γ ((fun w : Euc d => -w) ⁻¹' (periodBox d L)) volume :=
    (hγ.integrableOn_isCompact (isCompact_closedBall (0 : Euc d) R)).mono_set hsub
  have h2 := (Measure.measurePreserving_neg (volume : Measure (Euc d))).integrableOn_comp_preimage
    (MeasurableEquiv.neg (Euc d)).measurableEmbedding (f := γ)
    (s := (fun w : Euc d => -w) ⁻¹' (periodBox d L))
  have hpre : (fun w : Euc d => -w) ⁻¹' ((fun w : Euc d => -w) ⁻¹' (periodBox d L)) =
      periodBox d L := by
    ext z; simp
  rw [hpre] at h2
  exact h2.2 h1


/-- Differentiation under the integral sign for the translated-cell form. -/
theorem sa12c20_hasFDerivAt (L : ℝ) {γ h : Euc d → ℝ} (hγ : LocallyIntegrable γ volume)
    (hh : ContDiff ℝ 1 h) (x0 : Euc d) :
    HasFDerivAt (fun x => ∫ z in periodBox d L, γ (-z) * h (x + z))
      (∫ z in periodBox d L, γ (-z) • fderiv ℝ h (x0 + z)) x0 := by
  set μ : Measure (Euc d) := volume.restrict (periodBox d L) with hμ
  set R : ℝ := Real.sqrt (d * L ^ 2) with hR
  have hint : Integrable (fun z => γ (-z)) μ := sa12c20_integrableOn_neg hγ L
  have hK : IsCompact (Metric.closedBall (0 : Euc d) (‖x0‖ + 1 + R)) := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hh.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn hh.continuous.continuousOn
  have hmem : ∀ x ∈ Metric.ball x0 1, ∀ z ∈ periodBox d L,
      x + z ∈ Metric.closedBall (0 : Euc d) (‖x0‖ + 1 + R) := by
    intro x hx z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖x‖ ≤ ‖x0‖ + 1 := by
      have := norm_le_norm_add_norm_sub' x x0
      rw [Metric.mem_ball, dist_eq_norm] at hx
      linarith
    calc ‖x + z‖ ≤ ‖x‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖x0‖ + 1 + R := add_le_add h1 (sa12c20_box_norm L z hz)
  have hcont : ∀ x : Euc d, Continuous fun z : Euc d => h (x + z) := fun x =>
    hh.continuous.comp (continuous_const.add continuous_id)
  have hae : ∀ᵐ z ∂μ, z ∈ periodBox d L := ae_restrict_mem (sa12c20_box_meas L)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x z => γ (-z) * h (x + z)) (F' := fun x z => γ (-z) • fderiv ℝ h (x + z))
    (bound := fun z => ‖γ (-z)‖ * C) (Metric.ball_mem_nhds x0 one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x => hint.1.mul (hcont x).aestronglyMeasurable
  · refine Integrable.mono' (hint.norm.mul_const C0) (hint.1.mul (hcont x0).aestronglyMeasurable) ?_
    filter_upwards [hae] with z hz
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC0 _ (hmem x0 (Metric.mem_ball_self one_pos) z hz))
      (norm_nonneg _)
  · exact hint.1.smul ((hh.continuous_fderiv one_ne_zero).comp
      (continuous_const.add continuous_id)).aestronglyMeasurable
  · filter_upwards [hae] with z hz x hx
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC _ (hmem x hx z hz)) (norm_nonneg _)
  · exact hint.norm.mul_const C
  · refine Filter.Eventually.of_forall fun z x _ => ?_
    have h0 : HasFDerivAt h (fderiv ℝ h (x + z)) (x + z) :=
      ((hh.differentiable one_ne_zero) (x + z)).hasFDerivAt
    have h1 : HasFDerivAt (fun y => h (y + z)) (fderiv ℝ h (x + z)) x := by
      have := h0.comp x ((hasFDerivAt_id x).add_const z)
      exact this.congr_fderiv (ContinuousLinearMap.comp_id _)
    exact h1.const_mul (γ (-z))

theorem sa12c20_F'_integrable (L : ℝ) {γ h : Euc d → ℝ} (hγ : LocallyIntegrable γ volume)
    (hh : ContDiff ℝ 1 h) (x0 : Euc d) :
    Integrable (fun z => γ (-z) • fderiv ℝ h (x0 + z)) (volume.restrict (periodBox d L)) := by
  set R : ℝ := Real.sqrt (d * L ^ 2) with hR
  have hint : Integrable (fun z => γ (-z)) (volume.restrict (periodBox d L)) :=
    sa12c20_integrableOn_neg hγ L
  have hK : IsCompact (Metric.closedBall (0 : Euc d) (‖x0‖ + R)) := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hh.continuous_fderiv one_ne_zero).continuousOn
  have hae : ∀ᵐ z ∂(volume.restrict (periodBox d L)), z ∈ periodBox d L :=
    ae_restrict_mem (sa12c20_box_meas L)
  refine Integrable.mono' (hint.norm.mul_const C) (hint.1.smul ((hh.continuous_fderiv one_ne_zero).comp
      (continuous_const.add continuous_id)).aestronglyMeasurable) ?_
  filter_upwards [hae] with z hz
  rw [norm_smul]
  refine mul_le_mul_of_nonneg_left (hC _ ?_) (norm_nonneg _)
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_add_le _ _).trans (add_le_add le_rfl (sa12c20_box_norm L z hz))

-- BEGIN SA12.C20
theorem periodic_convolution_derivative (L : ℝ) (hL : 0 < L) (γ h : Euc d → ℝ) (hγ : LocallyIntegrable γ volume)
    (hγp : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x) (hh : ContDiff ℝ 1 h)
    (hhp : ∀ (x : Euc d) (k : Fin d → ℤ), h (x + L • latticePt k) = h x) (i : Fin d) (x : Euc d) :
    fderiv ℝ (perConv L γ h) x (EuclideanSpace.single i (1 : ℝ)) =
      perConv L γ (fun y => fderiv ℝ h y (EuclideanSpace.single i (1 : ℝ))) x := by
  have hfun : perConv L γ h = fun x => ∫ z in periodBox d L, γ (-z) * h (x + z) :=
    funext fun x => sa12c20_perConv_eq L hL γ h hγp hhp x
  have hper' : ∀ (y : Euc d) (k : Fin d → ℤ),
      fderiv ℝ h (y + L • latticePt k) (EuclideanSpace.single i (1 : ℝ)) =
        fderiv ℝ h y (EuclideanSpace.single i (1 : ℝ)) := by
    intro y k
    have : (fun y' => h (y' + L • latticePt (d := d) k)) = h := funext fun y' => hhp y' k
    have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := h) (L • latticePt (d := d) k) (x := y)
    rw [this] at h2
    rw [← h2]
  rw [sa12c20_perConv_eq L hL γ _ hγp hper' x, hfun,
    (sa12c20_hasFDerivAt L hγ hh x).fderiv]
  rw [ContinuousLinearMap.integral_apply (sa12c20_F'_integrable L hγ hh x) _]
  simp
-- END SA12.C20

end HRS.MH.AdjointRd.Phase2SA12Construction
