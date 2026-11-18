import Mathlib

/-!
Jointly measurable Nat-indexed coefficient fields from actual scalar L2
coordinates. Tonelli gives one almost-everywhere square-summability locus;
finite-single sections give strong measurability of the resulting ell2
field. No measurability of a proposed vector field is assumed.

This Mathlib-only module also gives the Fubini slice conclusion and an
actual continuous orthogonal projection making an almost-everywhere
zero mass exact at every parameter value.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.ProClosureS111

abbrev NatCoeffL2 := lp (fun _ : ℕ => ℝ) 2

theorem natCoeff_mem_iff {f : ℕ → ℝ} :
    Memℓp f 2 ↔ Summable (fun i => f i ^ 2) := by
  rw [memℓp_gen_iff (by norm_num)]
  simp [Real.norm_eq_abs, sq_abs]

theorem natCoeff_norm_sq (q : NatCoeffL2) :
    ‖q‖ ^ 2 = ∑' i, q i ^ 2 := by
  simpa [Real.norm_eq_abs, sq_abs] using
    lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℕ => ℝ) (by norm_num) q

theorem natCoeff_enorm_sq (q : NatCoeffL2) :
    ‖q‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖q‖ ^ 2) := by
  rw [← ofReal_norm_eq_enorm]
  exact (ENNReal.rpow_natCast _ 2).trans
    (ENNReal.ofReal_pow (norm_nonneg _) 2).symm

def natCoeffOf (f : ℕ → ℝ) : NatCoeffL2 :=
  if h : Memℓp f 2 then ⟨f, h⟩ else 0

theorem natCoeffOf_apply {f : ℕ → ℝ} (hf : Summable (fun i => f i ^ 2))
    (i : ℕ) : natCoeffOf f i = f i := by
  simp only [natCoeffOf, dif_pos (natCoeff_mem_iff.2 hf)]

variable {X : Type*} [MeasurableSpace X]

/-- Tonelli's exact square integral and one simultaneous square-summability
locus. This is the Nat specialization of the accepted I11 argument, kept
Mathlib-only to permit an independent small native consumer. -/
theorem scalar_square_tonelli (mu : Measure X)
    (f : ℕ → X → ℝ) (hf : ∀ i, MemLp (f i) 2 mu)
    (hS : Summable (fun i => ∫ x, f i x ^ 2 ∂mu)) :
    (∫⁻ x, ∑' i, ENNReal.ofReal (f i x ^ 2) ∂mu) =
      ENNReal.ofReal (∑' i, ∫ x, f i x ^ 2 ∂mu) ∧
    ∀ᵐ x ∂mu, Summable (fun i => f i x ^ 2) := by
  have hm : ∀ i, AEMeasurable (fun x => ENNReal.ofReal (f i x ^ 2)) mu :=
    fun i => ((hf i).aestronglyMeasurable.pow 2).aemeasurable.ennreal_ofReal
  have hlin : (∫⁻ x, ∑' i, ENNReal.ofReal (f i x ^ 2) ∂mu) =
      ENNReal.ofReal (∑' i, ∫ x, f i x ^ 2 ∂mu) := by
    rw [lintegral_tsum hm]
    have hi : ∀ i, (∫⁻ x, ENNReal.ofReal (f i x ^ 2) ∂mu) =
        ENNReal.ofReal (∫ x, f i x ^ 2 ∂mu) := fun i =>
      (ofReal_integral_eq_lintegral_ofReal (hf i).integrable_sq
        (ae_of_all _ fun _ => sq_nonneg _)).symm
    simp_rw [hi]
    exact (ENNReal.ofReal_tsum_of_nonneg
      (fun i => integral_nonneg fun _ => sq_nonneg _) hS).symm
  refine ⟨hlin, ?_⟩
  have hfinite : (∫⁻ x, ∑' i, ENNReal.ofReal (f i x ^ 2) ∂mu) < ⊤ := by
    rw [hlin]
    exact ENNReal.ofReal_lt_top
  have hmeas : AEMeasurable (fun x => ∑' i, ENNReal.ofReal (f i x ^ 2)) mu :=
    AEMeasurable.ennreal_tsum hm
  filter_upwards [ae_lt_top' hmeas hfinite.ne] with x hx
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hx.ne

theorem natCoeffOf_aestronglyMeasurable (mu : Measure X)
    (f : ℕ → X → ℝ) (hf : ∀ i, AEStronglyMeasurable (f i) mu)
    (hS : ∀ᵐ x ∂mu, Summable (fun i => f i x ^ 2)) :
    AEStronglyMeasurable (fun x => natCoeffOf (fun i => f i x)) mu := by
  let inc : ℕ → ℝ →L[ℝ] NatCoeffL2 := fun i =>
    lp.singleContinuousLinearMap (𝕜 := ℝ) (E := fun _ : ℕ => ℝ) 2 i
  refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ℕ))
    (f := fun S x => ∑ i ∈ S, inc i (f i x)) ?_ ?_
  · intro S
    exact Finset.aestronglyMeasurable_fun_sum S fun i _ =>
      (inc i).continuous.comp_aestronglyMeasurable (hf i)
  · filter_upwards [hS] with x hx
    have hm : Memℓp (fun i => f i x) 2 := natCoeff_mem_iff.2 hx
    have he : natCoeffOf (fun i => f i x) = ⟨fun i => f i x, hm⟩ := by
      simp only [natCoeffOf, dif_pos hm]
    rw [he]
    exact lp.hasSum_single (by norm_num) (⟨fun i => f i x, hm⟩ : NatCoeffL2)

section MeasurableCoeff

variable [MeasurableSpace NatCoeffL2] [BorelSpace NatCoeffL2]

/-- A genuine jointly measurable coefficient field, with every coordinate
on one common almost-everywhere locus and the exact integrated norm. The
measure need not be finite or normalized. -/
theorem exists_joint_coeffL2 (mu : Measure X)
    (f : ℕ → X → ℝ) (hf : ∀ i, MemLp (f i) 2 mu)
    (hS : Summable (fun i => ∫ x, f i x ^ 2 ∂mu)) :
    ∃ q : X → NatCoeffL2, Measurable q ∧ MemLp q 2 mu ∧
      (∀ᵐ x ∂mu, ∀ i, q x i = f i x) ∧
      (∫ x, ‖q x‖ ^ 2 ∂mu) = ∑' i, ∫ x, f i x ^ 2 ∂mu := by
  obtain ⟨hlin, hsum⟩ := scalar_square_tonelli mu f hf hS
  let q0 : X → NatCoeffL2 := fun x => natCoeffOf (fun i => f i x)
  have hq0 : AEStronglyMeasurable q0 mu :=
    natCoeffOf_aestronglyMeasurable mu f (fun i => (hf i).aestronglyMeasurable) hsum
  have hnorm : ∀ᵐ x ∂mu, ‖q0 x‖ₑ ^ (2 : ℝ) =
      ∑' i, ENNReal.ofReal (f i x ^ 2) := by
    filter_upwards [hsum] with x hx
    rw [natCoeff_enorm_sq, natCoeff_norm_sq]
    have he : (fun i => (q0 x i) ^ 2) = (fun i => f i x ^ 2) := by
      funext i
      rw [natCoeffOf_apply hx]
    rw [he]
    exact ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hx
  have hfinite : (∫⁻ x, ‖q0 x‖ₑ ^ (2 : ℝ) ∂mu) < ⊤ := by
    rw [lintegral_congr_ae hnorm, hlin]
    exact ENNReal.ofReal_lt_top
  have hqLp : MemLp q0 2 mu := by
    change eLpNorm q0 2 mu < ⊤
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hq0).2
    simpa only [ENNReal.toReal_ofNat] using hfinite
  have hnormInt : (∫ x, ‖q0 x‖ ^ 2 ∂mu) = ∑' i, ∫ x, f i x ^ 2 ∂mu := by
    have he : ENNReal.ofReal (∫ x, ‖q0 x‖ ^ 2 ∂mu) =
        ENNReal.ofReal (∑' i, ∫ x, f i x ^ 2 ∂mu) := by
      calc
        _ = ∫⁻ x, ENNReal.ofReal (‖q0 x‖ ^ 2) ∂mu :=
          ofReal_integral_eq_lintegral_ofReal
            ((memLp_two_iff_integrable_sq_norm hq0).1 hqLp)
            (ae_of_all _ fun _ => sq_nonneg _)
        _ = ∫⁻ x, ‖q0 x‖ₑ ^ (2 : ℝ) ∂mu := by simp_rw [natCoeff_enorm_sq]
        _ = _ := (lintegral_congr_ae hnorm).trans hlin
    have ht := congrArg ENNReal.toReal he
    simpa only [ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _),
      ENNReal.toReal_ofReal (tsum_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _)] using ht
  let q : X → NatCoeffL2 := hq0.mk q0
  have hqq : q =ᵐ[mu] q0 := hq0.ae_eq_mk.symm
  refine ⟨q, hq0.stronglyMeasurable_mk.measurable,
    (memLp_congr_ae hq0.ae_eq_mk).1 hqLp, ?_, ?_⟩
  · filter_upwards [hqq, hsum] with x hx hs i
    rw [hx]
    exact natCoeffOf_apply hs i
  · exact (integral_congr_ae (hqq.fun_comp (fun z : NatCoeffL2 => ‖z‖ ^ 2))).trans hnormInt

end MeasurableCoeff

/-- Product-almost-everywhere coordinate identities imply the exact
almost-everywhere-in-time, all-coordinate slice interface. -/
theorem joint_coeffL2_coordinates_slices
    {A Omega : Type*} [MeasurableSpace A] [MeasurableSpace Omega]
    (dt : Measure A) (P : Measure Omega) [SFinite P]
    {q : A × Omega → NatCoeffL2} {f : ℕ → A × Omega → ℝ}
    (h : ∀ᵐ p ∂dt.prod P, ∀ i, q p i = f i p) :
    ∀ᵐ t ∂dt, ∀ i, (fun w => q (t, w) i) =ᵐ[P] (fun w => f i (t, w)) := by
  filter_upwards [Measure.ae_ae_of_ae_prod h] with t ht i
  filter_upwards [ht] with w hw
  exact hw i

section MassProjection

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Orthogonal projection away from one specified mass vector. Division
by zero is harmless: when the mass vector is zero this is the identity. -/
def coeffMassProjection (c : V) : V →L[ℝ] V :=
  ContinuousLinearMap.id ℝ V -
    ((‖c‖ ^ 2)⁻¹ • innerSL ℝ c).smulRight c

theorem coeffMassProjection_apply (c z : V) :
    coeffMassProjection c z = z - (inner ℝ z c / ‖c‖ ^ 2) • c := by
  change z - ((‖c‖ ^ 2)⁻¹ * inner ℝ c z) • c =
    z - (inner ℝ z c / ‖c‖ ^ 2) • c
  rw [real_inner_comm c z]
  congr 2
  ring

theorem coeffMassProjection_inner (c z : V) :
    inner ℝ (coeffMassProjection c z) c = 0 := by
  rw [coeffMassProjection_apply, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  by_cases hc : c = 0
  · simp [hc]
  · have hn : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hc)
    rw [div_mul_cancel₀ _ hn, sub_self]

theorem coeffMassProjection_eq_self (c z : V) (hz : inner ℝ z c = 0) :
    coeffMassProjection c z = z := by
  simp only [coeffMassProjection_apply, hz, zero_div, zero_smul, sub_zero]

variable [MeasurableSpace V] [BorelSpace V]

/-- Make an almost-everywhere zero-mass coefficient field exactly zero
mass at every point, while preserving its entire almost-everywhere
vector value and hence all scalar coordinates and moments. -/
theorem exists_exact_zero_mass_field (mu : Measure X) (q : X → V)
    (hq : Measurable q) (hLp : MemLp q 2 mu) (c : V)
    (hmass : ∀ᵐ x ∂mu, inner ℝ (q x) c = 0) :
    ∃ q' : X → V, Measurable q' ∧ MemLp q' 2 mu ∧
      (∀ x, inner ℝ (q' x) c = 0) ∧ q' =ᵐ[mu] q := by
  let q' : X → V := fun x => coeffMassProjection c (q x)
  have he : q' =ᵐ[mu] q := by
    filter_upwards [hmass] with x hx
    exact coeffMassProjection_eq_self c (q x) hx
  exact ⟨q', (coeffMassProjection c).continuous.measurable.comp hq,
    (memLp_congr_ae he).2 hLp, fun x => coeffMassProjection_inner c (q x), he⟩

end MassProjection

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.exists_joint_coeffL2
#print axioms HRS.MS.ProClosureS111.joint_coeffL2_coordinates_slices
#print axioms HRS.MS.ProClosureS111.exists_exact_zero_mass_field
