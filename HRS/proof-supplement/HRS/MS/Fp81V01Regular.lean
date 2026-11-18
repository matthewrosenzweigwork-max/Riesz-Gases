import HRS.MS.S111K2B04g

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.Fp81.V01

/-- An integrable nonnegative bound on increments gives continuity and finite variation. -/
theorem fp81v01_regular_of_majorant
    {G : Type*} [NormedAddCommGroup G]
    (g : ℝ → G) (H : ℝ) (hH : 0 ≤ H)
    (m : ℝ → ℝ) (hm : IntegrableOn m (Icc 0 H))
    (hm0 : ∀ t ∈ Icc 0 H, 0 ≤ m t)
    (hinc : ∀ v w, 0 ≤ v → v ≤ w → w ≤ H →
      ‖g w - g v‖ ≤ ∫ t in Icc v w, m t) :
    ContinuousOn g (Icc 0 H) ∧
      eVariationOn g (Icc 0 H) ≤ ENNReal.ofReal (∫ t in Icc 0 H, m t) := by
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (m t)
  have hnonneg : ∀ᵐ t ∂(volume.restrict (Icc 0 H)), 0 ≤ m t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hm0 t ht
  have hfin : ∫⁻ t in Icc 0 H, f t ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hm hnonneg]
    exact ENNReal.ofReal_ne_top
  have hdiff : ∀ x y, x ∈ Icc 0 H → y ∈ Icc 0 H → x ≤ y →
      edist (g y) (g x) ≤ ∫⁻ t in Ioc x y, f t := by
    intro x y hx hy hxy
    have hsub : Ioc x y ⊆ Icc 0 H := fun t ht =>
      ⟨hx.1.trans ht.1.le, ht.2.trans hy.2⟩
    have hmIoc : IntegrableOn m (Ioc x y) := hm.mono_set hsub
    have hnonnegIoc : ∀ᵐ t ∂(volume.restrict (Ioc x y)), 0 ≤ m t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hm0 t (hsub ht)
    have hlin : ∫⁻ t in Ioc x y, f t =
        ENNReal.ofReal (∫ t in Icc x y, m t) := by
      calc ∫⁻ t in Ioc x y, f t
          = ENNReal.ofReal (∫ t in Ioc x y, m t) :=
              (ofReal_integral_eq_lintegral_ofReal hmIoc hnonnegIoc).symm
        _ = ENNReal.ofReal (∫ t in Icc x y, m t) := by
              rw [← integral_Icc_eq_integral_Ioc]
    calc edist (g y) (g x)
        = ENNReal.ofReal ‖g y - g x‖ := by
            rw [edist_eq_enorm_sub, ← ofReal_norm]
      _ ≤ ENNReal.ofReal (∫ t in Icc x y, m t) :=
            ENNReal.ofReal_le_ofReal (hinc x y hx.1 hxy hy.2)
      _ = ∫⁻ t in Ioc x y, f t := hlin.symm
  refine ⟨?_, ?_⟩
  · intro x₀ hx₀
    rw [ContinuousWithinAt, tendsto_iff_edist_tendsto_0]
    set μ : Measure ℝ := volume.restrict (Icc 0 H) with hμ
    have h1 : Tendsto (fun x : ℝ => ENNReal.ofReal |x - x₀|) (𝓝[Icc 0 H] x₀) (𝓝 0) := by
      have hc : Continuous fun x : ℝ => |x - x₀| := by fun_prop
      have h2 := (hc.tendsto x₀).mono_left (nhdsWithin_le_nhds (s := Icc 0 H))
      have h3 := ENNReal.tendsto_ofReal h2
      simpa using h3
    have hmeas : Tendsto (μ ∘ fun x : ℝ => Ioc (min x x₀) (max x x₀))
        (𝓝[Icc 0 H] x₀) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
        (fun _ => bot_le) (fun x => ?_)
      simp only [Function.comp]
      refine ((Measure.restrict_le_self : μ ≤ volume) _).trans (le_of_eq ?_)
      rw [Real.volume_Ioc]
      congr 1
      rcases le_total x x₀ with h | h
      · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]
    have hs := tendsto_setLIntegral_zero (μ := μ) (f := f) hfin hmeas
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hsub : Ioc (min x x₀) (max x x₀) ⊆ Icc 0 H := fun t ht =>
      ⟨le_trans (le_min hx.1 hx₀.1) ht.1.le, ht.2.trans (max_le hx.2 hx₀.2)⟩
    rw [hμ, Measure.restrict_restrict measurableSet_Ioc, Set.inter_eq_left.2 hsub]
    rcases le_total x x₀ with h | h
    · rw [edist_comm, min_eq_left h, max_eq_right h]
      exact hdiff x x₀ hx hx₀ h
    · rw [min_eq_right h, max_eq_left h]
      exact hdiff x₀ x hx₀ hx h
  · unfold eVariationOn
    refine iSup_le fun p => ?_
    obtain ⟨n, v, hv, hmem⟩ := p
    calc ∑ i ∈ Finset.range n, edist (g (v (i + 1))) (g (v i))
        ≤ ∑ i ∈ Finset.range n, ∫⁻ t in Ioc (v i) (v (i + 1)), f t :=
          Finset.sum_le_sum fun i _ => hdiff (v i) (v (i + 1)) (hmem i) (hmem (i + 1))
            (hv (Nat.le_succ i))
      _ = ∫⁻ t in Ioc (v 0) (v n), f t := HRS.MS.S111K2.s111k2_sum_Ioc f v hv n
      _ ≤ ∫⁻ t in Icc 0 H, f t :=
        lintegral_mono_set (fun t ht => ⟨(hmem 0).1.trans ht.1.le, ht.2.trans (hmem n).2⟩)
      _ = ENNReal.ofReal (∫ t in Icc 0 H, m t) :=
        (ofReal_integral_eq_lintegral_ofReal hm hnonneg).symm

/-- The regularity result with zero initial value also controls every point by the partial integral. -/
theorem fp81v01_regular_of_majorant_zero
    {G : Type*} [NormedAddCommGroup G]
    (g : ℝ → G) (H : ℝ) (hH : 0 ≤ H)
    (m : ℝ → ℝ) (hm : IntegrableOn m (Icc 0 H))
    (hm0 : ∀ t ∈ Icc 0 H, 0 ≤ m t)
    (hinc : ∀ v w, 0 ≤ v → v ≤ w → w ≤ H →
      ‖g w - g v‖ ≤ ∫ t in Icc v w, m t)
    (hg0 : g 0 = 0) :
    ContinuousOn g (Icc 0 H) ∧
      eVariationOn g (Icc 0 H) ≤ ENNReal.ofReal (∫ t in Icc 0 H, m t) ∧
      ∀ v ∈ Icc 0 H, ‖g v‖ ≤ ∫ t in Icc 0 v, m t := by
  obtain ⟨hcont, hvar⟩ := fp81v01_regular_of_majorant g H hH m hm hm0 hinc
  refine ⟨hcont, hvar, ?_⟩
  intro v hv
  have hv0 : 0 ≤ v := hv.1
  have hmV : IntegrableOn m (Icc 0 v) := hm.mono_set (Icc_subset_Icc le_rfl hv.2)
  have hmV0 : ∀ t ∈ Icc 0 v, 0 ≤ m t := fun t ht => hm0 t ⟨ht.1, ht.2.trans hv.2⟩
  have hlocal := fp81v01_regular_of_majorant g v hv0 m hmV hmV0
    (fun x y hx hxy hy => hinc x y hx hxy (hy.trans hv.2))
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) v := ⟨le_rfl, hv0⟩
  have hvLocal : v ∈ Icc (0 : ℝ) v := ⟨hv0, le_rfl⟩
  have hdist := (eVariationOn.edist_le g hvLocal hzero).trans hlocal.2
  rw [hg0, edist_zero_right, ← ofReal_norm] at hdist
  have hnonneg : 0 ≤ ∫ t in Icc 0 v, m t :=
    setIntegral_nonneg measurableSet_Icc (fun t ht => hmV0 t ht)
  exact (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hdist

/-- The difference of two increment-controlled functions has the sum majorant. -/
theorem fp81v01_difference_majorant
    {G : Type*} [NormedAddCommGroup G]
    (g₁ g₂ : ℝ → G) (H : ℝ) (hH : 0 ≤ H)
    (m₁ m₂ : ℝ → ℝ)
    (hm₁ : IntegrableOn m₁ (Icc 0 H)) (hm₂ : IntegrableOn m₂ (Icc 0 H))
    (hm₁0 : ∀ t ∈ Icc 0 H, 0 ≤ m₁ t) (hm₂0 : ∀ t ∈ Icc 0 H, 0 ≤ m₂ t)
    (hinc₁ : ∀ v w, 0 ≤ v → v ≤ w → w ≤ H →
      ‖g₁ w - g₁ v‖ ≤ ∫ t in Icc v w, m₁ t)
    (hinc₂ : ∀ v w, 0 ≤ v → v ≤ w → w ≤ H →
      ‖g₂ w - g₂ v‖ ≤ ∫ t in Icc v w, m₂ t) :
    ContinuousOn (fun t => g₁ t - g₂ t) (Icc 0 H) ∧
      eVariationOn (fun t => g₁ t - g₂ t) (Icc 0 H) ≤
        ENNReal.ofReal (∫ t in Icc 0 H, m₁ t + m₂ t) := by
  have hm : IntegrableOn (fun t => m₁ t + m₂ t) (Icc 0 H) := hm₁.add hm₂
  have hm0 : ∀ t ∈ Icc 0 H, 0 ≤ m₁ t + m₂ t := fun t ht => add_nonneg (hm₁0 t ht) (hm₂0 t ht)
  have hinc : ∀ v w, 0 ≤ v → v ≤ w → w ≤ H →
      ‖(g₁ w - g₂ w) - (g₁ v - g₂ v)‖ ≤ ∫ t in Icc v w, m₁ t + m₂ t := by
    intro v w hv hvw hw
    have hsub : Icc v w ⊆ Icc 0 H := fun t ht => ⟨hv.trans ht.1, ht.2.trans hw⟩
    calc ‖(g₁ w - g₂ w) - (g₁ v - g₂ v)‖
        = ‖(g₁ w - g₁ v) - (g₂ w - g₂ v)‖ := by congr 1 <;> abel
      _ ≤ ‖g₁ w - g₁ v‖ + ‖g₂ w - g₂ v‖ := norm_sub_le _ _
      _ ≤ (∫ t in Icc v w, m₁ t) + ∫ t in Icc v w, m₂ t :=
        add_le_add (hinc₁ v w hv hvw hw) (hinc₂ v w hv hvw hw)
      _ = ∫ t in Icc v w, m₁ t + m₂ t := by
        rw [integral_add (hm₁.mono_set hsub) (hm₂.mono_set hsub)]
  exact fp81v01_regular_of_majorant (fun t => g₁ t - g₂ t) H hH
    (fun t => m₁ t + m₂ t) hm hm0 hinc

/-- Scaling a nonnegative majorant by `B` scales the total variation bound by `B`. -/
theorem fp81v01_scaled_majorant_variation
    {G : Type*} [NormedAddCommGroup G]
    (g : ℝ → G) (H B : ℝ) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (m : ℝ → ℝ) (hm : IntegrableOn m (Icc 0 H))
    (hm0 : ∀ t ∈ Icc 0 H, 0 ≤ m t)
    (hinc : ∀ v w, 0 ≤ v → v ≤ w → w ≤ H →
      ‖g w - g v‖ ≤ ∫ t in Icc v w, B * m t) :
    eVariationOn g (Icc 0 H) ≤ ENNReal.ofReal (B * ∫ t in Icc 0 H, m t) := by
  have hmB : IntegrableOn (fun t => B * m t) (Icc 0 H) := hm.const_mul B
  have hmB0 : ∀ t ∈ Icc 0 H, 0 ≤ B * m t := fun t ht => mul_nonneg hB (hm0 t ht)
  have hreg := fp81v01_regular_of_majorant g H hH (fun t => B * m t) hmB hmB0 hinc
  calc eVariationOn g (Icc 0 H)
      ≤ ENNReal.ofReal (∫ t in Icc 0 H, B * m t) := hreg.2
    _ = ENNReal.ofReal (B * ∫ t in Icc 0 H, m t) := by rw [integral_const_mul]

#print axioms fp81v01_regular_of_majorant
#print axioms fp81v01_regular_of_majorant_zero
#print axioms fp81v01_difference_majorant
#print axioms fp81v01_scaled_majorant_variation

end HRS.Fp81.V01
