import HRS.MC.S7PIEMeas

/-!
# Packet PI-E, part 10: the drift measure (continuity, bound) from the standing data

Dominated convergence for `t ↦ ∫ 1_{u ≤ t} V^{t,u} b(u) du` with dominating function `C ‖b(u)‖`.
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.PIE

open HRS HRS.PDE HRS.A33 HRS.Sec7

variable {d : ℕ}

theorem pie_drift_main {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} {m : ℝ} {n₀ : ℕ}
    (P : PIEData J D μ T m n₀) :
    ∃ C : ℝ, ∀ b : ℝ → NegSobolev d m, MemLp b 1 (volume.restrict (Set.Icc (0 : ℝ) T)) →
      ∀ a a' : ℝ, 0 ≤ a → a ≤ a' → a' ≤ T →
      (Continuous fun t : Set.Icc (0 : ℝ) T => ∫ u in Set.Ioc a (min a' t), Vprop D μ m t u (b u)) ∧
      ‖driftInc D μ m T b a a'‖ ≤ C * ∫ u in Set.Ioc a a', ‖b u‖ := by
  classical
  have P' := P
  obtain ⟨H, hn₀, hJ, hm0, hm1⟩ := P
  obtain ⟨C, hC0, hCb⟩ := pie_Vbound H m n₀ hn₀ hJ hm0 hm1
  refine ⟨C, fun b hb a a' ha haa' ha'T => ?_⟩
  set μR : Measure ℝ := volume.restrict (Set.Ioc a a') with hμR
  have hsubT : Set.Ioc a a' ⊆ Set.Icc 0 T := fun u hu => ⟨ha.trans hu.1.le, hu.2.trans ha'T⟩
  have hbI : Integrable (fun u => ‖b u‖) μR := by
    have h1 : Integrable b (volume.restrict (Set.Icc (0 : ℝ) T)) := hb.integrable le_rfl
    have h2 : Integrable b μR := h1.mono_measure (Measure.restrict_mono hsubT le_rfl)
    exact h2.norm
  set Fm : Set.Icc (0 : ℝ) T → ℝ → NegSobolev d m := fun t u =>
    Set.indicator (Set.Iic t.1) (fun u => Vprop D μ m t.1 u (b u)) u with hFm
  -- the integral over `Ioc a (min a' t)` as an integral of `Fm t`
  have hclaim1 : ∀ t : Set.Icc (0 : ℝ) T,
      ∫ u in Set.Ioc a (min a' t.1), Vprop D μ m t.1 u (b u) = ∫ u, Fm t u ∂μR := by
    intro t
    simp only [hFm]
    rw [integral_indicator measurableSet_Iic, hμR, Measure.restrict_restrict measurableSet_Iic]
    congr 2
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc, le_min_iff]
    tauto
  -- pointwise bound
  have hFbound : ∀ t : Set.Icc (0 : ℝ) T, ∀ᵐ u ∂μR, ‖Fm t u‖ ≤ C * ‖b u‖ := by
    intro t
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
    simp only [hFm]
    by_cases hut : u ≤ t.1
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 hut)]
      have ht : t.1 ∈ Set.Ioc 0 T := ⟨lt_of_le_of_lt ha (lt_of_lt_of_le hu.1 hut), t.2.2⟩
      exact hCb t.1 ht u ⟨ha.trans hu.1.le, hut⟩ (b u)
    · rw [Set.indicator_of_notMem (by simpa using hut)]
      simpa using mul_nonneg hC0 (norm_nonneg (b u))
  -- measurability
  have hFmeas : ∀ t : Set.Icc (0 : ℝ) T, AEStronglyMeasurable (Fm t) μR := by
    intro t
    simp only [hFm]
    rw [aestronglyMeasurable_indicator_iff measurableSet_Iic, hμR, Measure.restrict_restrict measurableSet_Iic]
    by_cases ht0 : 0 < t.1
    · have hSt : Set.Iic t.1 ∩ Set.Ioc a a' ⊆ Set.Icc 0 t.1 := fun u hu =>
        ⟨ha.trans hu.2.1.le, hu.1⟩
      have hbS : AEStronglyMeasurable b (volume.restrict (Set.Iic t.1 ∩ Set.Ioc a a')) :=
        hb.aestronglyMeasurable.mono_measure (Measure.restrict_mono
          (fun u hu => hsubT hu.2) le_rfl)
      exact pie_V_aesm P' ⟨ht0, t.2.2⟩ (measurableSet_Iic.inter measurableSet_Ioc) hSt hbS
    · have h0 : t.1 = 0 := le_antisymm (not_lt.1 ht0) t.2.1
      have : Set.Iic t.1 ∩ Set.Ioc a a' = ∅ := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, -⟩
        rw [h0] at h1
        linarith
      rw [this, Measure.restrict_empty]
      exact aestronglyMeasurable_zero_measure _
  -- continuity
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) T =>
      ∫ u in Set.Ioc a (min a' t.1), Vprop D μ m t.1 u (b u) := by
    simp_rw [hclaim1]
    rw [continuous_iff_continuousAt]
    intro x₀
    refine continuousAt_of_dominated (bound := fun u => C * ‖b u‖) (Eventually.of_forall hFmeas)
      (Eventually.of_forall hFbound) (hbI.const_mul C) ?_
    have hne : ∀ᵐ u ∂μR, u ≠ x₀.1 := by
      refine ae_restrict_of_ae ?_
      rw [ae_iff]
      simp
    filter_upwards [hne, (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => hu)]
      with u hu hmem
    rcases lt_or_gt_of_ne hu with h | h
    · -- u < x₀
      have hev : ∀ᶠ x : Set.Icc (0 : ℝ) T in 𝓝 x₀, u < x.1 :=
        (continuous_subtype_val.tendsto x₀).eventually (lt_mem_nhds h)
      have hu0 : 0 ≤ u := ha.trans hmem.1.le
      have := pie_V_tendsto_t P' hu0 x₀ h (b u)
      have hF0 : Fm x₀ u = Vprop D μ m x₀.1 u (b u) := by
        simp only [hFm]
        rw [Set.indicator_of_mem (Set.mem_Iic.2 h.le)]
      rw [ContinuousAt, hF0]
      refine this.congr' ?_
      filter_upwards [hev] with x hx
      simp only [hFm]
      rw [Set.indicator_of_mem (Set.mem_Iic.2 hx.le)]
    · -- u > x₀
      have hev : ∀ᶠ x : Set.Icc (0 : ℝ) T in 𝓝 x₀, x.1 < u :=
        (continuous_subtype_val.tendsto x₀).eventually (gt_mem_nhds h)
      have hz : (fun x : Set.Icc (0 : ℝ) T => Fm x u) =ᶠ[𝓝 x₀] fun _ => 0 := by
        filter_upwards [hev] with x hx
        simp only [hFm]
        rw [Set.indicator_of_notMem (by simpa using hx)]
      exact (continuousAt_const).congr hz.symm
  refine ⟨hcont, ?_⟩
  have hM : 0 ≤ C * ∫ u in Set.Ioc a a', ‖b u‖ :=
    mul_nonneg hC0 (integral_nonneg fun u => norm_nonneg _)
  have hdrift : driftInc D μ m T b a a' = (⟨fun t : Set.Icc (0 : ℝ) T =>
      ∫ u in Set.Ioc a (min a' t.1), Vprop D μ m t.1 u (b u), hcont⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
    unfold driftInc pathOf
    exact dif_pos hcont
  rw [hdrift]
  show ‖(⟨fun t : Set.Icc (0 : ℝ) T => ∫ u in Set.Ioc a (min a' t.1), Vprop D μ m t.1 u (b u), hcont⟩ :
    C(Set.Icc (0 : ℝ) T, NegSobolev d m))‖ ≤ _
  refine (ContinuousMap.norm_le _ hM).2 fun t => ?_
  show ‖∫ u in Set.Ioc a (min a' t.1), Vprop D μ m t.1 u (b u)‖ ≤ _
  rw [hclaim1 t]
  calc ‖∫ u, Fm t u ∂μR‖ ≤ ∫ u, C * ‖b u‖ ∂μR :=
        norm_integral_le_of_norm_le (hbI.const_mul C) (hFbound t)
    _ = C * ∫ u in Set.Ioc a a', ‖b u‖ := by rw [integral_const_mul]

end HRS.MC.Sec7.PIE

end
