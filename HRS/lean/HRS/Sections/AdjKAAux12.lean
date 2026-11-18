import HRS.Sections.AdjKAAux11

/-!
# ADJKA part 12: rational approximation, window trace bounds, concatenated partitions
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjka_lintegral_trace_window {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a b B : ℝ} (hab : a ≤ b) (hB : 0 ≤ B) (f : ℝ → Ω → ℝ) (hf : ∀ u ω, f u ω ≤ B) {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ ω, (∫⁻ u in Icc a b, ENNReal.ofReal (f u ω)) ^ r ∂P ≤ ENNReal.ofReal (((b - a) * B) ^ r) := by
  have h1 : ∀ ω, ∫⁻ u in Icc a b, ENNReal.ofReal (f u ω) ≤ ENNReal.ofReal ((b - a) * B) := fun ω => by
    calc ∫⁻ u in Icc a b, ENNReal.ofReal (f u ω) ≤ ∫⁻ _u in Icc a b, ENNReal.ofReal B :=
          lintegral_mono fun u => ENNReal.ofReal_le_ofReal (hf u ω)
      _ = ENNReal.ofReal B * ENNReal.ofReal (b - a) := by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
      _ = ENNReal.ofReal ((b - a) * B) := by
          rw [mul_comm (ENNReal.ofReal B), ← ENNReal.ofReal_mul (sub_nonneg.2 hab)]
  calc ∫⁻ ω, (∫⁻ u in Icc a b, ENNReal.ofReal (f u ω)) ^ r ∂P
      ≤ ∫⁻ _ω, (ENNReal.ofReal ((b - a) * B)) ^ r ∂P := lintegral_mono fun ω => ENNReal.rpow_le_rpow (h1 ω) hr
    _ = ENNReal.ofReal (((b - a) * B) ^ r) := by
        rw [lintegral_const, measure_univ, mul_one,
          ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (sub_nonneg.2 hab) hB) hr]

theorem adjka_Icc_subset_closure_rat {T : ℝ} (hT : 0 ≤ T) : Set.Icc (0 : ℝ) T ⊆ closure (ratIcc 0 T) := by
  rcases hT.eq_or_lt with h0 | hpos
  · intro x hx
    have : x = 0 := by rw [← h0] at hx; exact le_antisymm hx.2 hx.1
    subst this
    exact subset_closure ⟨⟨le_rfl, hT⟩, ⟨0, by simp⟩⟩
  · rw [← closure_Ioo hpos.ne]
    refine closure_minimal ?_ isClosed_closure
    intro x hx
    have h1 := (Rat.denseRange_cast (𝕜 := ℝ)).open_subset_closure_inter isOpen_Ioo hx
    refine closure_mono ?_ h1
    rintro y ⟨hy1, ⟨q, hq'⟩⟩
    exact ⟨⟨hy1.1.le, hy1.2.le⟩, ⟨q, hq'⟩⟩

/-- Lower semicontinuity along a continuous path reduces the supremum to rational times. -/
theorem adjka_energy_le_sup_rat {j m T : ℝ} (hT : 0 ≤ T) {Zp : ℝ → NegSobolev d m}
    (hc : ContinuousOn Zp (Set.Icc (0 : ℝ) T)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    adjkEnergy j m (Zp t) ≤ ⨆ q ∈ ratIcc 0 T, adjkEnergy j m (Zp q) := by
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.1 (adjka_Icc_subset_closure_rat hT ht)
  have h1 : Tendsto (fun n => Zp (u n)) atTop (𝓝 (Zp t)) :=
    (hc t ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hut, Eventually.of_forall fun n => (hu n).1⟩)
  have h2 := adjka_lsc_liminf (adjkEnergy_lsc (d := d) j m) h1
  refine h2.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_))
  exact le_iSup₂ (f := fun q (_ : q ∈ ratIcc 0 T) => adjkEnergy j m (Zp q)) (u n) (hu n)

end HRS.AdjK
