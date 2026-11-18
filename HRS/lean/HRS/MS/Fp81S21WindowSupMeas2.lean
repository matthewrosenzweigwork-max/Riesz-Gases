import HRS.MS.Fp81S21WindowSupMeas

/-! Continuous window suprema and countable dense time sets. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal
namespace HRS.Fp81.S21

/-- The extended nonnegative supremum on a compact interval is determined by
any dense subset. -/
theorem fp81s21_window_enorm_sup_dense {f : ℝ → ℝ} {b T : ℝ}
    (hf : ContinuousOn f (Icc b T)) {D : Set ℝ}
    (hDs : D ⊆ Icc b T) (hDd : Icc b T ⊆ closure D) :
    (⨆ t : Icc b T, ‖f t‖ₑ) = ⨆ d ∈ D, ‖f d‖ₑ := by
  rw [← iSup_subtype' (p := fun t => t ∈ Icc b T) (f := fun t _ => ‖f t‖ₑ)]
  refine le_antisymm (iSup₂_le fun t ht => ?_)
    (iSup₂_le fun d hd => le_iSup₂ (f := fun t _ => ‖f t‖ₑ) d (hDs hd))
  obtain ⟨u, hu, hut⟩ := mem_closure_iff_seq_limit.1 (hDd ht)
  have hut' : Tendsto u atTop (𝓝[Icc b T] t) :=
    tendsto_nhdsWithin_iff.2 ⟨hut, Eventually.of_forall fun n => hDs (hu n)⟩
  have h1 : Tendsto (fun n => ‖f (u n)‖ₑ) atTop (𝓝 ‖f t‖ₑ) :=
    (continuous_enorm.tendsto _).comp ((hf t ht).tendsto.comp hut')
  exact le_of_tendsto' h1 fun n => le_iSup₂ (f := fun d _ => ‖f d‖ₑ) (u n) (hu n)

/-- For continuous sample paths the real supremum is bounded, agrees with
the extended supremum, and is almost everywhere measurable. -/
theorem fp81s21_window_sup_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ → Ω → ℝ) (b T : ℝ) (hbT : b ≤ T)
    (hm : ∀ t ∈ Icc b T, AEMeasurable (X t) P)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) (Icc b T)) :
    ∃ D : Set ℝ, D.Countable ∧ D ⊆ Icc b T ∧ Icc b T ⊆ closure D ∧
      (∀ᵐ ω ∂P, BddAbove (Set.range (fun t : Icc b T => ‖X t ω‖)) ∧
        ENNReal.ofReal (⨆ t : Icc b T, ‖X t ω‖) = ⨆ d ∈ D, ‖X d ω‖ₑ) ∧
      AEMeasurable (fun ω => ⨆ t : Icc b T, ‖X t ω‖) P := by
  classical
  obtain ⟨D, hDc, hDs, hDd⟩ := TopologicalSpace.exists_countable_dense_subset (Icc b T)
  letI : Nonempty (Icc b T) := ⟨⟨b, ⟨le_rfl, hbT⟩⟩⟩
  have hbdd : ∀ᵐ ω ∂P, BddAbove (Set.range (fun t : Icc b T => ‖X t ω‖)) := by
    filter_upwards [hc] with ω hω
    have hcompact : IsCompact ((fun t => ‖X t ω‖) '' Icc b T) :=
      isCompact_Icc.image_of_continuousOn hω.norm
    convert hcompact.bddAbove using 1
    ext y
    simp only [Set.mem_range, Set.mem_image, Subtype.exists]
    tauto
  have heq : ∀ᵐ ω ∂P,
      ENNReal.ofReal (⨆ t : Icc b T, ‖X t ω‖) = ⨆ d ∈ D, ‖X d ω‖ₑ := by
    filter_upwards [hc, hbdd] with ω hω hB
    rw [← HRS.MS.R2WinOrb.s103_ofReal_iSup _ (fun t => norm_nonneg _) hB]
    simpa only [← Real.enorm_eq_ofReal (norm_nonneg _), enorm_norm] using
      fp81s21_window_enorm_sup_dense hω hDs hDd
  have hdmeas : AEMeasurable (fun ω => ⨆ d ∈ D, ‖X d ω‖ₑ) P :=
    AEMeasurable.biSup D hDc fun d hd => (hm d (hDs hd)).enorm
  have hreal : AEMeasurable (fun ω => (⨆ d ∈ D, ‖X d ω‖ₑ).toReal) P :=
    ENNReal.measurable_toReal.comp_aemeasurable hdmeas
  refine ⟨D, hDc, hDs, hDd, ?_, ?_⟩
  · filter_upwards [hbdd, heq] with ω h1 h2
    exact ⟨h1, h2⟩
  · apply hreal.congr
    filter_upwards [heq] with ω hω
    rw [← hω, ENNReal.toReal_ofReal]
    exact Real.iSup_nonneg fun t => norm_nonneg _

#print axioms fp81s21_window_enorm_sup_dense
#print axioms fp81s21_window_sup_measurable
end HRS.Fp81.S21
end
