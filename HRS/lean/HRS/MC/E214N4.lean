import HRS.MC.E214PD

/-!
# E214N4: time-homogeneity of the window drift (the near-part identity of `shift_identity`)

For a regime with a time-constant density, `V^{h+t,h+v} = V^{t,v}`, hence the drift of the original coefficient
restricted to the times `≥ h` at the window `a + h` is the drift of the shifted coefficient at the window `a`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214N

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final

variable {d : ℕ}

section VShift

variable {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m)

theorem vprop_shift (hρ : ∀ t t', (regime S β₀ hE).ρ t = (regime S β₀ hE).ρ t') {h : ℝ} (hh : 0 ≤ h)
    {w t : ℝ} (hw : 0 ≤ w) (hwt : w ≤ t) (F : NegSobolev d m) :
    Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (h + t) (h + w) F =
      Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t w F := by
  unfold Vprop
  congr 1
  funext k
  congr 1
  have hG : 0 < max t 1 := lt_max_of_lt_right one_pos
  have := HRS.MC.E213U2.e213u2_propagator_shift (regime S β₀ hE) hh hG hw hwt (le_max_left t 1)
    (HRS.FieldSingAux.isSmooth_realMode k)
  have hfun : (fun τ => (regime S β₀ hE).ρ (h + τ)) = (regime S β₀ hE).ρ := funext fun τ => hρ _ _
  rw [hfun] at this
  exact this.symm

/-- The integral identity behind the near-part identity of the drift. -/
theorem drift_integral_shift (hρ : ∀ t t', (regime S β₀ hE).ρ t = (regime S β₀ hE).ρ t') {a h : ℝ}
    (ha : 0 ≤ a) (hh : 0 ≤ h) (bq : ℝ → NegSobolev d (rLvl d)) {t : ℝ} (ht : 0 ≤ t) :
    (∫ v in Set.Ioc 0 (a + h + t), Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + h + t) v
        (nearCoef h (fun v => NegSobolev.embed m (bq v)) v)) =
      ∫ v in Set.Ioc 0 (a + t), Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + t) v
        (NegSobolev.embed m (bq (h + v))) := by
  set g : ℝ → NegSobolev d m := fun u =>
    Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + h + t) u (NegSobolev.embed m (bq u)) with hg
  have step1 : (∫ v in Set.Ioc 0 (a + h + t), Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + h + t) v
        (nearCoef h (fun v => NegSobolev.embed m (bq v)) v)) = ∫ v in Set.Ioc h (a + h + t), g v := by
    rw [setIntegral_eq_of_subset_of_ae_diff_eq_zero measurableSet_Ioc.nullMeasurableSet
      (Set.Ioc_subset_Ioc_left hh)]
    · refine setIntegral_congr_fun measurableSet_Ioc (fun v hv => ?_)
      simp only [hg, nearCoef, if_pos hv.1.le]
    · have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ h := by
        have := (Set.countable_singleton h).ae_notMem (volume : Measure ℝ)
        filter_upwards [this] with u hu
        simpa using hu
      filter_upwards [hne] with u hu hmem
      have hle : u ≤ h := by
        by_contra hcon
        exact hmem.2 ⟨not_le.1 hcon, hmem.1.2⟩
      have : nearCoef h (fun v => NegSobolev.embed m (bq v)) u = 0 := by
        unfold nearCoef
        rw [if_neg (not_le.2 (lt_of_le_of_ne hle hu))]
      rw [this]
      exact HRS.MC.E213U10.u10_vprop_zero _ _ _ _ _
  rw [step1]
  have hmp := measurePreserving_add_left (volume : Measure ℝ) h
  have hemb : MeasurableEmbedding (fun x : ℝ => h + x) := measurableEmbedding_addLeft h
  have hpre : (fun x : ℝ => h + x) ⁻¹' Set.Ioc h (a + h + t) = Set.Ioc 0 (a + t) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have := hmp.setIntegral_preimage_emb hemb g (Set.Ioc h (a + h + t))
  rw [hpre] at this
  rw [← this]
  refine setIntegral_congr_fun measurableSet_Ioc (fun v hv => ?_)
  simp only [hg]
  have := vprop_shift hE hρ hh (w := v) (t := a + t) hv.1.le hv.2 (NegSobolev.embed m (bq (h + v)))
  rw [show h + (a + t) = a + h + t by ring] at this
  exact this

end VShift

end HRS.MC.E214N

end
