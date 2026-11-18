import HRS.MS.MfeConfAux118

/-!
# S.B.1, packet F9 (part 22): the time integral of the source converges (abstract form)

`sb1_src_tendsto_abs`: if `a_M = -κ (c_M - EQ_M) + b_M` on `[0,T]` with `c_M → c`, `b_M → 0` pointwise, `|-κ c_M + b_M| ≤ G` integrable,
`a_M` measurable, and the integrals of `EQ_M` converge, then `∫_0^t a_M → ∫_0^t a` for `a = -κ (c - EQ)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MfeConf

theorem sb1_src_tendsto_abs {T κ : ℝ} {aM cM bM EQM : ℕ → ℝ → ℝ} {a c EQ : ℝ → ℝ}
    (hdec : ∀ M, ∀ s ∈ Set.Icc (0 : ℝ) T, aM M s = -κ * (cM M s - EQM M s) + bM M s)
    (hlim : ∀ s ∈ Set.Icc (0 : ℝ) T, a s = -κ * (c s - EQ s))
    (hc : ∀ s ∈ Set.Icc (0 : ℝ) T, Tendsto (fun M => cM M s) atTop (𝓝 (c s)))
    (hb : ∀ s ∈ Set.Icc (0 : ℝ) T, Tendsto (fun M => bM M s) atTop (𝓝 0))
    {G : ℝ → ℝ} (hG : IntegrableOn G (Set.Icc 0 T))
    (hbd : ∀ M, ∀ s ∈ Set.Icc (0 : ℝ) T, |-κ * cM M s + bM M s| ≤ G s)
    (hmeas : ∀ M, AEStronglyMeasurable (aM M) (volume.restrict (Set.Icc 0 T)))
    (hEQi : ∀ M, IntegrableOn (EQM M) (Set.Icc 0 T)) (hEQ : IntegrableOn EQ (Set.Icc 0 T))
    (hEQt : ∀ t ∈ Set.Icc (0 : ℝ) T, Tendsto (fun M => ∫ s in Set.Icc (0 : ℝ) t, EQM M s) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) t, EQ s)))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IntegrableOn a (Set.Icc 0 T) ∧
    Tendsto (fun M => ∫ s in Set.Icc (0 : ℝ) t, aM M s) atTop (𝓝 (∫ s in Set.Icc (0 : ℝ) t, a s)) := by
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  have hmeasI : MeasurableSet (Set.Icc (0 : ℝ) t) := measurableSet_Icc
  set dM : ℕ → ℝ → ℝ := fun M s => -κ * cM M s + bM M s with hdM
  have hdmeas : ∀ M, AEStronglyMeasurable (dM M) (volume.restrict (Set.Icc 0 T)) := by
    intro M
    have h1 := (hmeas M).sub (((hEQi M).aestronglyMeasurable).const_mul κ)
    refine h1.congr ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_))
    simp only [hdM, Pi.sub_apply, hdec M s hs]
    ring
  have hdlim : ∀ s ∈ Set.Icc (0 : ℝ) T, Tendsto (fun M => dM M s) atTop (𝓝 (-κ * c s)) := by
    intro s hs
    have := ((hc s hs).const_mul (-κ)).add (hb s hs)
    simpa [hdM] using this
  have hdi : ∀ M, IntegrableOn (dM M) (Set.Icc 0 T) := fun M =>
    Integrable.mono' hG (hdmeas M) ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => by
      rw [Real.norm_eq_abs]; exact hbd M s hs))
  have hclim_meas : AEStronglyMeasurable (fun s => -κ * c s) (volume.restrict (Set.Icc 0 T)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hdmeas
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hdlim))
  have hci : IntegrableOn (fun s => -κ * c s) (Set.Icc 0 T) := by
    refine Integrable.mono' hG hclim_meas ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_))
    rw [Real.norm_eq_abs]
    exact le_of_tendsto' ((hdlim s hs).abs) fun M => hbd M s hs
  -- the dominated convergence in time
  have hdint : Tendsto (fun M => ∫ s in Set.Icc (0 : ℝ) t, dM M s) atTop (𝓝 (∫ s in Set.Icc (0 : ℝ) t, -κ * c s)) := by
    refine tendsto_integral_of_dominated_convergence G
      (fun M => (hdmeas M).mono_measure (Measure.restrict_mono hsub le_rfl)) (hG.mono_set hsub)
      (fun M => (ae_restrict_iff' hmeasI).2 (Eventually.of_forall fun s hs => by
        rw [Real.norm_eq_abs]; exact hbd M s (hsub hs)))
      ((ae_restrict_iff' hmeasI).2 (Eventually.of_forall fun s hs => hdlim s (hsub hs)))
  have hsplit : ∀ M, ∫ s in Set.Icc (0 : ℝ) t, aM M s =
      (∫ s in Set.Icc (0 : ℝ) t, dM M s) + κ * ∫ s in Set.Icc (0 : ℝ) t, EQM M s := by
    intro M
    rw [← integral_const_mul, ← integral_add ((hdi M).mono_set hsub) (((hEQi M).mono_set hsub).const_mul κ)]
    refine setIntegral_congr_fun hmeasI fun s hs => ?_
    simp only [hdM, hdec M s (hsub hs)]
    ring
  have hasplit : ∫ s in Set.Icc (0 : ℝ) t, a s =
      (∫ s in Set.Icc (0 : ℝ) t, -κ * c s) + κ * ∫ s in Set.Icc (0 : ℝ) t, EQ s := by
    rw [← integral_const_mul, ← integral_add (hci.mono_set hsub) ((hEQ.mono_set hsub).const_mul κ)]
    refine setIntegral_congr_fun hmeasI fun s hs => ?_
    simp only [hlim s (hsub hs)]
    ring
  refine ⟨?_, ?_⟩
  · refine ((hci.add (hEQ.const_mul κ))).congr ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_))
    simp only [Pi.add_apply, hlim s hs]
    ring
  simp only [hsplit, hasplit]
  exact hdint.add ((hEQt t ht).const_mul κ)

end HRS.MS.MfeConf
