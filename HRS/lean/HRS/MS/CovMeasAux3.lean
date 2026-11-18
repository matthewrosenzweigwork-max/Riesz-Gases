import HRS.MS.CovMeasAux2

/-!
# S10.1 (worker S101B), part 3: the time derivative as a measurable bounded function, the fundamental theorem of calculus in `t`

`s101Th C m T τ s α x = 1_{τ<s≤T} ∂_sU^{τ,s}φ_α(x)` is the `A'`-coordinate of the feature.  `s101_th_aesm`: measurable in `s`
(derivative of a function differentiable within `[τ,T]`); `s101_ftc`: `U^{τ,t}φ_α(x) - U^{τ,τ}φ_α(x) = ∫_τ^t ∂_sU^{τ,s}φ_α(x) ds`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go

variable {d : ℕ}

/-- `1_{τ<s≤T} ∂_sU^{τ,s}φ_α(x)`. -/
def s101Th (C : WholeCoeff d) (m T : ℝ) (τ s : ℝ) (α : MultiIndex d) (x : Euc d) : ℝ :=
  if τ < s ∧ s ≤ T then s101Dt C m T τ s α x else 0

lemma s101_derivWithin_Icc_eq {f : ℝ → ℝ} {a b s : ℝ} (hs : s ∈ Ioo a b)
    (hf : DifferentiableWithinAt ℝ f (Icc a b) s) :
    derivWithin f (Icc a b) s = derivWithin f (Ici s) s := by
  have hn : Icc a b ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
  have hda : DifferentiableAt ℝ f s := hf.differentiableAt hn
  rw [derivWithin_of_mem_nhds hn]
  exact (hda.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici s)).symm

theorem s101_th_aesm {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (α : MultiIndex d) (x : Euc d) :
    AEStronglyMeasurable (fun s => s101Th C m T τ s α x) volume := by
  set f : ℝ → ℝ := fun t' => propagatorW C τ t' (oscTestFun m α) x with hf
  have hg : Measurable fun s : ℝ => if τ < s ∧ s < T then derivWithin f (Ici s) s else 0 :=
    Measurable.ite (measurableSet_Ioi.inter measurableSet_Iio : MeasurableSet (Ioi τ ∩ Iio T))
      (measurable_derivWithin_Ici f) measurable_const
  refine hg.aemeasurable.aestronglyMeasurable.congr ?_
  have hae : ∀ᵐ s : ℝ, s ≠ T := by
    have : volume ({T} : Set ℝ) = 0 := Real.volume_singleton
    exact (measure_eq_zero_iff_ae_notMem.1 this).mono fun s hs => by simpa using hs
  filter_upwards [hae] with s hsT
  by_cases h : τ < s ∧ s < T
  · have h' : τ < s ∧ s ≤ T := ⟨h.1, h.2.le⟩
    have hh : τ < s ∧ s < T := h
    have e1 : s101Th C m T τ s α x = derivWithin f (Icc τ T) s := by
      simp only [s101Th, h', ite_true]; rfl
    rw [e1, if_pos hh]
    exact (s101_derivWithin_Icc_eq ⟨h.1, h.2⟩ (hD.diffT α τ hτ x s ⟨h.1.le, h.2.le⟩)).symm
  · have h' : ¬ (τ < s ∧ s ≤ T) := by
      rintro ⟨h1, h2⟩
      exact h ⟨h1, lt_of_le_of_ne h2 hsT⟩
    rw [if_neg h]
    simp [s101Th, h']

lemma s101_th_bound {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (s : ℝ) (α : MultiIndex d) (x : Euc d) :
    |s101Th C m T τ s α x| ≤ c α := by
  by_cases h : τ < s ∧ s ≤ T
  · have := hD.bddD α τ hτ s ⟨h.1.le, h.2⟩ 0 (Nat.zero_le _) x
    simpa [s101Th, h] using this
  · simpa [s101Th, h] using hD.nonneg α

theorem s101_ftc {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}
    (hD : S101Data C m T r c) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) {t : ℝ} (ht : t ∈ Icc τ T)
    (α : MultiIndex d) (x : Euc d) :
    propagatorW C τ t (oscTestFun m α) x - propagatorW C τ τ (oscTestFun m α) x =
      ∫ s in τ..t, s101Th C m T τ s α x := by
  set f : ℝ → ℝ := fun t' => propagatorW C τ t' (oscTestFun m α) x with hf
  have hτT : τ ∈ Icc τ T := ⟨le_rfl, hτ.2⟩
  have hcont : ContinuousOn f (Icc τ t) := by
    intro s hs
    exact ((hD.diffT α τ hτ x s ⟨hs.1, hs.2.trans ht.2⟩).continuousWithinAt).mono
      (Icc_subset_Icc_right ht.2)
  have hderiv : ∀ s ∈ Ioo τ t, HasDerivWithinAt f (s101Th C m T τ s α x) (Ioi s) s := by
    intro s hs
    have hsT : s ≤ T := hs.2.le.trans ht.2
    have h1 := (hD.diffT α τ hτ x s ⟨hs.1.le, hsT⟩).hasDerivWithinAt
    have hth : s101Th C m T τ s α x = derivWithin f (Icc τ T) s := by
      simp only [s101Th, hs.1, hsT, and_self, ite_true]; rfl
    rw [hth]
    refine h1.mono_of_mem_nhdsWithin ?_
    have : Icc τ T ∈ 𝓝[>] s := by
      have h2 : Ioo τ T ∈ 𝓝 s := Ioo_mem_nhds hs.1 (lt_of_lt_of_le hs.2 ht.2)
      exact mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset h2 Ioo_subset_Icc_self)
    exact this
  have hint : IntervalIntegrable (fun s => s101Th C m T τ s α x) volume τ t := by
    have hm := s101_th_aesm hD hτ α x
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).2 ?_
    refine Measure.integrableOn_of_bounded (M := c α) (by simp) hm ?_
    exact Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]; exact s101_th_bound hD hτ s α x
  have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 hcont hderiv hint
  rw [this]

end HRS.MS.CovMeas
