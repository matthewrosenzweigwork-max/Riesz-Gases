import HRS.MS.WadAux48

/-!
# S8.3 (Route A): uniqueness of the projected backward solutions

`s85_proj_unique`: if `f` is an `IsAdjointSolutionG (projGeneratorW C μ) t φ f` and `w` the frozen classical
solution with the same datum, then `f_0 = w_0 - μ(w_0) + μ(φ)`.  Proof: the mean `μ(f_r)` is constant
(`∫ P_μ ℒ f_r dμ = 0`), the shift `κ(r) = ∫_r^t μ(ℒ f_s) ds` (continuous `m` by `s85_gen_cont_r`) turns `f` into a
classical solution `f + κ`, which agrees with `w` by uniqueness.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s85_G_facts {G : ℝ → (Euc d → ℝ) → Euc d → ℝ} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsAdjointSolutionG G t φ f) :
    ∃ B0 B1 B2 : ℝ, (∀ r ∈ Set.Icc 0 t, ∀ y, |f r y| ≤ B0) ∧
      (∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (f r) y‖ ≤ B1) ∧
      (∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (fderiv ℝ (f r)) y‖ ≤ B2) ∧
      ContinuousOn (fun q : ℝ × Euc d => f q.1 q.2) (Set.Icc 0 t ×ˢ Set.univ) ∧
      ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (f q.1) q.2) (Set.Icc 0 t ×ˢ Set.univ) ∧
      ContinuousOn (fun q : ℝ × Euc d => fderiv ℝ (fderiv ℝ (f q.1)) q.2) (Set.Icc 0 t ×ˢ Set.univ) ∧
      ContinuousOn (fun q : ℝ × Euc d => G q.1 (f q.1) q.2) (Set.Icc 0 t ×ˢ Set.univ) := by
  obtain ⟨B0, hB0⟩ := hf.bdd 0 (by norm_num)
  obtain ⟨B1, hB1⟩ := hf.bdd 1 (by norm_num)
  obtain ⟨B2, hB2⟩ := hf.bdd 2 (by norm_num)
  refine ⟨B0, B1, B2, fun r hr y => ?_, fun r hr y => ?_, fun r hr y => ?_, ?_, ?_, ?_, ?_⟩
  · have := hB0 r hr y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  · have := hB1 r hr y
    rwa [norm_iteratedFDeriv_one] at this
  · have := hB2 r hr y
    rwa [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at this
  · exact s84_contOn_of_subtype (s84_cont_D0 (F := fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1)
      (x := fun p => p.2) (hf.cont_c2 0 (by norm_num)))
  · exact s84_contOn_of_subtype (s84_cont_D1 (F := fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1)
      (x := fun p => p.2) (hf.cont_c2 1 (by norm_num)))
  · exact s84_contOn_of_subtype (s84_cont_D2 (F := fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1)
      (x := fun p => p.2) (hf.cont_c2 2 (by norm_num)))
  · exact s84_contOn_of_subtype hf.cont_time_deriv

/-- Restriction of a jointly continuous function to the slice `r ↦ (r, x₀)`. -/
theorem s85_slice_cont {t : ℝ} {F : ℝ × Euc d → ℝ} (hF : ContinuousOn F (Set.Icc 0 t ×ˢ Set.univ))
    (x₀ : Euc d) : ContinuousOn (fun r : ℝ => F (r, x₀)) (Set.Icc 0 t) := by
  have h' := hF.comp (Continuous.prodMk continuous_id (continuous_const (y := x₀))).continuousOn
    (fun (r : ℝ) (hr : r ∈ Set.Icc 0 t) =>
      (⟨hr, Set.mem_univ x₀⟩ : (r, x₀) ∈ Set.Icc 0 t ×ˢ (Set.univ : Set (Euc d))))
  exact h'

/-- Restriction of a jointly continuous function to the slice `y ↦ (r₀, y)`. -/
theorem s85_slice_cont' {t : ℝ} {F : ℝ × Euc d → ℝ} (hF : ContinuousOn F (Set.Icc 0 t ×ˢ Set.univ))
    {r₀ : ℝ} (hr₀ : r₀ ∈ Set.Icc 0 t) : Continuous (fun y : Euc d => F (r₀, y)) := by
  have h' := hF.comp_continuous (Continuous.prodMk (continuous_const (y := r₀)) continuous_id)
    (fun y => (⟨hr₀, Set.mem_univ y⟩ : (r₀, y) ∈ Set.Icc 0 t ×ˢ (Set.univ : Set (Euc d))))
  exact h'

theorem s85_proj_unique (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    {f : ℝ → Euc d → ℝ}
    (hf : IsAdjointSolutionG (projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ)) t φ f)
    {w : ℝ → Euc d → ℝ} (hw : IsClassicalAdjointW (critCoeff d a β ρβ) t φ w) (x : Euc d) :
    f 0 x = s85_V ρβ w φ x := by
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  have hprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hP
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  have hmom : Integrable (fun y : Euc d => 1 + ‖y‖) (HRS.Whole.withDensityReal ρβ) :=
    s85_first_moment hP hg
  unfold s85_V
  generalize HRS.Whole.withDensityReal ρβ = μ at hprob hmom hf ⊢
  haveI := hprob
  have hpair : ∀ ψ : Euc d → ℝ, HRS.Whole.pair μ ψ = ∫ z, ψ z ∂μ := fun ψ => rfl
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    rw [hf.terminal, hw.terminal, hpair]
    ring
  obtain ⟨B0, B1, B2, hb0, hb1, hb2, hwc, hD1, hD2, hGpc⟩ := s85_G_facts hf
  obtain ⟨BG, hBG⟩ := hf.bdd_time_deriv
  set Gp := projGeneratorW (critCoeff d a β ρβ) μ with hGp
  set m : ℝ → ℝ := fun r => ∫ y, generatorW (critCoeff d a β ρβ) r (f r) y ∂μ with hm
  have hGpdef : ∀ r x, Gp r (f r) x = generatorW (critCoeff d a β ρβ) r (f r) x - m r := fun r x => rfl
  have hI1 : Integrable (fun y : Euc d => |BG| * (1 + ‖y‖)) μ := hmom.const_mul _
  have hBGa : ∀ r ∈ Set.Icc 0 t, ∀ y, |Gp r (f r) y| ≤ |BG| * (1 + ‖y‖) := fun r hr y =>
    (hBG r hr y).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hGpcy : ∀ r ∈ Set.Icc 0 t, Continuous (fun y => Gp r (f r) y) := fun r hr =>
    s85_slice_cont' (F := fun q : ℝ × Euc d => Gp q.1 (f q.1) q.2) hGpc hr
  have hGpint : ∀ r ∈ Set.Icc 0 t, Integrable (fun y => Gp r (f r) y) μ := fun r hr =>
    s85_integrable_of_bound (hGpcy r hr).aestronglyMeasurable hI1 (hBGa r hr)
  -- m is continuous
  have hGenc : ContinuousOn (fun r => generatorW (critCoeff d a β ρβ) r (f r) 0) (Set.Icc 0 t) :=
    s85_gen_cont_r hd ha hβ hρ hf.c2 ⟨max B1 B2, fun r hr y =>
      ⟨(hb1 r hr y).trans (le_max_left _ _), (hb2 r hr y).trans (le_max_right _ _)⟩⟩ hD1 hD2 0
  have hGp0 : ContinuousOn (fun r => Gp r (f r) 0) (Set.Icc 0 t) :=
    s85_slice_cont (F := fun q : ℝ × Euc d => Gp q.1 (f q.1) q.2) hGpc 0
  have hmc : ContinuousOn m (Set.Icc 0 t) := by
    refine (hGenc.sub hGp0).congr fun r hr => ?_
    show m r = generatorW (critCoeff d a β ρβ) r (f r) 0 - Gp r (f r) 0
    rw [hGpdef]; ring
  -- the mean of the projected generator vanishes
  have hGpzero : ∀ r ∈ Set.Icc 0 t, ∫ y, Gp r (f r) y ∂μ = 0 := by
    intro r hr
    have e : ∀ y, generatorW (critCoeff d a β ρβ) r (f r) y = Gp r (f r) y + m r := fun y => by
      rw [hGpdef]; ring
    have h1 : m r = ∫ y, (Gp r (f r) y + m r) ∂μ := by
      show ∫ y, generatorW (critCoeff d a β ρβ) r (f r) y ∂μ = _
      exact integral_congr_ae (Filter.Eventually.of_forall e)
    rw [integral_add (hGpint r hr) (integrable_const _)] at h1
    simp at h1
    linarith
  -- the mean of f_r is constant
  set e : ℝ → ℝ := fun r => ∫ z, f r z ∂μ with he
  have hec : ContinuousOn e (Set.Icc 0 t) :=
    s85_cont_param (integrable_const B0) hwc hb0
  have hed : ∀ r ∈ Set.Ioo (0 : ℝ) t, HasDerivAt e 0 r := by
    intro r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) t := ⟨hr.1.le, hr.2.le⟩
    have := s85_deriv_param (μ := μ) (t := t) (r := r) hr (F := f) (F' := fun r' y => -Gp r' (f r') y)
      (bd := fun y => |BG| * (1 + ‖y‖)) (bF := fun _ => B0) hI1 (integrable_const B0)
      (fun r' hr'' => (hf.c2 r' ⟨hr''.1.le, hr''.2.le⟩).continuous) (hGpcy r hr').neg
      (fun y => hb0 r hr' y)
      (fun r' hr'' y => by rw [abs_neg]; exact hBGa r' ⟨hr''.1.le, hr''.2.le⟩ y)
      (fun y r' hr'' => hf.time_deriv y r' hr'')
    rw [integral_neg, hGpzero r hr'] at this
    simpa using this
  have hconst : e t = e 0 := by
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope e (fun _ => (0 : ℝ)) hpos hec hed
    have h1 : (e t - e 0) / (t - 0) = 0 := hc'.symm
    rw [div_eq_zero_iff] at h1
    rcases h1 with h1 | h1
    · linarith
    · linarith
  -- the shift
  have hmint : IntervalIntegrable m MeasureTheory.volume 0 t :=
    (hmc.mono (Set.uIcc_of_le hpos.le).subset).intervalIntegrable
  set κ : ℝ → ℝ := fun r => (∫ s in (0 : ℝ)..t, m s) - ∫ s in (0 : ℝ)..r, m s with hκ
  have hκc : ContinuousOn κ (Set.Icc 0 t) := by
    have hh : ContinuousOn (fun r => ∫ s in (0 : ℝ)..r, m s) (Set.Icc 0 t) := by
      have := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := t) (f := m)
        (μ := MeasureTheory.volume) (by rw [Set.uIcc_of_le hpos.le]; exact hmc.integrableOn_Icc)
      rwa [Set.uIcc_of_le hpos.le] at this
    exact continuousOn_const.sub hh
  have hκd : ∀ r ∈ Set.Ioo (0 : ℝ) t, HasDerivAt κ (-m r) r := by
    intro r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) t := ⟨hr.1.le, hr.2.le⟩
    have hmr : IntervalIntegrable m MeasureTheory.volume 0 r :=
      (hmc.mono ((Set.uIcc_of_le hr.1.le).subset.trans (Set.Icc_subset_Icc le_rfl hr.2.le))).intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter m (𝓝 r) MeasureTheory.volume :=
      (hmc.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo r hr
    have hcont : ContinuousAt m r := hmc.continuousAt (Icc_mem_nhds hr.1 hr.2)
    exact (intervalIntegral.integral_hasDerivAt_right hmr hmeas hcont).const_sub (∫ s in (0 : ℝ)..t, m s)
  have hκ't : κ t = 0 := by simp [hκ]
  have key := s85_transfer (G := Gp) (G' := generatorW (critCoeff d a β ρβ)) hf (κ := κ) (κ' := fun r => -m r) hκc hmc.neg hκd
    (fun r hr x => by
      show generatorW (critCoeff d a β ρβ) r (fun y => f r y + κ r) x = Gp r (f r) x - -m r
      rw [s85_gen_add_const a β ρβ r (f r) (κ r) x, hGpdef]; ring)
  have hφ : (fun y => φ y + κ t) = φ := by funext y; rw [hκ't, add_zero]
  rw [hφ] at key
  have hw' := s85_G_to_cl key
  have hweq : w 0 = fun y => f 0 y + κ 0 :=
    (s85_cl_unique hd ha hβ hρ ht hw hw' (r := 0) ⟨le_rfl, ht⟩)
  have hi : Integrable (f 0) μ := s85_int_bdd (hf.c2 0 ⟨le_rfl, ht⟩).continuous (hb0 0 ⟨le_rfl, ht⟩)
  have hit : Integrable φ μ := by
    have : φ = f t := hf.terminal.symm
    rw [this]
    exact s85_int_bdd (hf.c2 t ⟨ht, le_rfl⟩).continuous (hb0 t ⟨ht, le_rfl⟩)
  rw [hweq, hpair]
  have e1 : ∫ z, (f 0 z + κ 0) ∂μ = ∫ z, f 0 z ∂μ + κ 0 := by
    rw [integral_add hi (integrable_const _)]; simp
  have e2 : ∫ z, f 0 z ∂μ = ∫ z, φ z ∂μ := by
    have h1 : e 0 = ∫ z, f 0 z ∂μ := rfl
    have h2 : e t = ∫ z, φ z ∂μ := by
      show ∫ z, f t z ∂μ = _
      rw [hf.terminal]
    rw [← h1, ← hconst, h2]
  show f 0 x = (f 0 x + κ 0) - ∫ z, (f 0 z + κ 0) ∂μ + ∫ z, φ z ∂μ
  rw [e1, e2]
  ring

end HRS.MS.Wad
