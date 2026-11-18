import HRS.PDE.TorusFPEntropyClassicalAux1

/-!
# D3-a (classical layer), helper 2: parametric integrals, the integrated product rule, regularity of tests

* `d3a_continuousOn_integral`: continuity of `s ↦ ∫ H s x dν` for `H` jointly continuous on `[0,τ] × 𝕋^n`;
* `d3a_ftc`: for `F, D` jointly continuous on `[0,τ] × 𝕋^n` with `∂_s F = D` on `(0,τ)`,
  `∫ F_τ dν - ∫ F_0 dν = ∫_0^τ ∫ D_r dν dr` (differentiation under the integral, compact torus);
* restriction of `IsC12Test` to a shorter interval, joint continuity of gradients.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

theorem d3a_contOn_time {τ : ℝ} {F : ℝ → Torus n → ℝ}
    (hF : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => F p.1 p.2) (x : Torus n) :
    ContinuousOn (fun s => F s x) (Set.Icc 0 τ) := by
  rw [continuousOn_iff_continuous_restrict]
  exact hF.comp (continuous_id.prodMk continuous_const)

theorem d3a_contOn_space {τ : ℝ} {F : ℝ → Torus n → ℝ}
    (hF : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => F p.1 p.2) {s : ℝ}
    (hs : s ∈ Set.Icc 0 τ) : Continuous (F s) :=
  hF.comp (Continuous.prodMk continuous_const continuous_id :
    Continuous fun x : Torus n => ((⟨s, hs⟩ : Set.Icc (0 : ℝ) τ), x))

theorem d3a_bound {τ : ℝ} {F : ℝ → Torus n → ℝ}
    (hF : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => F p.1 p.2) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc 0 τ, ∀ x, ‖F s x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Set.Icc (0 : ℝ) τ × Torus n)).exists_bound_of_continuousOn
    hF.continuousOn
  exact ⟨C, fun s hs x => hC (⟨s, hs⟩, x) (Set.mem_univ _)⟩

theorem d3a_continuousOn_integral {τ : ℝ} {ν : Measure (Torus n)} [IsFiniteMeasure ν]
    {H : ℝ → Torus n → ℝ} (hH : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => H p.1 p.2) :
    ContinuousOn (fun s => ∫ x, H s x ∂ν) (Set.Icc 0 τ) := by
  obtain ⟨C, hC⟩ := d3a_bound hH
  exact continuousOn_of_dominated (bound := fun _ => C)
    (fun s hs => (d3a_contOn_space hH hs).aestronglyMeasurable)
    (fun s hs => ae_of_all _ fun x => hC s hs x) (integrable_const _)
    (ae_of_all _ fun x => d3a_contOn_time hH x)

/-- Integrated product rule / fundamental theorem of calculus under the integral sign. -/
theorem d3a_ftc {τ : ℝ} (hτ : 0 < τ) {ν : Measure (Torus n)} [IsFiniteMeasure ν]
    {F D : ℝ → Torus n → ℝ}
    (hF : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => F p.1 p.2)
    (hD : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => D p.1 p.2)
    (hder : ∀ x : Torus n, ∀ r ∈ Set.Ioo 0 τ, HasDerivAt (fun s => F s x) (D r x) r) :
    ∫ x, F τ x ∂ν - ∫ x, F 0 x ∂ν = ∫ r in Set.Icc 0 τ, ∫ x, D r x ∂ν := by
  obtain ⟨C, hC⟩ := d3a_bound hD
  have hcontF := d3a_continuousOn_integral (ν := ν) hF
  have hcontD := d3a_continuousOn_integral (ν := ν) hD
  have hderiv : ∀ s ∈ Set.Ioo 0 τ,
      HasDerivAt (fun s => ∫ x, F s x ∂ν) (∫ x, D s x ∂ν) s := by
    intro s hs
    have hsI : s ∈ Set.Icc 0 τ := ⟨hs.1.le, hs.2.le⟩
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
      (F := fun s' x => F s' x) (F' := fun s' x => D s' x)
      (x₀ := s) (s := Set.Ioo 0 τ) (bound := fun _ => C)
      (Ioo_mem_nhds hs.1 hs.2) ?_ ?_ ?_ ?_ (integrable_const _) ?_).2
    · exact Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) fun s' hs' =>
        (d3a_contOn_space hF ⟨hs'.1.le, hs'.2.le⟩).aestronglyMeasurable
    · exact d3a_hint ν (d3a_contOn_space hF hsI)
    · exact (d3a_contOn_space hD hsI).aestronglyMeasurable
    · exact ae_of_all _ fun a s' hs' => hC s' ⟨hs'.1.le, hs'.2.le⟩ a
    · exact ae_of_all _ fun a s' hs' => hder a s' hs'
  have hint : IntervalIntegrable (fun s => ∫ x, D s x ∂ν) volume 0 τ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hτ.le]
    exact hcontD
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ.le hcontF hderiv hint
  rw [intervalIntegral.integral_of_le hτ.le, ← integral_Icc_eq_integral_Ioc] at this
  linarith

/-- Restriction of a `C^{1,2}` test on `[0,t]` to `[0,τ]`, `τ ∈ [0,t]`. -/
theorem d3a_C12_restrict {t τ : ℝ} {f ft : ℝ → Torus n → ℝ} (hf : IsC12Test t f ft)
    (hτ : τ ∈ Set.Icc 0 t) : IsC12Test τ f ft where
  c2 r hr := hf.c2 r ⟨hr.1, hr.2.trans hτ.2⟩
  cont_c2 j hj := by
    have hmap : Continuous fun p : Set.Icc (0 : ℝ) τ × Euc n =>
        ((⟨p.1.1, p.1.2.1, p.1.2.2.trans hτ.2⟩ : Set.Icc (0 : ℝ) t), p.2) :=
      ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd
    exact (hf.cont_c2 j hj).comp hmap
  time_deriv x r hr := hf.time_deriv x r ⟨hr.1, hr.2.trans_le hτ.2⟩
  cont_time_deriv := by
    have hmap : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n =>
        ((⟨p.1.1, p.1.2.1, p.1.2.2.trans hτ.2⟩ : Set.Icc (0 : ℝ) t), p.2) :=
      ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd
    exact hf.cont_time_deriv.comp hmap

/-- Joint continuity of the gradient of a `C^{1,2}` test. -/
theorem d3a_continuous_grad {τ : ℝ} {f ft : ℝ → Torus n → ℝ} (hf : IsC12Test τ f ft) :
    Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => Torus.grad (f p.1) p.2 := by
  apply d1_continuous_prod_of_lift (h := fun p : Set.Icc (0 : ℝ) τ × Torus n => Torus.grad (f p.1) p.2)
  have e : (fun p : Set.Icc (0 : ℝ) τ × Euc n => Torus.grad (f p.1) (Torus.mk p.2)) =
      fun p => gradient (Torus.lift (f p.1)) p.2 := by
    funext p
    exact grad_mk _ _
  rw [e]
  exact hf.continuous_gradient_lift

/-- Joint continuity of the (coordinate) partial derivatives of a `C^{1,2}` test. -/
theorem d3a_continuous_pd {τ : ℝ} {f ft : ℝ → Torus n → ℝ} (hf : IsC12Test τ f ft) (j : Fin n) :
    Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => Torus.partialDeriv j (f p.1) p.2 := by
  have h := (EuclideanSpace.proj j : Euc n →L[ℝ] ℝ).continuous.comp (d3a_continuous_grad hf)
  refine h.congr fun p => ?_
  simp [d1c_grad_component]

end HRS
