import HRS.MS.R26T8AD01

/-!
# S8.2 observed-time layer, packet T8A.O05b (helper 1): multiplying a `C^{1,2}` function by a cutoff

If `f ∈ C^{1,2}([0,T] × U)` with `U` open and `θ` is smooth with `tsupport θ ⊆ U`, then `(t, x) ↦ θ(x) f(t, x)` (extended by zero
outside `U`) is `C^{1,2}([0,T] × E)`.  Every `IsC12On` field is local in `x`: near a point of `U` the product rule applies, and near a
point outside `tsupport θ` the product vanishes identically.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem r26t8a_o05b1_cont_local {β : Type*} [TopologicalSpace β] (F : ℝ × E → β) (T : ℝ)
    (U V : Set E) (hU : IsOpen U) (hV : IsOpen V) (hcover : ∀ x : E, x ∈ U ∨ x ∈ V)
    (hFU : ContinuousOn F (Set.Icc 0 T ×ˢ U)) (hFV : ContinuousOn F {p : ℝ × E | p.2 ∈ V}) :
    ContinuousOn F (Set.Icc 0 T ×ˢ (Set.univ : Set E)) := by
  intro p hp
  rcases hcover p.2 with h | h
  · have hmem : Set.Icc 0 T ×ˢ U ∈ 𝓝[Set.Icc 0 T ×ˢ (Set.univ : Set E)] p := by
      refine mem_nhdsWithin.2 ⟨{q : ℝ × E | q.2 ∈ U}, hU.preimage continuous_snd, h, ?_⟩
      intro q hq
      exact ⟨hq.2.1, hq.1⟩
    exact (hFU p ⟨hp.1, h⟩).mono_of_mem_nhdsWithin hmem
  · have hop : IsOpen {q : ℝ × E | q.2 ∈ V} := hV.preimage continuous_snd
    exact (hFV.continuousAt (hop.mem_nhds h)).continuousWithinAt

theorem r26t8a_o05b_c12_mul (T : ℝ) (U : Set E) (hU : IsOpen U) (θ : E → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hθU : tsupport θ ⊆ U) (f : ℝ → E → ℝ) (hf : IsC12On T U f) :
    IsC12On T Set.univ (fun t x => θ x * f t x) := by
  set V : Set E := (tsupport θ)ᶜ with hVdef
  have hV : IsOpen V := (isClosed_tsupport θ).isOpen_compl
  have hcover : ∀ x : E, x ∈ U ∨ x ∈ V := by
    intro x
    by_cases hx : x ∈ tsupport θ
    · exact Or.inl (hθU hx)
    · exact Or.inr hx
  have hθ0 : ∀ x ∈ V, θ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hθV : ∀ x ∈ V, θ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := fun x hx =>
    notMem_tsupport_iff_eventuallyEq.1 hx
  have hθd : Differentiable ℝ θ := hθ.differentiable (by simp)
  have hθ1 : Continuous (fderiv ℝ θ) := hθ.continuous_fderiv (by simp)
  have hθ2 : Continuous (fderiv ℝ (fderiv ℝ θ)) :=
    (hθ.fderiv_right (m := 1) (by simp)).continuous_fderiv (by simp)
  have hθ1d : Differentiable ℝ (fderiv ℝ θ) :=
    (hθ.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  -- the function vanishes identically near points of `V`
  set g : ℝ → E → ℝ := fun t x => θ x * f t x with hg
  have hgV : ∀ t, ∀ x ∈ V, g t =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    intro t x hx
    filter_upwards [hθV x hx] with y hy
    simp [hg, hy]
  have hfdV : ∀ t, ∀ x ∈ V, fderiv ℝ (g t) =ᶠ[𝓝 x] fun _ => (0 : E →L[ℝ] ℝ) := by
    intro t x hx
    filter_upwards [hV.mem_nhds hx] with y hy
    exact ((hgV t y hy).fderiv_eq).trans (by simp)
  -- the formulas on `U`
  set D1 : ℝ → E → (E →L[ℝ] ℝ) := fun t y => θ y • fderiv ℝ (f t) y + f t y • fderiv ℝ θ y with hD1
  have hfd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ U, fderiv ℝ (g t) y = D1 t y := by
    intro t ht y hy
    have h1 := (hf.hasFDerivAt t ht y hy).differentiableAt
    show fderiv ℝ (fun x => θ x * f t x) y = θ y • fderiv ℝ (f t) y + f t y • fderiv ℝ θ y
    exact fderiv_mul (𝕜 := ℝ) (hθd y) h1
  set D2 : ℝ → E → (E →L[ℝ] E →L[ℝ] ℝ) := fun t y =>
    θ y • fderiv ℝ (fderiv ℝ (f t)) y + (fderiv ℝ θ y).smulRight (fderiv ℝ (f t) y) +
      (f t y • fderiv ℝ (fderiv ℝ θ) y + (fderiv ℝ (f t) y).smulRight (fderiv ℝ θ y)) with hD2
  have hD1d : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ U, HasFDerivAt (D1 t) (D2 t y) y := by
    intro t ht y hy
    have a1 := (hθd y).hasFDerivAt.smul (hf.hasFDerivAt_fderiv t ht y hy)
    have a2 := (hf.hasFDerivAt t ht y hy).smul (hθ1d y).hasFDerivAt
    exact a1.add a2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cont
    refine r26t8a_o05b1_cont_local (fun p : ℝ × E => g p.1 p.2) T U V hU hV hcover ?_ ?_
    · have h1 : ContinuousOn (fun p : ℝ × E => θ p.2) (Set.Icc 0 T ×ˢ U) :=
        (hθ.continuous.comp continuous_snd).continuousOn
      exact h1.mul hf.cont
    · refine (continuousOn_const (c := (0 : ℝ))).congr ?_
      intro p hp
      simp [hg, hθ0 p.2 hp]
  · -- hasFDerivAt
    intro t ht x _
    rcases hcover x with hx | hx
    · exact ((hθd x).mul (hf.hasFDerivAt t ht x hx).differentiableAt).hasFDerivAt
    · exact (((hgV t x hx).differentiableAt_iff).2 (differentiableAt_const _)).hasFDerivAt
  · -- hasFDerivAt_fderiv
    intro t ht x _
    rcases hcover x with hx | hx
    · have hev : fderiv ℝ (g t) =ᶠ[𝓝 x] D1 t := by
        filter_upwards [hU.mem_nhds hx] with y hy using hfd t ht y hy
      exact ((hD1d t ht x hx).congr_of_eventuallyEq hev).differentiableAt.hasFDerivAt
    · exact (((hfdV t x hx).differentiableAt_iff).2 (differentiableAt_const _)).hasFDerivAt
  · -- cont_fderiv
    refine r26t8a_o05b1_cont_local (fun p : ℝ × E => fderiv ℝ (g p.1) p.2) T U V hU hV hcover ?_ ?_
    · have hc : ContinuousOn (fun p : ℝ × E => D1 p.1 p.2) (Set.Icc 0 T ×ˢ U) := by
        have h1 : ContinuousOn (fun p : ℝ × E => θ p.2) (Set.Icc 0 T ×ˢ U) :=
          (hθ.continuous.comp continuous_snd).continuousOn
        have h2 : ContinuousOn (fun p : ℝ × E => fderiv ℝ θ p.2) (Set.Icc 0 T ×ˢ U) :=
          (hθ1.comp continuous_snd).continuousOn
        exact (h1.smul hf.cont_fderiv).add (hf.cont.smul h2)
      refine hc.congr fun p hp => ?_
      exact hfd p.1 hp.1 p.2 hp.2
    · refine (continuousOn_const (c := (0 : E →L[ℝ] ℝ))).congr ?_
      intro p hp
      simp only
      exact ((hgV p.1 p.2 hp).fderiv_eq).trans (by simp)
  · -- cont_fderiv₂
    refine r26t8a_o05b1_cont_local (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (g p.1)) p.2) T U V hU hV hcover ?_ ?_
    · have hc : ContinuousOn (fun p : ℝ × E => D2 p.1 p.2) (Set.Icc 0 T ×ˢ U) := by
        have h1 : ContinuousOn (fun p : ℝ × E => θ p.2) (Set.Icc 0 T ×ˢ U) :=
          (hθ.continuous.comp continuous_snd).continuousOn
        have h2 : ContinuousOn (fun p : ℝ × E => fderiv ℝ θ p.2) (Set.Icc 0 T ×ˢ U) :=
          (hθ1.comp continuous_snd).continuousOn
        have h3 : ContinuousOn (fun p : ℝ × E => fderiv ℝ (fderiv ℝ θ) p.2) (Set.Icc 0 T ×ˢ U) :=
          (hθ2.comp continuous_snd).continuousOn
        have sR : ∀ {A B : ℝ × E → (E →L[ℝ] ℝ)} {s : Set (ℝ × E)}, ContinuousOn A s → ContinuousOn B s →
            ContinuousOn (fun p => (A p).smulRight (B p)) s := by
          intro A B s hA hB
          have hL := (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.comp_continuousOn hA
          refine (hL.clm_apply hB).congr fun p _ => ?_
          ext x
          simp
        exact ((h1.smul hf.cont_fderiv₂).add (sR h2 hf.cont_fderiv)).add
          ((hf.cont.smul h3).add (sR hf.cont_fderiv h2))
      refine hc.congr fun p hp => ?_
      have hev : fderiv ℝ (g p.1) =ᶠ[𝓝 p.2] D1 p.1 := by
        filter_upwards [hU.mem_nhds hp.2] with y hy using hfd p.1 hp.1 y hy
      simp only
      rw [hev.fderiv_eq]
      exact (hD1d p.1 hp.1 p.2 hp.2).fderiv
    · refine (continuousOn_const (c := (0 : E →L[ℝ] E →L[ℝ] ℝ))).congr ?_
      intro p hp
      simp only
      exact ((hfdV p.1 p.2 hp).fderiv_eq).trans (by simp)
  · -- hasDerivWithinAt
    intro x _ t ht
    rcases hcover x with hx | hx
    · exact (((hf.hasDerivWithinAt x hx t ht).const_mul (θ x)).differentiableWithinAt).hasDerivWithinAt
    · have : (fun r => g r x) = fun _ => (0 : ℝ) := by
        funext r; simp [hg, hθ0 x hx]
      rw [this]
      exact (differentiableWithinAt_const (0 : ℝ)).hasDerivWithinAt
  · -- cont_deriv
    refine r26t8a_o05b1_cont_local
      (fun p : ℝ × E => derivWithin (fun r => g r p.2) (Set.Icc 0 T) p.1) T U V hU hV hcover ?_ ?_
    · have h1 : ContinuousOn (fun p : ℝ × E => θ p.2) (Set.Icc 0 T ×ˢ U) :=
        (hθ.continuous.comp continuous_snd).continuousOn
      refine (h1.mul hf.cont_deriv).congr fun p hp => ?_
      by_cases hu : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) T) p.1
      · exact (((hf.hasDerivWithinAt p.2 hp.2 p.1 hp.1).const_mul (θ p.2)).derivWithin hu)
      · rw [derivWithin_zero_of_not_uniqueDiffWithinAt hu]
        simp [hg, derivWithin_zero_of_not_uniqueDiffWithinAt hu]
    · refine (continuousOn_const (c := (0 : ℝ))).congr ?_
      intro p hp
      simp only
      have : (fun r => g r p.2) = fun _ => (0 : ℝ) := by
        funext r; simp [hg, hθ0 p.2 hp]
      rw [this]
      simp

end HRS.MS.R26T8A

end
