import HRS.PDE.TorusFPExistAux1

/-!
# D1 existence, helper 2: backward maximum principle for classical solutions
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {n : ℕ}

/-- First and second order conditions at a global minimum of a `C²` function on the torus. -/
theorem d1_torus_min_grad_laplacian {f : Torus n → ℝ} (hf : Torus.IsCk 2 f) {x0 : Torus n}
    (hmin : ∀ x, f x0 ≤ f x) : Torus.grad f x0 = 0 ∧ 0 ≤ Torus.laplacian f x0 := by
  have hF : ContDiff ℝ 2 (Torus.lift f) := by
    have : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (Torus.lift f) := hf
    simpa using this
  have hloc : IsLocalMin (Torus.lift f) (Torus.rep x0) := by
    refine Filter.Eventually.of_forall fun y => ?_
    have h := hmin (Torus.mk y)
    simpa [Torus.lift, Torus.mk_rep] using h
  constructor
  · have h0 : fderiv ℝ (Torus.lift f) (Torus.rep x0) = 0 := hloc.fderiv_eq_zero
    simp [Torus.grad, gradient, h0]
  · have h := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (Torus.lift f)
      (EuclideanSpace.basisFun (Fin n) ℝ)) (Torus.rep x0)
    unfold Torus.laplacian
    rw [h]
    refine Finset.sum_nonneg fun i _ => ?_
    rw [iteratedFDeriv_two_apply]
    simpa using d1_secondDeriv_nonneg hF hloc (EuclideanSpace.basisFun (Fin n) ℝ i)


theorem d1_isOpenQuotientMap_mk : IsOpenQuotientMap (Torus.mk : Euc n → Torus n) := by
  have h1 : IsOpenQuotientMap
      (Pi.map (fun _ : Fin n => ((↑) : ℝ → UnitAddCircle))) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  have h2 := h1.comp (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isOpenQuotientMap
  exact h2

/-- Continuity of a function on `X × 𝕋^n` can be checked on the covering space. -/
theorem d1_continuous_prod_of_lift {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    {h : X × Torus n → Z} (H : Continuous fun p : X × Euc n => h (p.1, Torus.mk p.2)) :
    Continuous h := by
  have hq : IsOpenQuotientMap (Prod.map (id : X → X) (Torus.mk : Euc n → Torus n)) :=
    IsOpenQuotientMap.id.prodMap d1_isOpenQuotientMap_mk
  exact hq.isQuotientMap.continuous_iff.2 H

theorem D1BackwardSolution.continuous_lift {κ : ℝ} {b : Torus n → Euc n} {t : ℝ} {φ : Torus n → ℝ}
    {f : ℝ → Torus n → ℝ} (h : D1BackwardSolution κ b t φ f) :
    Continuous fun p : Set.Icc (0 : ℝ) t × Euc n => f p.1 (Torus.mk p.2) := by
  have h0 := (continuousMultilinearCurryFin0 ℝ (Euc n) ℝ).continuous.comp (h.cont_c2 0 (by norm_num))
  refine h0.congr fun p => ?_
  simp [iteratedFDeriv_zero_eq_comp, Torus.lift]

theorem D1BackwardSolution.continuous_joint {κ : ℝ} {b : Torus n → Euc n} {t : ℝ} {φ : Torus n → ℝ}
    {f : ℝ → Torus n → ℝ} (h : D1BackwardSolution κ b t φ f) :
    Continuous fun p : Set.Icc (0 : ℝ) t × Torus n => f p.1 p.2 :=
  d1_continuous_prod_of_lift (h := fun p : Set.Icc (0 : ℝ) t × Torus n => f p.1 p.2) h.continuous_lift

/-- **Backward maximum principle** for classical solutions: nonnegative terminal datum gives a
nonnegative solution. -/
theorem d1_backward_nonneg {κ : ℝ} (hκ : 0 < κ) {b : Torus n → Euc n} {t : ℝ} (ht : 0 < t)
    {φ : Torus n → ℝ} {f : ℝ → Torus n → ℝ} (hf : D1BackwardSolution κ b t φ f)
    (hφ : ∀ x, 0 ≤ φ x) : ∀ r ∈ Set.Icc 0 t, ∀ x, 0 ≤ f r x := by
  have hC := hf.isC12Test
  have hcont := hf.continuous_joint
  have key : ∀ ε : ℝ, 0 < ε → ∀ r ∈ Set.Icc 0 t, ∀ x, 0 ≤ f r x + ε * (t - r) := by
    intro ε hε
    set G : Set.Icc (0 : ℝ) t × Torus n → ℝ := fun p => f p.1 p.2 + ε * (t - p.1) with hG
    have hGc : Continuous G := hcont.add (continuous_const.mul
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)))
    have hne : (Set.univ : Set (Set.Icc (0 : ℝ) t × Torus n)).Nonempty :=
      ⟨(⟨0, le_rfl, ht.le⟩, 0), Set.mem_univ _⟩
    obtain ⟨p0, -, hp0⟩ := (isCompact_univ (X := Set.Icc (0 : ℝ) t × Torus n)).exists_isMinOn
      hne hGc.continuousOn
    have hmin : ∀ p, G p0 ≤ G p := fun p => hp0 (Set.mem_univ p)
    obtain ⟨⟨r0, hr0⟩, x0⟩ := p0
    rcases hr0.2.eq_or_lt with hrt | hrt
    · -- minimum at the terminal time
      have hG0 : 0 ≤ G (⟨r0, hr0⟩, x0) := by
        simp only [hG]
        rw [hrt, hf.terminal]
        have := hφ x0
        simpa using this
      intro r hr x
      exact hG0.trans (hmin (⟨r, hr⟩, x))
    · exfalso
      -- spatial conditions
      have hspace : ∀ x, f r0 x0 ≤ f r0 x := by
        intro x
        have := hmin (⟨r0, hr0⟩, x)
        simp only [hG] at this
        linarith
      obtain ⟨hgrad, hlap⟩ := d1_torus_min_grad_laplacian (hf.c2 r0 hr0) hspace
      -- time condition
      have hder := hC.hasDerivWithinAt_Icc ht x0 hr0
      have hder2 : HasDerivWithinAt (fun r => f r x0 + ε * (t - r))
          (-(d1_gen κ b (f r0) x0) + -ε) (Set.Icc 0 t) r0 := by
        have h1 : HasDerivWithinAt (fun r : ℝ => ε * (t - r)) (-ε) (Set.Icc 0 t) r0 := by
          have := (((hasDerivAt_id r0).const_sub t).const_mul ε).hasDerivWithinAt (s := Set.Icc 0 t)
          simpa using this
        exact hder.add h1
      have hlmin : IsLocalMinOn (fun r => f r x0 + ε * (t - r)) (Set.Icc 0 t) r0 := by
        refine eventually_nhdsWithin_of_forall fun r hr => ?_
        have := hmin (⟨r, hr⟩, x0)
        simpa [hG] using this
      have hseg : t - r0 ∈ posTangentConeAt (Set.Icc 0 t) r0 := by
        refine mem_posTangentConeAt_of_segment_subset ?_
        rw [segment_eq_Icc (by linarith)]
        intro z hz
        exact ⟨by linarith [hz.1, hr0.1], by linarith [hz.2]⟩
      have hnn := hlmin.hasFDerivWithinAt_nonneg hder2.hasFDerivWithinAt hseg
      have hnn' : 0 ≤ (t - r0) * (-(d1_gen κ b (f r0) x0) + -ε) := by simpa using hnn
      have hd : 0 ≤ -(d1_gen κ b (f r0) x0) + -ε := by
        by_contra hc
        rw [not_le] at hc
        nlinarith [sub_pos.2 hrt, hnn']
      have hL : 0 ≤ d1_gen κ b (f r0) x0 := by
        unfold d1_gen
        rw [hgrad]
        simp only [inner_zero_right, add_zero]
        exact mul_nonneg hκ.le hlap
      linarith
  intro r hr x
  by_contra hneg
  rw [not_le] at hneg
  have hε : 0 < (-(f r x)) / (t + 1) := by
    apply div_pos (by linarith) (by linarith [ht])
  have := key _ hε r hr x
  have hrt : t - r ≤ t := by linarith [hr.1]
  have h2 : (-(f r x)) / (t + 1) * (t - r) ≤ (-(f r x)) / (t + 1) * t :=
    mul_le_mul_of_nonneg_left hrt hε.le
  have h3 : (-(f r x)) / (t + 1) * t < -(f r x) := by
    have : (-(f r x)) / (t + 1) * t = (-(f r x)) * (t / (t + 1)) := by ring
    rw [this]
    have h4 : t / (t + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    nlinarith
  linarith

end HRS
