import HRS.MS.S11Q3A1

/-!
# S11.3 / S11.4 (worker S11Q3), A2: reflection extension past `t = 0`

`s11q3_Half`: data of a space-time function `Q` on `[0,∞)` (right time derivative `d1` continuous on `[0,∞)`, two-sided for `t > 0`;
spatial derivatives `d2, d3` jointly continuous), with `Q` constant in `t ≤ 0` (clamped).  `s11q3_Half.reflect`: the reflection
`Q̃(t,z) = Q(t,z) + Q(0,z) - Q(-t,z)` is of class `s113q_C12` and agrees with `Q` for `t ≥ 0`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace HRS.MS.S11Q3

open HRS.MS.S113Q

section Half

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

structure s11q3_Half (Q d1 : ℝ → E → ℝ) (d2 : ℝ → E → E →L[ℝ] ℝ) (d3 : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ) : Prop where
  c0 : Continuous fun p : ℝ × E => Q p.1 p.2
  c1 : ContinuousOn (fun p : ℝ × E => d1 p.1 p.2) (Ici 0 ×ˢ univ)
  c2 : Continuous fun p : ℝ × E => d2 p.1 p.2
  c3 : Continuous fun p : ℝ × E => d3 p.1 p.2
  h1R : ∀ t, 0 ≤ t → ∀ z, HasDerivWithinAt (fun σ => Q σ z) (d1 t z) (Ici t) t
  h1A : ∀ t, 0 < t → ∀ z, HasDerivAt (fun σ => Q σ z) (d1 t z) t
  h2 : ∀ t z, HasFDerivAt (Q t) (d2 t z) z
  h3 : ∀ t z, HasFDerivAt (d2 t) (d3 t z) z
  clampQ : ∀ t, t ≤ 0 → Q t = Q 0

theorem s11q3_Half.reflect {Q d1 : ℝ → E → ℝ} {d2 : ℝ → E → E →L[ℝ] ℝ} {d3 : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ}
    (h : s11q3_Half Q d1 d2 d3) :
    ∃ (Qr : ℝ × E → ℝ), s113q_C12 Qr ∧ ∀ t, 0 ≤ t → ∀ z, Qr (t, z) = Q t z := by
  refine ⟨fun p => Q p.1 p.2 + (Q 0 p.2 + (-1 : ℝ) * Q (-p.1) p.2), ?_, fun t ht z => ?_⟩
  swap
  · simp only
    rw [h.clampQ (-t) (by linarith)]
    ring
  refine ⟨fun p => d1 (max p.1 0) p.2 + (d1 (max (-p.1) 0) p.2 + (-1 : ℝ) * d1 0 p.2),
    fun p => d2 p.1 p.2 + (d2 0 p.2 + (-1 : ℝ) • d2 (-p.1) p.2),
    fun p => d3 p.1 p.2 + (d3 0 p.2 + (-1 : ℝ) • d3 (-p.1) p.2), ?_⟩
  have hneg : Continuous fun p : ℝ × E => (-p.1, p.2) := continuous_neg.comp continuous_fst |>.prodMk continuous_snd
  have h0 : Continuous fun p : ℝ × E => ((0 : ℝ), p.2) := continuous_const.prodMk continuous_snd
  have hmax1 : Continuous fun p : ℝ × E => (max p.1 0, p.2) := (continuous_fst.max continuous_const).prodMk continuous_snd
  have hmax2 : Continuous fun p : ℝ × E => (max (-p.1) 0, p.2) :=
    ((continuous_neg.comp continuous_fst).max continuous_const).prodMk continuous_snd
  have mem1 : ∀ p : ℝ × E, (max p.1 0, p.2) ∈ Ici (0 : ℝ) ×ˢ (univ : Set E) := fun p => Set.mk_mem_prod (Set.mem_Ici.2 (le_max_right _ _)) (mem_univ _)
  have mem2 : ∀ p : ℝ × E, (max (-p.1) 0, p.2) ∈ Ici (0 : ℝ) ×ˢ (univ : Set E) := fun p => Set.mk_mem_prod (Set.mem_Ici.2 (le_max_right _ _)) (mem_univ _)
  have mem0 : ∀ p : ℝ × E, ((0 : ℝ), p.2) ∈ Ici (0 : ℝ) ×ˢ (univ : Set E) := fun p => Set.mk_mem_prod (Set.mem_Ici.2 le_rfl) (mem_univ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.c0.add (((h.c0.comp h0).add (continuous_const.mul (h.c0.comp hneg))))
  · exact (h.c1.comp_continuous hmax1 mem1).add (((h.c1.comp_continuous hmax2 mem2).add
      (continuous_const.mul (h.c1.comp_continuous h0 mem0))))
  · exact h.c2.add ((h.c2.comp h0).add ((h.c2.comp hneg).const_smul (-1 : ℝ)))
  · exact s11q3_cont_add2 h.c3 (s11q3_cont_add2 (h.c3.comp h0) ((h.c3.comp hneg).const_smul (-1 : ℝ)))
  · -- time derivative
    rintro ⟨t, z⟩
    simp only
    rcases lt_trichotomy t 0 with ht | ht | ht
    · -- t < 0
      have hd : HasDerivAt (fun σ : ℝ => Q (-σ) z) (-d1 (-t) z) t := by
        have := (h.h1A (-t) (by linarith) z).comp t (hasDerivAt_neg' (x := t))
        exact this.congr_deriv (by ring)
      have h2 : HasDerivAt (fun σ : ℝ => Q σ z + (Q 0 z + (-1 : ℝ) * Q (-σ) z)) (d1 (-t) z) t := by
        have h3 : HasDerivAt (fun σ : ℝ => Q σ z) 0 t := by
          have : (fun σ : ℝ => Q σ z) =ᶠ[𝓝 t] fun _ => Q 0 z := by
            filter_upwards [Iio_mem_nhds ht] with σ hσ
            rw [h.clampQ σ hσ.le]
          exact (hasDerivAt_const t (Q 0 z)).congr_of_eventuallyEq this
        have := h3.add ((hd.const_mul (-1 : ℝ)).const_add (Q 0 z))
        convert this using 1
        ring
      convert h2 using 1
      rw [max_eq_right ht.le, max_eq_left (by linarith)]
      ring
    · -- t = 0
      subst ht
      have hR : HasDerivWithinAt (fun σ : ℝ => Q σ z + (Q 0 z + (-1 : ℝ) * Q (-σ) z)) (d1 0 z) (Ici 0) 0 := by
        refine ((h.h1R 0 le_rfl z)).congr (fun σ hσ => ?_) (by simp)
        have : Q (-σ) z = Q 0 z := by rw [h.clampQ (-σ) (by simpa using hσ)]
        simp only [this]
        ring
      have hL : HasDerivWithinAt (fun σ : ℝ => Q σ z + (Q 0 z + (-1 : ℝ) * Q (-σ) z)) (d1 0 z) (Iic 0) 0 := by
        have hneg' : HasDerivWithinAt (fun σ : ℝ => -σ) (-1) (Iic 0) 0 :=
          (hasDerivAt_neg' (x := (0 : ℝ))).hasDerivWithinAt
        have hQ : HasDerivWithinAt (fun σ : ℝ => Q σ z) (d1 0 z) (Ici 0) (-(0 : ℝ)) := by
          simpa using h.h1R 0 le_rfl z
        have hc := hQ.scomp (0 : ℝ) hneg' (fun σ hσ => by simpa using hσ)
        have h3 : HasDerivWithinAt (fun σ : ℝ => Q 0 z + (Q 0 z + (-1 : ℝ) * Q (-σ) z)) (d1 0 z) (Iic 0) 0 := by
          have := ((hc.const_mul (-1 : ℝ)).const_add (Q 0 z)).const_add (Q 0 z)
          simpa using this
        refine h3.congr (fun σ hσ => ?_) (by simp)
        have : Q σ z = Q 0 z := by rw [h.clampQ σ hσ]
        simp only [this]
      have hU : HasDerivWithinAt (fun σ : ℝ => Q σ z + (Q 0 z + (-1 : ℝ) * Q (-σ) z)) (d1 0 z) (Ici 0 ∪ Iic 0) 0 :=
        hR.union hL
      have hUU : (Ici (0 : ℝ) ∪ Iic 0) = univ := by
        ext x
        simp
      rw [hUU, hasDerivWithinAt_univ] at hU
      convert hU using 1
      simp
    · -- t > 0
      have h2 : HasDerivAt (fun σ : ℝ => Q σ z + (Q 0 z + (-1 : ℝ) * Q (-σ) z)) (d1 t z) t := by
        have : (fun σ : ℝ => Q σ z + (Q 0 z + (-1 : ℝ) * Q (-σ) z)) =ᶠ[𝓝 t] fun σ => Q σ z := by
          filter_upwards [Ioi_mem_nhds ht] with σ hσ
          have : Q (-σ) z = Q 0 z := by rw [h.clampQ (-σ) (by linarith [hσ.out])]
          rw [this]
          ring
        exact (h.h1A t ht z).congr_of_eventuallyEq this
      convert h2 using 1
      rw [max_eq_left ht.le, max_eq_right (by linarith)]
      ring
  · rintro ⟨t, z⟩
    exact (h.h2 t z).add ((h.h2 0 z).add ((h.h2 (-t) z).const_mul (-1 : ℝ)))
  · rintro ⟨t, z⟩
    exact (h.h3 t z).add ((h.h3 0 z).add ((h.h3 (-t) z).const_smul (-1 : ℝ)))

end Half

end HRS.MS.S11Q3

end
