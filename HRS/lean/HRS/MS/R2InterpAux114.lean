import HRS.MS.R2InterpAux110

/-!
# S10.2 (worker S10R), part 114 (packet M3g): joint measurability of the observed predicted path and of the drift densities in `(u,ζ)`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d}

theorem s102_orbJoint_meas {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f) :
    Measurable fun p : ℝ × Euc d => if p.1 ∈ Icc (0 : ℝ) t then f p.1 p.2 else 0 := by
  classical
  have hcont : ContinuousOn (fun p : ℝ × Euc d => f p.1 p.2) (Icc (0 : ℝ) t ×ˢ univ) := by
    rw [continuousOn_iff_continuous_restrict]
    have h0 := hf.cont_c2 0 (by norm_num)
    have h1 : Continuous fun p : Icc (0 : ℝ) t × Euc d => f p.1 p.2 := by
      have := (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp h0
      refine this.congr fun p => ?_
      simp
    have h2 : Continuous fun p : (Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d))) =>
        ((⟨p.1.1, (mem_prod.1 p.2).1⟩ : Icc (0 : ℝ) t), p.1.2) :=
      (continuous_subtype_val.fst.subtype_mk _).prodMk (continuous_subtype_val.snd)
    exact h1.comp h2
  have hset : MeasurableSet (Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d))) := measurableSet_Icc.prod MeasurableSet.univ
  have := ContinuousOn.measurable_piecewise (f := fun p : ℝ × Euc d => f p.1 p.2)
    (g := fun _ => (0 : ℝ)) (s := Icc (0 : ℝ) t ×ˢ univ) hcont continuousOn_const hset
  have e : (fun p : ℝ × Euc d => if p.1 ∈ Icc (0 : ℝ) t then f p.1 p.2 else 0) =
      Set.piecewise (Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d))) (fun p : ℝ × Euc d => f p.1 p.2) (fun _ => (0 : ℝ)) := by
    funext p
    simp only [Set.piecewise, mem_prod, mem_univ, and_true]
  rw [e]
  exact this

theorem s102_zf_orb_jmeas {N : ℕ} (hN : 0 < N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t)) {t : ℝ} (ht : 0 ≤ t)
    {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f)
    (hXjm : Measurable fun q : ℝ × Ω => X (min q.1 t).toNNReal q.2) :
    ∃ F : ℝ × Ω → ℝ, Measurable F ∧ ∀ u : ℝ, 0 ≤ u → ∀ ζ, s102_zf P X ζ (min u t) (f (min u t)) = F (u, ζ) := by
  classical
  set Gt : ℝ × Euc d → ℝ := fun p => if p.1 ∈ Icc (0 : ℝ) t then f p.1 p.2 else 0 with hGt
  have hGm : Measurable Gt := s102_orbJoint_meas hf
  set A : ℝ × Ω → ℝ := fun q => (N : ℝ)⁻¹ * ∑ k, Gt (min q.1 t, X (min q.1 t).toNNReal q.2 k) with hA
  have hAm : Measurable A := by
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
    exact hGm.comp ((measurable_fst.min measurable_const).prodMk ((measurable_pi_apply k).comp hXjm))
  set ct : ℝ → ℝ := fun u => ∫ ζ', A (u, ζ') ∂P with hc
  have hcm : Measurable ct := (hAm.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  refine ⟨fun q => Real.sqrt N * (A q - ct q.1), (hAm.sub (hcm.comp measurable_fst)).const_mul _, fun u hu ζ => ?_⟩
  have hv : min u t ∈ Icc (0 : ℝ) t := ⟨le_min hu ht, min_le_right _ _⟩
  obtain ⟨Bf, hBf⟩ : ∃ Bf : ℝ, ∀ x, |f (min u t) x| ≤ Bf := by
    obtain ⟨B, hB⟩ := hf.bdd 0 (Nat.zero_le _)
    refine ⟨B, fun x => ?_⟩
    have := hB _ hv x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hgm : Measurable (f (min u t)) := (hf.c2 _ hv).continuous.measurable
  have hXv : Measurable (X (min u t).toNNReal) := hXm _
  have hE := HRS.MS.S21.s21_E_pair_emp (Nat.succ_le_of_lt hN) P (X (min u t).toNNReal) hXv
    (P.map (X (min u t).toNNReal)) (by
      haveI : IsProbabilityMeasure (P.map (X (min u t).toNNReal)) := ⟨by
        rw [Measure.map_apply hXv MeasurableSet.univ]; simp⟩
      rfl) hgm hBf
  have hAeq : ∀ ζ', A (u, ζ') = HRS.Whole.pair (HRS.Whole.empirical (X (min u t).toNNReal ζ')) (f (min u t)) := by
    intro ζ'
    simp only [hA, hGt, if_pos hv]
    rw [HRS.Whole.pair_empirical hN]
  unfold s102_zf
  simp only [hc, hAeq, hE]

end HRS.MS.R2Interp

end
