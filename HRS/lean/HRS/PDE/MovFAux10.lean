import HRS.PDE.MovFAux9

/-!
# MOVF Aux10: junk elimination for the weak formulation

`movf_primitive_measurable`: the Bochner "indefinite integral" `t ↦ ∫_{[0,t]} A` of a bounded function is Borel
measurable, whether or not `A` is measurable (it is `0` where `A` is not integrable, Lipschitz where it is).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movf_primitive_measurable {T B : ℝ} (A : ℝ → ℝ) (hA : ∀ r ∈ Set.Icc (0 : ℝ) T, |A r| ≤ B) :
    Measurable (fun t : Set.Icc (0 : ℝ) T => ∫ r in Set.Icc (0 : ℝ) t.1, A r) := by
  classical
  set S : Set (Set.Icc (0 : ℝ) T) := {t | IntegrableOn A (Set.Icc (0 : ℝ) t.1)} with hSdef
  have hSoc : S.OrdConnected := by
    refine ⟨fun a ha b hb x hx => ?_⟩
    have : IntegrableOn A (Set.Icc (0 : ℝ) b.1) := hb
    exact this.mono_set (Set.Icc_subset_Icc le_rfl (Subtype.coe_le_coe.2 hx.2))
  have hS : MeasurableSet S := hSoc.measurableSet
  set J : Set.Icc (0 : ℝ) T → ℝ := fun t => ∫ r in Set.Icc (0 : ℝ) t.1, A r with hJ
  have hLip : LipschitzOnWith (B.toNNReal) J S := by
    refine LipschitzOnWith.of_dist_le_mul fun s hs t ht => ?_
    wlog hst : s ≤ t generalizing s t
    · rw [dist_comm s t, dist_comm (J s) (J t)]
      exact this t ht s hs (le_of_not_ge hst)
    have hs' : IntegrableOn A (Set.Icc (0 : ℝ) s.1) := hs
    have ht' : IntegrableOn A (Set.Icc (0 : ℝ) t.1) := ht
    have hst' : s.1 ≤ t.1 := hst
    have hunion : Set.Icc (0 : ℝ) t.1 = Set.Icc (0 : ℝ) s.1 ∪ Set.Ioc s.1 t.1 := by
      ext x
      simp only [Set.mem_Icc, Set.mem_union, Set.mem_Ioc]
      constructor
      · rintro ⟨h0, h1⟩
        by_cases hx : x ≤ s.1
        · exact Or.inl ⟨h0, hx⟩
        · exact Or.inr ⟨not_le.1 hx, h1⟩
      · rintro (⟨h0, h1⟩ | ⟨h0, h1⟩)
        · exact ⟨h0, h1.trans hst'⟩
        · exact ⟨s.2.1.trans h0.le, h1⟩
    have hdisj : Disjoint (Set.Icc (0 : ℝ) s.1) (Set.Ioc s.1 t.1) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx.2 (not_le.2 hx'.1)
    have hI2 : IntegrableOn A (Set.Ioc s.1 t.1) := ht'.mono_set (by rw [hunion]; exact Set.subset_union_right)
    have hsum : J t = J s + ∫ r in Set.Ioc s.1 t.1, A r := by
      simp only [hJ]
      rw [hunion, setIntegral_union hdisj measurableSet_Ioc hs' hI2]
    have hb : ‖∫ r in Set.Ioc s.1 t.1, A r‖ ≤ B * (t.1 - s.1) := by
      have := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure ℝ)) (s := Set.Ioc s.1 t.1)
        (f := A) (C := B) (by simp) (fun x hx => by
          rw [Real.norm_eq_abs]
          exact hA x ⟨s.2.1.trans hx.1.le, hx.2.trans t.2.2⟩)
      simpa [Real.volume_real_Ioc_of_le hst'] using this
    have hBn : 0 ≤ B := by
      have := hA 0 ⟨le_rfl, s.2.1.trans s.2.2⟩
      exact (abs_nonneg _).trans this
    rw [Real.dist_eq, hsum, Subtype.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hBn]
    have : |s.1 - t.1| = t.1 - s.1 := by rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.2 hst')
    rw [this]
    have e : J s - (J s + ∫ r in Set.Ioc s.1 t.1, A r) = -∫ r in Set.Ioc s.1 t.1, A r := by ring
    rw [e, abs_neg]
    simpa [Real.norm_eq_abs] using hb
  have hJS : ContinuousOn J S := hLip.continuousOn
  have hpw : J = S.piecewise J (fun _ => 0) := by
    funext t
    by_cases ht : t ∈ S
    · rw [Set.piecewise_eq_of_mem _ _ _ ht]
    · rw [Set.piecewise_eq_of_notMem _ _ _ ht]
      exact integral_undef ht
  show Measurable J
  rw [hpw]
  exact hJS.measurable_piecewise continuous_const.continuousOn hS

end HRS

end
