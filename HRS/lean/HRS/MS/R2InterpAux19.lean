import HRS.MS.R2InterpAux18

/-!
# S10.2 (worker S102), part 19 (packet I4): `r2DriftInc` is a genuine additive path of bounded variation
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.FixEq

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}
  {b : ℝ → (Euc d → ℝ) → ℝ} {Mb : ℝ → ℝ}

theorem s102_g_continuousOn (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) (hT : 0 ≤ T) {a a' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') :
    ContinuousOn (fun t => s102_g C m b a a' t) (Icc 0 T) := by
  set KV := s102_KV d r Pw c with hKV
  have hKV0 : 0 ≤ KV := s102_KV_nonneg d r Pw c
  set I : ℝ := ∫ u in Icc 0 T, Mb u with hI
  have hH : ContinuousOn (fun t => s102_H Mb (min a' t)) (Icc 0 T) :=
    (s102_H_continuousOn hT hb.Mb_int).comp (continuous_const.min continuous_id).continuousOn
      (fun t ht => ⟨le_min ha' ht.1, (min_le_right _ _).trans ht.2⟩)
  intro t₀ ht₀
  have hdiff : ∀ t ∈ Icc (0 : ℝ) T, ‖s102_g C m b a a' t - s102_g C m b a a' t₀‖ ≤
      KV * (|t - t₀| * I + |s102_H Mb (min a' t) - s102_H Mb (min a' t₀)|) := by
    intro t ht
    rcases le_total t₀ t with h | h
    · have := s102_g_diff hP hD hlin hb ha ha' ht₀ ht h
      have hnn : 0 ≤ s102_H Mb (min a' t) - s102_H Mb (min a' t₀) := by
        rw [← s102_setIntegral_Mb (le_min ha' ht₀.1) (min_le_min le_rfl h)
          ((min_le_right _ _).trans ht.2) hb.Mb_int]
        exact setIntegral_nonneg measurableSet_Ioc (fun u _ => hb.Mb_nonneg u)
      rw [abs_of_nonneg (sub_nonneg.2 h), abs_of_nonneg hnn]
      exact this
    · have := s102_g_diff hP hD hlin hb ha ha' ht ht₀ h
      have hnn : 0 ≤ s102_H Mb (min a' t₀) - s102_H Mb (min a' t) := by
        rw [← s102_setIntegral_Mb (le_min ha' ht.1) (min_le_min le_rfl h)
          ((min_le_right _ _).trans ht₀.2) hb.Mb_int]
        exact setIntegral_nonneg measurableSet_Ioc (fun u _ => hb.Mb_nonneg u)
      rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.2 h), neg_sub, abs_sub_comm, abs_of_nonneg hnn]
      exact this
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Icc (fun u _ => hb.Mb_nonneg u)
  have hrhs : ContinuousWithinAt (fun t => KV * (|t - t₀| * I +
      |s102_H Mb (min a' t) - s102_H Mb (min a' t₀)|)) (Icc 0 T) t₀ := by
    have h1 : ContinuousWithinAt (fun t : ℝ => |t - t₀| * I) (Icc 0 T) t₀ := by fun_prop
    have h2 : ContinuousWithinAt (fun t => |s102_H Mb (min a' t) - s102_H Mb (min a' t₀)|) (Icc 0 T) t₀ :=
      ((hH t₀ ht₀).sub continuousWithinAt_const).abs
    exact (h1.add h2).const_mul KV
  have hr0 : KV * (|t₀ - t₀| * I + |s102_H Mb (min a' t₀) - s102_H Mb (min a' t₀)|) = 0 := by simp
  have hlim := hrhs.tendsto
  rw [hr0] at hlim
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun t => dist_nonneg) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [dist_eq_norm]
  exact hdiff t ht

theorem s102_driftInc_at (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) (hT : 0 ≤ T) {a a' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    r2PathAt (r2DriftInc C m T b a a') t = s102_g C m b a a' t :=
  s102_windowPathOf_at (f := fun t => ∫ u in Ioc a (min a' t), r2Vprop C m t u (b u))
    (s102_g_continuousOn hP hD hlin hb hT ha ha') ht

theorem s102_g_add (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) {a a' a'' t : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') (haa' : a' ≤ a'')
    (ht : t ∈ Icc (0 : ℝ) T) :
    s102_g C m b a a' t + s102_g C m b a' a'' t = s102_g C m b a a'' t := by
  unfold s102_g
  by_cases h : a' ≤ t
  · rw [min_eq_left h]
    have hq : a' ≤ min a'' t := le_min haa' h
    have hs1 : Ioc a a' ⊆ Icc 0 t := fun u hu => ⟨ha.trans hu.1.le, hu.2.trans h⟩
    have hs2 : Ioc a' (min a'' t) ⊆ Icc 0 t := fun u hu =>
      ⟨(ha.trans haa).trans hu.1.le, hu.2.trans (min_le_right _ _)⟩
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (s102_w_integrableOn hP hD hlin hb ht hs1 measurableSet_Ioc)
      (s102_w_integrableOn hP hD hlin hb ht hs2 measurableSet_Ioc), Set.Ioc_union_Ioc_eq_Ioc haa hq]
  · have h' : t ≤ a' := (not_le.1 h).le
    rw [min_eq_right h', min_eq_right (h'.trans haa'), Set.Ioc_eq_empty (not_lt.2 h')]
    simp

theorem s102_driftInc_add (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) (hT : 0 ≤ T) {a a' a'' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a')
    (haa' : a' ≤ a'') :
    r2DriftInc C m T b a a' + r2DriftInc C m T b a' a'' = r2DriftInc C m T b a a'' := by
  have ha' : 0 ≤ a' := ha.trans haa
  have ha'' : 0 ≤ a'' := ha'.trans haa'
  apply ContinuousMap.ext
  intro t
  have h1 := s102_driftInc_at hP hD hlin hb hT ha ha' t.2
  have h2 := s102_driftInc_at hP hD hlin hb hT ha' ha'' t.2
  have h3 := s102_driftInc_at hP hD hlin hb hT ha ha'' t.2
  rw [s102_r2PathAt_of_mem _ t.2] at h1 h2 h3
  have := s102_g_add hP hD hlin hb ha haa haa' t.2
  rw [← h1, ← h2, ← h3] at this
  exact this

theorem s102_driftInc_norm_le (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) (hT : 0 ≤ T) {a a' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') (ha'T : a' ≤ T) :
    ‖r2DriftInc C m T b a a'‖ ≤ s102_KV d r Pw c * ∫ u in Ioc a a', Mb u := by
  have ha' : 0 ≤ a' := ha.trans haa
  have hKV0 := s102_KV_nonneg d r Pw c
  refine (ContinuousMap.norm_le _ (mul_nonneg hKV0 (setIntegral_nonneg measurableSet_Ioc
    (fun u _ => hb.Mb_nonneg u)))).2 (fun t => ?_)
  have h1 := s102_driftInc_at hP hD hlin hb hT ha ha' t.2
  rw [s102_r2PathAt_of_mem _ t.2] at h1
  show ‖OscPath.at' (r2DriftInc C m T b a a') t‖ ≤ _
  rw [h1]
  refine (s102_g_norm_le hP hD hlin hb ha t.2).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hKV0
  exact setIntegral_mono_set (hb.Mb_int.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc ha ha'T)))
    (Filter.Eventually.of_forall fun u => hb.Mb_nonneg u)
    (Filter.Eventually.of_forall (Ioc_subset_Ioc_right (min_le_left _ _)))

/-- A path whose increments are dominated by those of a monotone function has bounded variation. -/
theorem s102_bv_of_increment {E : Type*} [NormedAddCommGroup E] {T : ℝ} (hT : 0 ≤ T) (F : ℝ → E) (Φ : ℝ → ℝ)
    (hΦ : MonotoneOn Φ (Icc 0 T))
    (h : ∀ s' s, s' ∈ Icc (0 : ℝ) T → s ∈ Icc (0 : ℝ) T → s' ≤ s → ‖F s - F s'‖ ≤ Φ s - Φ s') :
    BoundedVariationOn F (Icc 0 T) := by
  unfold BoundedVariationOn
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (Φ T - Φ 0)) ENNReal.ofReal_ne_top ?_
  unfold eVariationOn
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  have hstep : ∀ i, edist (F (u (i + 1))) (F (u i)) ≤ ENNReal.ofReal (Φ (u (i + 1)) - Φ (u i)) := by
    intro i
    rw [edist_dist, dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal (h _ _ (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
  calc ∑ i ∈ Finset.range n, edist (F (u (i + 1))) (F (u i))
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (Φ (u (i + 1)) - Φ (u i)) := Finset.sum_le_sum fun i _ => hstep i
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, (Φ (u (i + 1)) - Φ (u i))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _
        exact sub_nonneg.2 (hΦ (hus i) (hus (i + 1)) (hu (Nat.le_succ i)))
    _ = ENNReal.ofReal (Φ (u n) - Φ (u 0)) := by rw [Finset.sum_range_sub (fun i => Φ (u i))]
    _ ≤ ENNReal.ofReal (Φ T - Φ 0) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := hΦ (hus n) (⟨hT, le_rfl⟩ : T ∈ Icc (0 : ℝ) T) (hus n).2
        have h2 := hΦ (⟨le_rfl, hT⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) T) (hus 0) (hus 0).1
        linarith

theorem s102_driftInc_zero (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) (hT : 0 ≤ T) :
    r2DriftInc C m T b 0 0 = 0 := by
  apply ContinuousMap.ext
  intro t
  have h1 := s102_driftInc_at hP hD hlin hb hT le_rfl le_rfl t.2
  rw [s102_r2PathAt_of_mem _ t.2] at h1
  show OscPath.at' (r2DriftInc C m T b 0 0) t = 0
  rw [h1]
  unfold s102_g
  rw [min_eq_left t.2.1]
  simp

/-- The cumulative drift path has bounded variation on `[0,T]` and vanishes at `0`. -/
theorem s102_drift_bv (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) (hT : 0 ≤ T) :
    BoundedVariationOn (fun s => r2DriftInc C m T b 0 s) (Icc 0 T) ∧ r2DriftInc C m T b 0 0 = 0 := by
  refine ⟨?_, s102_driftInc_zero hP hD hlin hb hT⟩
  have hKV0 := s102_KV_nonneg d r Pw c
  refine s102_bv_of_increment hT _ (fun s => s102_KV d r Pw c * s102_H Mb s) ?_ ?_
  · intro s' hs' s hs hss
    have : s102_H Mb s' ≤ s102_H Mb s := by
      have := s102_setIntegral_Mb hs'.1 hss hs.2 hb.Mb_int
      have h0 : 0 ≤ ∫ u in Ioc s' s, Mb u := setIntegral_nonneg measurableSet_Ioc (fun u _ => hb.Mb_nonneg u)
      linarith
    exact mul_le_mul_of_nonneg_left this hKV0
  · intro s' s hs' hs hss
    have hadd := s102_driftInc_add hP hD hlin hb hT (a := 0) (a' := s') (a'' := s) le_rfl hs'.1 hss
    have hsub : r2DriftInc C m T b 0 s - r2DriftInc C m T b 0 s' = r2DriftInc C m T b s' s := by
      rw [← hadd]; abel
    rw [hsub]
    refine (s102_driftInc_norm_le hP hD hlin hb hT hs'.1 hss hs.2).trans (le_of_eq ?_)
    rw [s102_setIntegral_Mb hs'.1 hss hs.2 hb.Mb_int]; ring

end HRS.MS.R2Interp

end
