import HRS.MC.S7PIS1Path2
import HRS.MC.S7PIE

/-!
# Packet S1, `s7_PIS_drift_facts`: the drift increment is a genuine, additive, bounded-variation path

Proof of `HRS.MC.Sec7.PIPlan.s7_PIS_drift_facts` (statement copied verbatim).  Continuity and the bound are PI-E
(`s7_PI_E_drift_measure_proof`); the value formula is `pathAt (pathOf ..)`; additivity is the pointwise (in `t`) splitting of
the integral over `(a, a'' ∧ t]`, which needs the integrability of `u ↦ V^{t,u} b(u)` (measurability `pie_V_aesm`, bound
`pie_Vbound`); the bounded variation follows from `‖𝒟(s,s']‖ ≤ C ∫_{(s,s']} ‖b‖` by telescoping the partition sums.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIS1

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIDV

variable {d : ℕ}

/-- integrability of `u ↦ V^{t,u} b(u)` on `(a, c] ⊆ [0,t]` -/
lemma S7PIS1_intOn {J n₀ : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} {m : ℝ}
    (P : PIEData J D μ T m n₀) {CV : ℝ}
    (hCV : ∀ t ∈ Set.Ioc 0 T, ∀ u ∈ Set.Icc 0 t, ∀ F : NegSobolev d m, ‖Vprop D μ m t u F‖ ≤ CV * ‖F‖)
    {b : ℝ → NegSobolev d m} (hb : MemLp b 1 (volume.restrict (Set.Icc (0 : ℝ) T)))
    {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {a c : ℝ} (ha : 0 ≤ a) (hct : c ≤ t) :
    IntegrableOn (fun u => Vprop D μ m t u (b u)) (Set.Ioc a c) := by
  have hSt : Set.Ioc a c ⊆ Set.Icc 0 t := fun u hu => ⟨ha.trans hu.1.le, hu.2.trans hct⟩
  have hsubT : Set.Ioc a c ⊆ Set.Icc 0 T := hSt.trans (Set.Icc_subset_Icc_right ht.2)
  have hbI : Integrable (fun u => ‖b u‖) (volume.restrict (Set.Ioc a c)) :=
    ((hb.integrable le_rfl).mono_measure (Measure.restrict_mono hsubT le_rfl)).norm
  have hbS : AEStronglyMeasurable b (volume.restrict (Set.Ioc a c)) :=
    hb.aestronglyMeasurable.mono_measure (Measure.restrict_mono hsubT le_rfl)
  have hm := pie_V_aesm P ht measurableSet_Ioc hSt hbS
  exact Integrable.mono' (hbI.const_mul CV) hm
    (ae_restrict_of_forall_mem measurableSet_Ioc fun u hu => hCV t ht u (hSt hu) (b u))

/-- a bound on increments by a monotone function gives bounded variation -/
lemma S7PIS1_bv {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (Φ : ℝ → ℝ) (T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hΦ : MonotoneOn Φ (Set.Icc 0 T))
    (h : ∀ s s' : ℝ, s ∈ Set.Icc 0 T → s' ∈ Set.Icc 0 T → s ≤ s' → ‖f s' - f s‖ ≤ C * (Φ s' - Φ s)) :
    BoundedVariationOn f (Set.Icc 0 T) := by
  unfold BoundedVariationOn eVariationOn
  refine ne_of_lt (lt_of_le_of_lt (iSup_le fun p => ?_) (ENNReal.ofReal_lt_top (r := C * (Φ T - Φ 0))))
  obtain ⟨n, u, hmono, hu⟩ := p
  simp only
  have hstep : ∀ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) ≤
      ENNReal.ofReal (C * (Φ (u (i + 1)) - Φ (u i))) := by
    intro i _
    rw [edist_dist, dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal (h _ _ (hu i) (hu (i + 1)) (hmono (Nat.le_succ i)))
  refine (Finset.sum_le_sum hstep).trans ?_
  have hnn : ∀ i ∈ Finset.range n, 0 ≤ C * (Φ (u (i + 1)) - Φ (u i)) := fun i _ =>
    mul_nonneg hC (sub_nonneg.2 (hΦ (hu i) (hu (i + 1)) (hmono (Nat.le_succ i))))
  rw [← ENNReal.ofReal_sum_of_nonneg hnn, ← Finset.mul_sum, Finset.sum_range_sub (fun i => Φ (u i)) n]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC)
  have h1 : Φ (u n) ≤ Φ T := hΦ (hu n) ⟨hT, le_rfl⟩ (hu n).2
  have h2 : Φ 0 ≤ Φ (u 0) := hΦ ⟨le_rfl, hT⟩ (hu 0) (hu 0).1
  linarith

/-- **S3 (the drift increment is a genuine, additive, bounded-variation path)**. -/
theorem s7_PIS_drift_facts_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, ∀ b : ℝ → NegSobolev d m, MemLp b 1 (volume.restrict (Set.Icc (0 : ℝ) T)) →
      (∀ a a' : ℝ, 0 ≤ a → a ≤ a' → a' ≤ T → ∀ t ∈ Set.Icc (0 : ℝ) T,
        pathAt (driftInc R.D R.ρ m T b a a') t = ∫ u in Set.Ioc a (min a' t), Vprop R.D R.ρ m t u (b u)) ∧
      (∀ a a' a'' : ℝ, 0 ≤ a → a ≤ a' → a' ≤ a'' → a'' ≤ T →
        driftInc R.D R.ρ m T b a a' + driftInc R.D R.ρ m T b a' a'' = driftInc R.D R.ρ m T b a a'') ∧
      (∀ a a' : ℝ, 0 ≤ a → a ≤ a' → a' ≤ T →
        ‖driftInc R.D R.ρ m T b a a'‖ ≤ C * ∫ u in Set.Ioc a a', ‖b u‖) ∧
      driftInc R.D R.ρ m T b 0 0 = 0 ∧
      BoundedVariationOn (fun s => driftInc R.D R.ρ m T b 0 s) (Set.Icc 0 T) := by
  classical
  obtain ⟨C0, hC0⟩ := HRS.MC.Sec7.PIE.s7_PI_E_drift_measure_proof R m hm T hT
  obtain ⟨J, k, hk, hJ, hm0, hm1, H⟩ := S7PIS1_data R m hm T hT
  have P : PIEData J R.D R.ρ T m (k + 1) :=
    ⟨H, by omega, by omega, by push_cast; linarith, by push_cast; linarith⟩
  obtain ⟨CV, hCV0, hCV⟩ := pie_Vbound H m (k + 1) (by omega) (by omega) (by push_cast; linarith)
    (by push_cast; linarith)
  refine ⟨max C0 0, fun b hb => ?_⟩
  -- (a) the value formula
  have hA : ∀ a a' : ℝ, 0 ≤ a → a ≤ a' → a' ≤ T → ∀ t ∈ Set.Icc (0 : ℝ) T,
      pathAt (driftInc R.D R.ρ m T b a a') t = ∫ u in Set.Ioc a (min a' t), Vprop R.D R.ρ m t u (b u) := by
    intro a a' ha haa' ha'T t ht
    have hc := (hC0 b hb a a' ha haa' ha'T).1
    exact S7PIS1_pathAt_pathOf (fun t => ∫ u in Set.Ioc a (min a' t), Vprop R.D R.ρ m t u (b u)) hc ht
  -- the splitting of the integral
  have hI : ∀ a a' a'' : ℝ, 0 ≤ a → a ≤ a' → a' ≤ a'' → a'' ≤ T → ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∫ u in Set.Ioc a (min a' t), Vprop R.D R.ρ m t u (b u)) +
        (∫ u in Set.Ioc a' (min a'' t), Vprop R.D R.ρ m t u (b u)) =
      ∫ u in Set.Ioc a (min a'' t), Vprop R.D R.ρ m t u (b u) := by
    intro a a' a'' ha h1 h2 h3 t ht
    rcases ht.1.eq_or_lt with h0 | hpos
    · have ht0 : t = 0 := h0.symm
      subst ht0
      have e1 : Set.Ioc a (min a' 0) = ∅ := Set.Ioc_eq_empty (not_lt.2 ((min_le_right _ _).trans ha))
      have e2 : Set.Ioc a' (min a'' 0) = ∅ :=
        Set.Ioc_eq_empty (not_lt.2 ((min_le_right _ _).trans (ha.trans h1)))
      have e3 : Set.Ioc a (min a'' 0) = ∅ := Set.Ioc_eq_empty (not_lt.2 ((min_le_right _ _).trans ha))
      simp [e1, e2, e3]
    · have htI : t ∈ Set.Ioc 0 T := ⟨hpos, ht.2⟩
      rcases le_or_gt t a' with hta | hat
      · have e1 : min a' t = t := min_eq_right hta
        have e2 : min a'' t = t := min_eq_right (hta.trans h2)
        have e3 : Set.Ioc a' t = ∅ := Set.Ioc_eq_empty (not_lt.2 hta)
        rw [e1, e2, e3]; simp
      · have e1 : min a' t = a' := min_eq_left hat.le
        have hc : a' ≤ min a'' t := le_min h2 hat.le
        rw [e1, ← Set.Ioc_union_Ioc_eq_Ioc h1 hc]
        rw [setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
          (S7PIS1_intOn P hCV hb htI ha hat.le)
          (S7PIS1_intOn P hCV hb htI (ha.trans h1) (min_le_right _ _))]
  -- (b) additivity
  have hB : ∀ a a' a'' : ℝ, 0 ≤ a → a ≤ a' → a' ≤ a'' → a'' ≤ T →
      driftInc R.D R.ρ m T b a a' + driftInc R.D R.ρ m T b a' a'' = driftInc R.D R.ρ m T b a a'' := by
    intro a a' a'' ha h1 h2 h3
    apply ContinuousMap.ext
    intro t
    have e : ∀ x : PathSpace d m T, PathSpace.at' x t = pathAt x t.1 := fun x => (S7PIS1_pathAt_coe x t).symm
    show PathSpace.at' (driftInc R.D R.ρ m T b a a') t + PathSpace.at' (driftInc R.D R.ρ m T b a' a'') t =
      PathSpace.at' (driftInc R.D R.ρ m T b a a'') t
    rw [e, e, e, hA a a' ha h1 (h2.trans h3) t.1 t.2, hA a' a'' (ha.trans h1) h2 h3 t.1 t.2,
      hA a a'' ha (h1.trans h2) h3 t.1 t.2]
    exact hI a a' a'' ha h1 h2 h3 t.1 t.2
  -- (c) the bound
  have hCb : ∀ a a' : ℝ, 0 ≤ a → a ≤ a' → a' ≤ T →
      ‖driftInc R.D R.ρ m T b a a'‖ ≤ max C0 0 * ∫ u in Set.Ioc a a', ‖b u‖ := by
    intro a a' ha haa' ha'T
    refine (hC0 b hb a a' ha haa' ha'T).2.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (integral_nonneg fun u => norm_nonneg _)
  -- (d) the zero increment
  have hZ : driftInc R.D R.ρ m T b 0 0 = 0 := by
    apply ContinuousMap.ext
    intro t
    have e : PathSpace.at' (driftInc R.D R.ρ m T b 0 0) t = pathAt (driftInc R.D R.ρ m T b 0 0) t.1 :=
      (S7PIS1_pathAt_coe _ t).symm
    show PathSpace.at' (driftInc R.D R.ρ m T b 0 0) t = 0
    rw [e, hA 0 0 le_rfl le_rfl hT.le t.1 t.2]
    have : Set.Ioc (0 : ℝ) (min 0 t.1) = ∅ := Set.Ioc_eq_empty (not_lt.2 (min_le_left _ _))
    rw [this]; simp
  refine ⟨hA, hB, hCb, hZ, ?_⟩
  -- (e) bounded variation
  set Φ : ℝ → ℝ := fun s => ∫ u in Set.Ioc 0 s, ‖b u‖ with hΦdef
  have hbT : IntegrableOn (fun u => ‖b u‖) (Set.Icc 0 T) := (hb.integrable le_rfl).norm
  have hΦsplit : ∀ s s' : ℝ, s ∈ Set.Icc (0 : ℝ) T → s' ∈ Set.Icc (0 : ℝ) T → s ≤ s' →
      Φ s' = Φ s + ∫ u in Set.Ioc s s', ‖b u‖ := by
    intro s s' hs hs' hss'
    simp only [hΦdef]
    rw [← Set.Ioc_union_Ioc_eq_Ioc hs.1 hss', setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl)
      measurableSet_Ioc]
    · exact hbT.mono_set (fun u hu => ⟨hu.1.le, hu.2.trans hs.2⟩)
    · exact hbT.mono_set (fun u hu => ⟨(hs.1.trans hu.1.le), hu.2.trans hs'.2⟩)
  have hmono : MonotoneOn Φ (Set.Icc 0 T) := by
    intro s hs s' hs' hss'
    rw [hΦsplit s s' hs hs' hss']
    linarith [integral_nonneg (μ := volume.restrict (Set.Ioc s s')) (f := fun u => ‖b u‖) (fun u => norm_nonneg (b u))]
  refine S7PIS1_bv (fun s => driftInc R.D R.ρ m T b 0 s) Φ T (max C0 0) hT.le (le_max_right _ _) hmono ?_
  intro s s' hs hs' hss'
  have hadd := hB 0 s s' le_rfl hs.1 hss' hs'.2
  have hd : driftInc R.D R.ρ m T b 0 s' - driftInc R.D R.ρ m T b 0 s = driftInc R.D R.ρ m T b s s' := by
    rw [← hadd]; abel
  show ‖driftInc R.D R.ρ m T b 0 s' - driftInc R.D R.ρ m T b 0 s‖ ≤ max C0 0 * (Φ s' - Φ s)
  rw [hd, hΦsplit s s' hs hs' hss']
  have := hCb s s' hs.1 hss' hs'.2
  linarith

end HRS.MC.Sec7.S7PIS1

end
