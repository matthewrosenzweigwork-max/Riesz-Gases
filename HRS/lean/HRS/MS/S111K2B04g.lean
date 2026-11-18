import Mathlib

/-!
# S11.1 continuation, B04 (part 7): continuity and variation of an interval function from its interval bounds

If `D a b` is additive in the interval, with `‖D a b‖ ≤ ∫_{(a,b]} f` for an integrable `f`, then `v ↦ D 0 v` is continuous on `[0,H]`
and has variation at most `∫_{[0,H]} f`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MS.S111K2

lemma s111k2_sum_Ioc (f : ℝ → ℝ≥0∞) (u : ℕ → ℝ) (hu : Monotone u) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∫⁻ v in Ioc (u i) (u (i + 1)), f v = ∫⁻ v in Ioc (u 0) (u n), f v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, ← lintegral_union measurableSet_Ioc
      (Set.disjoint_left.2 fun x hx hx' => by linarith [hx.2, hx'.1]),
      Set.Ioc_union_Ioc_eq_Ioc (hu (Nat.zero_le n)) (hu (Nat.le_succ n))]

lemma s111k2_interval_bv {E : Type*} [NormedAddCommGroup E] (Dd : ℝ → ℝ → E) {H : ℝ} (f : ℝ → ℝ≥0∞)
    (hfin : ∫⁻ v in Icc 0 H, f v ≠ ⊤)
    (hadd : ∀ a b c, 0 ≤ a → a ≤ b → b ≤ c → c ≤ H → Dd a c = Dd a b + Dd b c)
    (hbd : ∀ a b, 0 ≤ a → a ≤ b → b ≤ H → ‖Dd a b‖ₑ ≤ ∫⁻ v in Ioc a b, f v) :
    ContinuousOn (fun v => Dd 0 v) (Icc 0 H) ∧
      eVariationOn (fun v => Dd 0 v) (Icc 0 H) ≤ ∫⁻ v in Icc 0 H, f v := by
  have hdiff : ∀ x y, x ∈ Icc 0 H → y ∈ Icc 0 H → x ≤ y →
      edist (Dd 0 y) (Dd 0 x) ≤ ∫⁻ v in Ioc x y, f v := by
    intro x y hx hy hxy
    have h := hadd 0 x y le_rfl hx.1 hxy hy.2
    rw [edist_eq_enorm_sub, h, add_sub_cancel_left]
    exact hbd x y hx.1 hxy hy.2
  refine ⟨?_, ?_⟩
  · intro x₀ hx₀
    rw [ContinuousWithinAt, tendsto_iff_edist_tendsto_0]
    set μ : Measure ℝ := volume.restrict (Icc 0 H) with hμ
    have h1 : Tendsto (fun x : ℝ => ENNReal.ofReal |x - x₀|) (𝓝[Icc 0 H] x₀) (𝓝 0) := by
      have hc : Continuous fun x : ℝ => |x - x₀| := by fun_prop
      have h2 := (hc.tendsto x₀).mono_left (nhdsWithin_le_nhds (s := Icc 0 H))
      have h3 := ENNReal.tendsto_ofReal h2
      simpa using h3
    have hmeas : Tendsto (μ ∘ fun x : ℝ => Ioc (min x x₀) (max x x₀)) (𝓝[Icc 0 H] x₀) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => bot_le) (fun x => ?_)
      simp only [Function.comp]
      refine ((Measure.restrict_le_self : μ ≤ volume) _).trans (le_of_eq ?_)
      rw [Real.volume_Ioc]
      congr 1
      rcases le_total x x₀ with h | h
      · rw [min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]
    have hs := tendsto_setLIntegral_zero (μ := μ) (f := f) hfin hmeas
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hsub : Ioc (min x x₀) (max x x₀) ⊆ Icc 0 H := fun v hv =>
      ⟨le_trans (le_min hx.1 hx₀.1) hv.1.le, hv.2.trans (max_le hx.2 hx₀.2)⟩
    rw [hμ, Measure.restrict_restrict measurableSet_Ioc, Set.inter_eq_left.2 hsub]
    rcases le_total x x₀ with h | h
    · rw [edist_comm, min_eq_left h, max_eq_right h]
      exact hdiff x x₀ hx hx₀ h
    · rw [min_eq_right h, max_eq_left h]
      exact hdiff x₀ x hx₀ hx h
  · unfold eVariationOn
    refine iSup_le fun p => ?_
    obtain ⟨n, u, hu, hmem⟩ := p
    calc ∑ i ∈ Finset.range n, edist (Dd 0 (u (i + 1))) (Dd 0 (u i))
        ≤ ∑ i ∈ Finset.range n, ∫⁻ v in Ioc (u i) (u (i + 1)), f v :=
          Finset.sum_le_sum fun i _ => hdiff (u i) (u (i + 1)) (hmem i) (hmem (i + 1)) (hu (Nat.le_succ i))
      _ = ∫⁻ v in Ioc (u 0) (u n), f v := s111k2_sum_Ioc f u hu n
      _ ≤ ∫⁻ v in Icc 0 H, f v :=
          lintegral_mono_set (fun v hv => ⟨(hmem 0).1.trans hv.1.le, hv.2.trans (hmem n).2⟩)

end HRS.MS.S111K2
