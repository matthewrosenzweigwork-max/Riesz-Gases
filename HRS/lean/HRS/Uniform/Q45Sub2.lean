import HRS.Uniform.Q45Sub1

/-!
# Q45 (Lemma 3.20): the generator takes values in the closed span of the range of `j`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

open Classical

namespace HRS.Uniform.Q45

section Sub

variable {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma VEA_mem {T : ℝ} {S : EvolData H E} (hev : S.IsEvolution T) {t r : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (hr : r ∈ Set.Icc (0 : ℝ) t) (x : S.D) : S.VE t r (S.A r x) ∈ E0 S := by
  have hd := hev.deriv t ⟨ht.le, htT⟩ x r hr
  have h := deriv_mem_of_closed (E0_closed S) hd hr (fun y hy =>
    VE_invariant hev hy.1 hy.2 htT _ (j_mem_E0 S _)) (neBot_Icc ht hr)
  simpa using h

lemma A_mem {T : ℝ} (hT : 0 < T) {S : EvolData H E} (hev : S.IsEvolution T) {r : ℝ}
    (hr : r ∈ Set.Icc (0 : ℝ) T) (x : S.D) : S.A r x ∈ E0 S := by
  rcases hr.1.eq_or_lt with h0 | hpos
  · -- `r = 0`: limit of `V(t,0) A_0 x` as `t ↓ 0`
    have hr0 : r = 0 := h0.symm
    subst hr0
    have hmem : ∀ t : ℝ, 0 < t → t ≤ T → S.VE t 0 (S.A 0 x) ∈ E0 S := fun t ht htT =>
      VEA_mem hev ht htT ⟨le_rfl, ht.le⟩ x
    have hc := hev.cont_E (S.A 0 x)
    have hcw : ContinuousWithinAt (fun p : ℝ × ℝ => S.VE p.1 p.2 (S.A 0 x))
        {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} (0, 0) := hc (0, 0) ⟨le_rfl, le_rfl, hT.le⟩
    have hseq : Tendsto (fun n : ℕ => (T / ((n : ℝ) + 1), (0 : ℝ))) atTop
        (𝓝[{p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}] (0, 0)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h1 : Tendsto (fun n : ℕ => T / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          (tendsto_const_div_atTop_nhds_zero_nat T |>.comp (tendsto_add_atTop_nat 1)) |> fun h => by
            simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
        exact h1.prodMk_nhds tendsto_const_nhds
      · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        refine ⟨le_rfl, by simp only []; positivity, ?_⟩
        show T / ((n : ℝ) + 1) ≤ T
        rw [div_le_iff₀ hn]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hlim := hcw.tendsto.comp hseq
    have hself := hev.self_E 0 ⟨le_rfl, hT.le⟩
    have hlim' : Tendsto (fun n : ℕ => S.VE (T / ((n : ℝ) + 1)) 0 (S.A 0 x)) atTop (𝓝 (S.A 0 x)) := by
      have : S.VE 0 0 (S.A 0 x) = S.A 0 x := by rw [hself]; rfl
      simpa [Function.comp_def, this] using hlim
    refine (E0_closed S).mem_of_tendsto hlim' (Eventually.of_forall fun n => ?_)
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    refine hmem _ (by positivity) ?_
    rw [div_le_iff₀ hn]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · have h := VEA_mem hev hpos hr.2 ⟨hr.1, le_rfl⟩ x
    have hself := hev.self_E r hr
    simpa [hself] using h

end Sub

end HRS.Uniform.Q45
