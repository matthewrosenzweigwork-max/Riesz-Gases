import HRS.MS.FixEqP1Aux1

/-!
# S11.1 continuation, B04 (part 2): continuity in a parameter of the partial derivatives

If `F t` is a family of `C^{n+1}` functions with uniformly bounded derivatives of orders `1..n+1`, and `t ↦ F t x` is continuous
for every `x`, then `t ↦ ∂^i (F t) (x)` is continuous for every index tuple of order `≤ n`.  Elementary proof:
the one-dimensional second-order Taylor bound makes the difference quotients converge uniformly in `t`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K2

open HRS HRS.Whole HRS.MS.FixEq

variable {d : ℕ}

lemma s111k2_taylor1d (ψ p p2 : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L) (hψ : ∀ s, HasDerivAt ψ (p s) s)
    (hp : ∀ s, HasDerivAt p (p2 s) s) (hb : ∀ s, |p2 s| ≤ L) {ε : ℝ} (hε : 0 < ε) :
    |ψ ε - ψ 0 - ε * p 0| ≤ L * ε ^ 2 := by
  have hlip : ∀ s, |p s - p 0| ≤ L * |s| := by
    intro s
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := p) (f' := p2) (s := Set.univ) (C := L)
      (fun x _ => (hp x).hasDerivWithinAt) (fun x _ => by simpa using hb x) convex_univ
      (Set.mem_univ 0) (Set.mem_univ s)
    simpa using this
  set w : ℝ → ℝ := fun s => ψ s - ψ 0 - s * p 0 with hw
  have hwd : ∀ s, HasDerivAt w (p s - p 0) s := by
    intro s
    have h1 := (hψ s).sub_const (ψ 0)
    have h2 := (hasDerivAt_id s).mul_const (p 0)
    exact (h1.sub h2).congr_deriv (by ring)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := w) (f' := fun s => p s - p 0)
    (s := Set.Icc 0 ε) (C := L * ε) (fun x _ => (hwd x).hasDerivWithinAt)
    (fun x hx => by
      rw [Real.norm_eq_abs]
      calc |p x - p 0| ≤ L * |x| := hlip x
        _ ≤ L * ε := by
          rw [abs_of_nonneg hx.1]; exact mul_le_mul_of_nonneg_left hx.2 hL)
    (convex_Icc 0 ε) (Set.left_mem_Icc.2 hε.le) (Set.right_mem_Icc.2 hε.le)
  have e0 : w 0 = 0 := by simp [hw]
  simp only [e0, sub_zero, Real.norm_eq_abs, abs_of_pos hε] at hmv
  have : w ε = ψ ε - ψ 0 - ε * p 0 := rfl
  rw [this] at hmv
  calc _ ≤ L * ε * ε := hmv
    _ = L * ε ^ 2 := by ring

lemma s111k2_cont_pd (I : Set ℝ) (F : ℝ → Euc d → ℝ) (n : ℕ) (L : ℝ) (hL0 : 0 ≤ L)
    (hF : ∀ t ∈ I, ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (F t))
    (hL : ∀ t ∈ I, ∀ j : ℕ, 1 ≤ j → j ≤ n + 1 → ∀ x, ‖iteratedFDeriv ℝ j (F t) x‖ ≤ L)
    (hc : ∀ x, ContinuousOn (fun t => F t x) I) :
    ∀ j : ℕ, j ≤ n → ∀ i : Fin j → Fin d, ∀ x, ContinuousOn (fun t => partialDeriv i (F t) x) I := by
  intro j
  induction j with
  | zero =>
    intro _ i x
    have : ∀ t, partialDeriv i (F t) x = F t x := by
      intro t; simp [partialDeriv, iteratedFDeriv_zero_apply]
    simp_rw [this]; exact hc x
  | succ j ih =>
    intro hj i x
    set k : Fin d := i 0 with hk
    set e : Euc d := EuclideanSpace.single k (1 : ℝ) with he
    set i' : Fin j → Fin d := fun l => i l.succ with hi'
    have hjn : j + 1 ≤ n := hj
    have hcast : ∀ a : ℕ, a ≤ n + 1 → ((a : ℕ) : WithTop ℕ∞) ≤ ((n + 1 : ℕ) : WithTop ℕ∞) := fun a ha => by
      exact_mod_cast ha
    have hline : ∀ (y : Euc d) (s : ℝ), HasDerivAt (fun s : ℝ => y + s • e) e s := by
      intro y s
      simpa using ((hasDerivAt_id s).smul_const e).const_add y
    -- Taylor bound for each `t`
    have htaylor : ∀ t ∈ I, ∀ ε : ℝ, 0 < ε →
        |partialDeriv i' (F t) (x + ε • e) - partialDeriv i' (F t) x - ε * partialDeriv i (F t) x| ≤ L * ε ^ 2 := by
      intro t ht ε hε
      have hF1 : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (F t) := (hF t ht).of_le (hcast _ (by omega))
      have hF2 : ContDiff ℝ ((j + 1 + 1 : ℕ) : WithTop ℕ∞) (F t) := (hF t ht).of_le (hcast _ (by omega))
      have hψC : ContDiff ℝ 1 (partialDeriv i' (F t)) :=
        s57p_partialDeriv_contDiff (hF t ht) 1 (by omega) i'
      have hpC : ContDiff ℝ 1 (partialDeriv i (F t)) :=
        s57p_partialDeriv_contDiff (hF t ht) 1 (by omega) i
      have hp_eq : ∀ y, partialDeriv i (F t) y = fderiv ℝ (partialDeriv i' (F t)) y e := fun y =>
        s57p_partialDeriv_succ hF1 i y
      have hp2_eq : ∀ y, fderiv ℝ (partialDeriv i (F t)) y e =
          partialDeriv (Fin.cons k i : Fin (j + 1 + 1) → Fin d) (F t) y := by
        intro y
        have := s57p_partialDeriv_succ hF2 (Fin.cons k i : Fin (j + 1 + 1) → Fin d) y
        simpa using this.symm
      refine s111k2_taylor1d (fun s => partialDeriv i' (F t) (x + s • e))
        (fun s => partialDeriv i (F t) (x + s • e))
        (fun s => partialDeriv (Fin.cons k i : Fin (j + 1 + 1) → Fin d) (F t) (x + s • e)) L hL0
        (fun s => ?_) (fun s => ?_) (fun s => ?_) hε |>.trans_eq' ?_
      · have := (hψC.differentiable one_ne_zero (x + s • e)).hasFDerivAt.comp_hasDerivAt s (hline x s)
        rw [hp_eq (x + s • e)]; exact this
      · have := (hpC.differentiable one_ne_zero (x + s • e)).hasFDerivAt.comp_hasDerivAt s (hline x s)
        rw [← hp2_eq (x + s • e)]; exact this
      · refine (s57p_abs_partialDeriv_le _ _ _).trans (hL t ht (j + 1 + 1) (by omega) (by omega) _)
      · simp
    intro t₀ ht₀
    rw [Metric.continuousWithinAt_iff]
    intro η hη
    set ε : ℝ := η / (4 * (L + 1)) with hε
    have hε0 : 0 < ε := by positivity
    have hih1 := (ih (by omega) i' (x + ε • e)) t₀ ht₀
    have hih2 := (ih (by omega) i' x) t₀ ht₀
    rw [Metric.continuousWithinAt_iff] at hih1 hih2
    obtain ⟨δ1, hδ1, h1⟩ := hih1 (ε * η / 4) (by positivity)
    obtain ⟨δ2, hδ2, h2⟩ := hih2 (ε * η / 4) (by positivity)
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun t ht hd => ?_⟩
    have hd1 : dist t t₀ < δ1 := lt_of_lt_of_le hd (min_le_left _ _)
    have hd2 : dist t t₀ < δ2 := lt_of_lt_of_le hd (min_le_right _ _)
    have e1 := h1 ht hd1
    have e2 := h2 ht hd2
    rw [Real.dist_eq] at e1 e2 ⊢
    have T1 := htaylor t ht ε hε0
    have T2 := htaylor t₀ ht₀ ε hε0
    set a1 := partialDeriv i' (F t) (x + ε • e)
    set a0 := partialDeriv i' (F t) x
    set b1 := partialDeriv i' (F t₀) (x + ε • e)
    set b0 := partialDeriv i' (F t₀) x
    set pt := partialDeriv i (F t) x
    set pt0 := partialDeriv i (F t₀) x
    -- ε (pt - pt0) = (a1 - a0 - (b1 - b0)) - (T-remainders)
    have hkey : ε * |pt - pt0| ≤ |a1 - b1| + |a0 - b0| + 2 * (L * ε ^ 2) := by
      have : ε * (pt - pt0) = -( (a1 - a0 - ε * pt) ) + (b1 - b0 - ε * pt0) * 1 + ((a1 - b1) - (a0 - b0)) := by ring
      calc ε * |pt - pt0| = |ε * (pt - pt0)| := by rw [abs_mul, abs_of_pos hε0]
        _ = |-( (a1 - a0 - ε * pt) ) + (b1 - b0 - ε * pt0) * 1 + ((a1 - b1) - (a0 - b0))| := by rw [this]
        _ ≤ |a1 - a0 - ε * pt| + |b1 - b0 - ε * pt0| + (|a1 - b1| + |a0 - b0|) := by
          refine (abs_add_le _ _).trans ?_
          refine add_le_add ((abs_add_le _ _).trans ?_) ((abs_sub _ _))
          rw [abs_neg, mul_one]
        _ ≤ _ := by linarith
    have hfin : |pt - pt0| < η := by
      have h3 : ε * |pt - pt0| < ε * η := by
        have : 2 * (L * ε ^ 2) ≤ ε * η / 2 := by
          have : L * ε ≤ η / 4 := by
            rw [hε]
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
          nlinarith
        nlinarith
      exact lt_of_mul_lt_mul_left h3 hε0.le
    exact hfin

end HRS.MS.S111K2
