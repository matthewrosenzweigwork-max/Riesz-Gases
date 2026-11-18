import HRS.MS.S111K2B04a
import HRS.MS.S111K2B04b
import HRS.MS.FixEqP3Aux15

/-!
# S11.1 continuation, B04 (part 3): continuity of `t ↦ η(F_t - F_t(0))`

`η` a bounded linear functional on `E_{r,P}` with finite dual norm, `F_t` a family of `C^{r+1}` functions with uniformly
bounded derivatives of orders `1..r+1`, bounded values, and pointwise continuous in `t`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K2

open HRS HRS.Whole HRS.MS.FixEq

variable {d : ℕ}

/-- `F t - F t 0`, the zero-mass normalisation. -/
def s111k2_g (F : ℝ → Euc d → ℝ) (t : ℝ) : Euc d → ℝ := fun x => F t x - F t 0

lemma s111k2_iteratedFDeriv_sub_const {f : Euc d → ℝ} {j : ℕ} (hf : ContDiff ℝ j f) (c : ℝ) (hj : j ≠ 0) (x : Euc d) :
    iteratedFDeriv ℝ j (fun y => f y - c) x = iteratedFDeriv ℝ j f x := by
  have h1 : (fun y => f y - c) = f + fun _ => -c := by funext y; simp [sub_eq_add_neg]
  rw [h1, iteratedFDeriv_add_apply hf.contDiffAt contDiffAt_const, iteratedFDeriv_const_of_ne hj]
  simp

lemma s111k2_g_props (r : ℕ) {Ft : Euc d → ℝ} (hF : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) Ft) {A : ℝ} (hA : 0 ≤ A)
    (hb : ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 → ∀ x, ‖iteratedFDeriv ℝ j Ft x‖ ≤ A) :
    ContDiff ℝ r (fun x => Ft x - Ft 0) ∧
      ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i (fun x => Ft x - Ft 0) x| ≤ A * (1 + ‖x‖) := by
  have hFr : ContDiff ℝ r Ft := hF.of_le (by exact_mod_cast Nat.le_succ r)
  refine ⟨hFr.sub contDiff_const, fun j hj i x => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have h0 : partialDeriv i (fun x => Ft x - Ft 0) x = Ft x - Ft 0 := by
      simp [partialDeriv, iteratedFDeriv_zero_apply]
    rw [h0]
    have hd : Differentiable ℝ Ft := hF.differentiable (by exact_mod_cast Nat.succ_ne_zero r)
    have hfd : ∀ y, ‖fderiv ℝ Ft y‖ ≤ A := by
      intro y
      have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := Ft) (x := y) (n := 0)
      rw [norm_iteratedFDeriv_zero] at h1
      rw [h1]; exact hb 1 le_rfl (by omega) y
    have := (convex_univ : Convex ℝ (Set.univ : Set (Euc d))).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hd y) (fun y _ => hfd y) (Set.mem_univ 0) (Set.mem_univ x)
    simp only [sub_zero] at this
    rw [← Real.norm_eq_abs]
    calc ‖Ft x - Ft 0‖ ≤ A * ‖x‖ := this
      _ ≤ A * (1 + ‖x‖) := by nlinarith [norm_nonneg x]
  · refine (s57p_abs_partialDeriv_le i _ x).trans ?_
    rw [s111k2_iteratedFDeriv_sub_const (hFr.of_le (by exact_mod_cast hj)) _ (by omega)]
    refine (hb j hj0 (by omega) x).trans ?_
    nlinarith [norm_nonneg x]

lemma s111k2_W_cont (P : ℝ) : Continuous (s57pW d P) := by
  unfold s57pW
  refine Continuous.rpow_const ?_ (fun x => Or.inl (s57p_jbracket_pos x).ne')
  unfold jbracket
  fun_prop

lemma s111k2_E_tendsto {r : ℕ} {P : ℝ} (hP : (d : ℝ) + 2 < 2 * P) (Δ : ℕ → Euc d → ℝ)
    (hΔ : ∀ n, ContDiff ℝ r (Δ n)) (C0 : ℝ)
    (hb : ∀ n, ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i (Δ n) x| ≤ C0 * (1 + ‖x‖))
    (hl : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, Tendsto (fun n => partialDeriv i (Δ n) x) atTop (𝓝 0)) :
    Tendsto (fun n => weightedSobolevE r P (Δ n)) atTop (𝓝 0) := by
  have hW := s111k2_Wlin_integrable (d := d) hP
  have hterm : ∀ j ≤ r, ∀ i : Fin j → Fin d,
      Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i (Δ n) x) ^ 2))
        atTop (𝓝 0) := by
    intro j hj i
    have hmeas : ∀ n, Measurable fun x => ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i (Δ n) x) ^ 2) := by
      intro n
      have h1 : Continuous (partialDeriv i (Δ n)) := (s57p_partialDeriv_contDiff (hΔ n) 0 (by omega) i).continuous
      have h2 : Continuous fun x : Euc d => jbracket x ^ (-2 * P) * (partialDeriv i (Δ n) x) ^ 2 :=
        (s111k2_W_cont P).mul (h1.pow 2)
      exact ENNReal.measurable_ofReal.comp h2.measurable
    have := tendsto_lintegral_of_dominated_convergence (μ := (volume : Measure (Euc d)))
      (F := fun n x => ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i (Δ n) x) ^ 2))
      (f := fun _ => 0) (fun x => ENNReal.ofReal (C0 ^ 2 * (s57pW d P x * (1 + ‖x‖) ^ 2))) hmeas
      (fun n => Filter.Eventually.of_forall fun x => by
        apply ENNReal.ofReal_le_ofReal
        have h2 : (partialDeriv i (Δ n) x) ^ 2 ≤ (C0 * (1 + ‖x‖)) ^ 2 := by
          have := hb n j hj i x
          exact sq_le_sq' (by linarith [abs_nonneg (partialDeriv i (Δ n) x), neg_abs_le (partialDeriv i (Δ n) x)])
            (le_trans (le_abs_self _) this)
        calc jbracket x ^ (-2 * P) * (partialDeriv i (Δ n) x) ^ 2 ≤ jbracket x ^ (-2 * P) * (C0 * (1 + ‖x‖)) ^ 2 :=
              mul_le_mul_of_nonneg_left h2 (Real.rpow_pos_of_pos (s57p_jbracket_pos x) _).le
          _ = C0 ^ 2 * (s57pW d P x * (1 + ‖x‖) ^ 2) := by unfold s57pW; ring)
      (ne_of_lt ((hW.const_mul (C0 ^ 2)).lintegral_lt_top))
      (Filter.Eventually.of_forall fun x => by
        have h1 := (hl j hj i x)
        have h2 : Tendsto (fun n => jbracket x ^ (-2 * P) * (partialDeriv i (Δ n) x) ^ 2) atTop (𝓝 0) := by
          simpa using (h1.pow 2).const_mul (jbracket x ^ (-2 * P))
        simpa using (ENNReal.tendsto_ofReal h2))
    simpa using this
  have hS : Tendsto (fun n => s57pS d r P (Δ n)) atTop (𝓝 0) := by
    unfold s57pS
    have : (0 : ℝ≥0∞) = ∑ j ∈ Finset.range (r + 1), ∑ _i : Fin j → Fin d, (0 : ℝ≥0∞) := by simp
    rw [this]
    refine tendsto_finsetSum _ fun j hj => tendsto_finsetSum _ fun i _ => ?_
    exact hterm j (by simpa [Nat.lt_succ_iff] using hj) i
  have := (ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0 |>.comp hS
  simpa [Function.comp_def, s57p_E_eq, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using this

lemma s111k2_pd_sub {j : ℕ} {f g : Euc d → ℝ} (hf : ContDiff ℝ j f) (hg : ContDiff ℝ j g) (i : Fin j → Fin d)
    (x : Euc d) : partialDeriv i (fun y => f y - g y) x = partialDeriv i f x - partialDeriv i g x := by
  unfold partialDeriv
  have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := j) hf.contDiffAt hg.contDiffAt (x := x)
  have e : (fun y => f y - g y) = f - g := rfl
  rw [e, this]; rfl

lemma s111k2_pd_g {j : ℕ} {Ft : Euc d → ℝ} (hF : ContDiff ℝ j Ft) (i : Fin j → Fin d) (x : Euc d) :
    partialDeriv i (fun y => Ft y - Ft 0) x =
      if j = 0 then Ft x - Ft 0 else partialDeriv i Ft x := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [partialDeriv, iteratedFDeriv_zero_apply]
  · rw [if_neg (by omega)]
    unfold partialDeriv
    rw [s111k2_iteratedFDeriv_sub_const hF _ (by omega)]

lemma s111k2_func_cont (r : ℕ) {P : ℝ} (hP : (d : ℝ) + 2 < 2 * P) {η : (Euc d → ℝ) → ℝ}
    (hη : IsBoundedLinearOnE r P η) (hdual : dualNormE r P η < ⊤) (I : Set ℝ) (F : ℝ → Euc d → ℝ)
    {L : ℝ} (hL0 : 0 ≤ L)
    (hF : ∀ t ∈ I, ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (F t))
    (hL : ∀ t ∈ I, ∀ j : ℕ, 1 ≤ j → j ≤ r + 1 → ∀ x, ‖iteratedFDeriv ℝ j (F t) x‖ ≤ L)
    (hB0 : ∀ t ∈ I, ∃ B0 : ℝ, ∀ x, |F t x| ≤ B0) (hc : ∀ x, ContinuousOn (fun t => F t x) I) :
    ContinuousOn (fun t => η (s111k2_g F t)) I := by
  have hP' : (d : ℝ) < 2 * P := by linarith
  have hpd := s111k2_cont_pd I F r L hL0 hF hL hc
  rw [continuousOn_iff_continuous_restrict]
  refine continuous_iff_seqContinuous.2 fun tn t₀ htn => ?_
  simp only [Set.restrict_apply, Function.comp_def]
  have hmem : ∀ n, (tn n : ℝ) ∈ I := fun n => (tn n).2
  have ht0 : (t₀ : ℝ) ∈ I := t₀.2
  have hFt : ∀ x, Tendsto (fun n => F (tn n) x) atTop (𝓝 (F t₀ x)) := fun x =>
    (((hc x).restrict.tendsto t₀).comp htn)
  have hpdt : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x,
      Tendsto (fun n => partialDeriv i (F (tn n)) x) atTop (𝓝 (partialDeriv i (F t₀) x)) := fun j hj i x =>
    (((hpd j hj i x).restrict.tendsto t₀).comp htn)
  choose! Bf hBf using hB0
  have hBf0 : ∀ t ∈ I, 0 ≤ Bf t := fun t ht => (abs_nonneg _).trans (hBf t ht 0)
  have hFr : ∀ t ∈ I, ContDiff ℝ r (F t) := fun t ht => (hF t ht).of_le (by exact_mod_cast Nat.le_succ r)
  have hgp : ∀ t ∈ I, ContDiff ℝ r (fun x => F t x - F t 0) ∧
      ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i (fun x => F t x - F t 0) x| ≤ L * (1 + ‖x‖) :=
    fun t ht => s111k2_g_props r (hF t ht) hL0 (hL t ht)
  -- derivative bounds for the dual lemma
  have hderiv0 : ∀ t ∈ I, ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (fun x => F t x - F t 0) x‖ ≤ 2 * Bf t + L := by
    intro t ht j hj x
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      have := hBf t ht x; have := hBf t ht 0
      have h1 : |F t x - F t 0| ≤ |F t x| + |F t 0| := abs_sub _ _
      linarith
    · rw [s111k2_iteratedFDeriv_sub_const (hFr t ht |>.of_le (by exact_mod_cast hj)) _ (by omega)]
      have := hL t ht j hj0 (by omega) x
      have := hBf0 t ht
      linarith
  have hderiv : ∀ n, ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (fun x => F (tn n) x - F (tn n) 0) x‖ ≤
      (2 * Bf (tn n) + L) + (2 * Bf t₀ + L) := fun n j hj x =>
    (hderiv0 _ (hmem n) j hj x).trans (by linarith [hBf0 _ ht0])
  have hderiv' : ∀ n, ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (fun x => F t₀ x - F t₀ 0) x‖ ≤
      (2 * Bf (tn n) + L) + (2 * Bf t₀ + L) := fun n j hj x =>
    (hderiv0 _ ht0 j hj x).trans (by linarith [hBf0 _ (hmem n)])
  set gn : ℕ → Euc d → ℝ := fun n => fun x => F (tn n) x - F (tn n) 0 with hgn
  set g0 : Euc d → ℝ := fun x => F t₀ x - F t₀ 0 with hg0
  set Δ : ℕ → Euc d → ℝ := fun n x => gn n x - g0 x with hΔ
  have hΔC : ∀ n, ContDiff ℝ r (Δ n) := fun n => (hgp _ (hmem n)).1.sub (hgp _ ht0).1
  have hetasub : ∀ n, η (Δ n) = η (gn n) - η g0 := fun n =>
    s57p_eta_sub hP' hη (hgp _ (hmem n)).1 (hgp _ ht0).1 (hderiv n) (hderiv' n)
  have hΔd : ∀ n, ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (Δ n) x‖ ≤ ((2 * Bf (tn n) + L) + (2 * Bf t₀ + L)) + ((2 * Bf (tn n) + L) + (2 * Bf t₀ + L)) := by
    intro n j hj x
    have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := j) ((hgp _ (hmem n)).1.of_le (by exact_mod_cast hj) |>.contDiffAt)
      ((hgp _ ht0).1.of_le (by exact_mod_cast hj) |>.contDiffAt) (x := x)
    have e : Δ n = gn n - g0 := rfl
    rw [e, this]
    exact (norm_sub_le _ _).trans (add_le_add (hderiv n j hj x) (hderiv' n j hj x))
  have hdb : ∀ n, ENNReal.ofReal |η (Δ n)| ≤ dualNormE r P η * weightedSobolevE r P (Δ n) := fun n =>
    s57p_dual_bound hP' hη (hΔC n) (hΔd n)
  have hEΔ : Tendsto (fun n => weightedSobolevE r P (Δ n)) atTop (𝓝 0) := by
    refine s111k2_E_tendsto hP Δ hΔC (L + L) (fun n j hj i x => ?_) (fun j hj i x => ?_)
    · rw [hΔ]
      simp only
      rw [s111k2_pd_sub ((hgp _ (hmem n)).1.of_le (by exact_mod_cast hj)) ((hgp _ ht0).1.of_le (by exact_mod_cast hj))]
      have a1 := (hgp _ (hmem n)).2 j hj i x
      have a2 := (hgp _ ht0).2 j hj i x
      have : (L + L) * (1 + ‖x‖) = L * (1 + ‖x‖) + L * (1 + ‖x‖) := by ring
      rw [this]
      exact (abs_sub _ _).trans (add_le_add a1 a2)
    · have hjC : ∀ t ∈ I, ContDiff ℝ j (F t) := fun t ht => (hFr t ht).of_le (by exact_mod_cast hj)
      have e : ∀ n, partialDeriv i (Δ n) x = partialDeriv i (gn n) x - partialDeriv i g0 x := fun n =>
        s111k2_pd_sub (f := gn n) (g := g0) ((hgp _ (hmem n)).1.of_le (by exact_mod_cast hj))
          ((hgp _ ht0).1.of_le (by exact_mod_cast hj)) i x
      have e1 : ∀ n, partialDeriv i (gn n) x =
          if j = 0 then F (tn n) x - F (tn n) 0 else partialDeriv i (F (tn n)) x := fun n =>
        s111k2_pd_g (hjC _ (hmem n)) i x
      have e0 : partialDeriv i g0 x = if j = 0 then F t₀ x - F t₀ 0 else partialDeriv i (F t₀) x :=
        s111k2_pd_g (hjC _ ht0) i x
      simp_rw [e, e1, e0]
      by_cases hj0 : j = 0
      · simp only [hj0, if_true]
        have := (hFt x).sub (hFt 0)
        simpa using this.sub_const (F t₀ x - F t₀ 0) |>.congr' (Eventually.of_forall fun n => rfl)
      · simp only [hj0, if_false]
        simpa using (hpdt j hj i x).sub_const (partialDeriv i (F t₀) x)
  -- conclude
  have h1 : Tendsto (fun n => dualNormE r P η * weightedSobolevE r P (Δ n)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul hEΔ (Or.inr hdual.ne)
    simpa using this
  have h2 : Tendsto (fun n => ENNReal.ofReal |η (Δ n)|) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun _ => bot_le) hdb
  have h3 : Tendsto (fun n => |η (Δ n)|) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h2
    simpa [Function.comp_def, ENNReal.toReal_ofReal (abs_nonneg _)] using this
  refine tendsto_iff_dist_tendsto_zero.2 ?_
  refine h3.congr fun n => ?_
  rw [Real.dist_eq]
  show |η (Δ n)| = |η (gn n) - η g0|
  rw [hetasub n]

end HRS.MS.S111K2
