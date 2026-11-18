import HRS.MS.WadAux117

/-!
# S8.3, packet S8G-1: smoothness of a family of bounded functionals

`s8g_smooth`: let `F : E → (V →L[ℝ] Z)` be such that, for every `q ∈ V`, `x ↦ F x q` is `C^{n+1}` and its iterated derivatives
of order `≤ n+1` are bounded by `w x * ‖q‖` for a continuous weight `w`.  Then `F` is `C^n` as a map into the operator space.
(Lemma for the tensor clause (4b): `x ↦ (f ↦ U_t f (x))` is a `C^j` map into the dual of `C_0`.)
-/

noncomputable section

open Filter Topology Metric
open scoped ContDiff

namespace HRS.MS.Wad

/-- Mean value bound for the first order Taylor remainder of a `C^2` function. -/
theorem s8g_taylor {E Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {g : E → Z} (hg : ContDiff ℝ 2 g) {x : E} {δ B : ℝ}
    (hB : ∀ z ∈ Metric.ball x δ, ‖iteratedFDeriv ℝ 2 g z‖ ≤ B) {h : E} (hh : ‖h‖ < δ) :
    ‖g (x + h) - g x - fderiv ℝ g x h‖ ≤ B * ‖h‖ ^ 2 := by
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hdg : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hsub : Metric.closedBall x ‖h‖ ⊆ Metric.ball x δ := fun z hz => by
    rw [mem_ball_iff_norm]
    exact lt_of_le_of_lt (mem_closedBall_iff_norm.1 hz) hh
  have h2 : ∀ y ∈ Metric.closedBall x ‖h‖, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ B := fun y hy => by
    have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := g) (x := y) (n := 1)
    rw [norm_iteratedFDeriv_one] at this
    rw [this]
    exact hB y (hsub hy)
  set ψ : E → Z := fun z => g z - fderiv ℝ g x z with hψ
  have hψd : ∀ z, HasFDerivAt ψ (fderiv ℝ g z - fderiv ℝ g x) z := fun z =>
    (hg1 z).hasFDerivAt.sub (fderiv ℝ g x).hasFDerivAt
  have key : ∀ z ∈ Metric.closedBall x ‖h‖, ‖fderiv ℝ ψ z‖ ≤ B * ‖h‖ := by
    intro z hz
    rw [(hψd z).fderiv]
    have h3 := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fderiv ℝ g) (C := B)
      (s := Metric.closedBall x ‖h‖) (fun y _ => hdg y) h2 (convex_closedBall _ _)
      (mem_closedBall_self (norm_nonneg h)) hz
    have h4 : ‖z - x‖ ≤ ‖h‖ := mem_closedBall_iff_norm.1 hz
    have hB0 : 0 ≤ B := (norm_nonneg (fderiv ℝ (fderiv ℝ g) x)).trans (h2 x (mem_closedBall_self (norm_nonneg h)))
    calc ‖fderiv ℝ g z - fderiv ℝ g x‖ ≤ B * ‖z - x‖ := by simpa [norm_sub_rev] using h3
      _ ≤ B * ‖h‖ := mul_le_mul_of_nonneg_left h4 hB0
  have hx1 : x + h ∈ Metric.closedBall x ‖h‖ := by simp [mem_closedBall_iff_norm]
  have h5 := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := ψ) (C := B * ‖h‖)
    (s := Metric.closedBall x ‖h‖) (fun y _ => (hψd y).differentiableAt) key (convex_closedBall _ _)
    (mem_closedBall_self (norm_nonneg h)) hx1
  have e : ψ (x + h) - ψ x = g (x + h) - g x - fderiv ℝ g x h := by
    simp only [hψ, map_add]; abel
  rw [e] at h5
  simpa [sq, mul_assoc] using h5


theorem s8g_lip {E V Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {w : E → ℝ} (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x) (F : E → V →L[ℝ] Z)
    (h1 : ∀ q, ContDiff ℝ 1 (fun x => F x q))
    (hb : ∀ q x, ‖iteratedFDeriv ℝ 1 (fun x => F x q) x‖ ≤ w x * ‖q‖) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro x0
  obtain ⟨δ, hδ, hδw⟩ := Metric.eventually_nhds_iff_ball.1
    (hw.continuousAt.eventually (gt_mem_nhds (show w x0 < w x0 + 1 by linarith)))
  have hlip : ∀ x ∈ Metric.ball x0 δ, ‖F x - F x0‖ ≤ (w x0 + 1) * ‖x - x0‖ := by
    intro x hx
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by linarith [hw0 x0]) (norm_nonneg _)) fun q => ?_
    have hq : ∀ z ∈ Metric.ball x0 δ, ‖fderiv ℝ (fun x => F x q) z‖ ≤ (w x0 + 1) * ‖q‖ := fun z hz => by
      have := hb q z
      rw [norm_iteratedFDeriv_one] at this
      exact this.trans (mul_le_mul_of_nonneg_right (hδw z hz).le (norm_nonneg _))
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fun x => F x q) (C := (w x0 + 1) * ‖q‖)
      (s := Metric.ball x0 δ) (fun y _ => ((h1 q).differentiable one_ne_zero) y) hq (convex_ball _ _)
      (Metric.mem_ball_self hδ) hx
    simp only [sub_apply]
    calc ‖F x q - F x0 q‖ ≤ (w x0 + 1) * ‖q‖ * ‖x - x0‖ := this
      _ = _ := by ring
  have hT : Tendsto (fun x => ‖F x - F x0‖) (𝓝 x0) (𝓝 0) := by
    have hc : Tendsto (fun x => (w x0 + 1) * ‖x - x0‖) (𝓝 x0) (𝓝 0) := by
      have h := ((continuous_id.sub (continuous_const : Continuous fun _ : E => x0)).norm.tendsto x0).const_mul
        (w x0 + 1)
      simpa using h
    refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hc
    filter_upwards [Metric.ball_mem_nhds x0 hδ] with x hx using hlip x hx
  exact tendsto_iff_norm_sub_tendsto_zero.2 hT

theorem s8g_smooth {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {w : E → ℝ} (hw : Continuous w) (hw0 : ∀ x, 0 ≤ w x) (n : ℕ) :
    ∀ {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (F : E → V →L[ℝ] Z),
      (∀ q, ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun x => F x q)) →
      (∀ q, ∀ k ≤ n + 1, ∀ x, ‖iteratedFDeriv ℝ k (fun x => F x q) x‖ ≤ w x * ‖q‖) →
      ContDiff ℝ (n : WithTop ℕ∞) F := by
  induction n with
  | zero =>
    intro Z _ _ F h1 hb
    exact contDiff_zero.2 (s8g_lip hw hw0 F (by simpa using h1) (fun q x => hb q 1 le_rfl x))
  | succ n ih =>
    intro Z _ _ F h1 hb
    have hdq : ∀ q, Differentiable ℝ (fun x => F x q) := fun q =>
      (h1 q).differentiable (by exact_mod_cast Nat.succ_ne_zero (n + 1))
    let D1 : E → V →L[ℝ] (E →L[ℝ] Z) := fun x =>
      LinearMap.mkContinuous
        { toFun := fun q => fderiv ℝ (fun x => F x q) x
          map_add' := fun q1 q2 => by
            have e : (fun x => F x (q1 + q2)) = (fun x => F x q1) + (fun x => F x q2) := by
              funext x; simp
            rw [e, fderiv_add (hdq q1 x) (hdq q2 x)]
          map_smul' := fun c q => by
            have e : (fun x => F x (c • q)) = fun x => c • F x q := by funext x; simp
            rw [e]; exact fderiv_const_smul (hdq q x) c }
        (w x) (fun q => by
          have := hb q 1 (by omega) x
          rw [norm_iteratedFDeriv_one] at this
          exact this)
    have hD1 : ∀ x q, D1 x q = fderiv ℝ (fun x => F x q) x := fun _ _ => rfl
    have hD1c : ContDiff ℝ (n : WithTop ℕ∞) D1 := by
      refine ih D1 (fun q => ?_) (fun q k hk x => ?_)
      · have e : (fun x => D1 x q) = fderiv ℝ (fun x => F x q) := funext fun x => hD1 x q
        rw [e]
        exact (h1 q).fderiv_right (m := ((n + 1 : ℕ) : WithTop ℕ∞)) (by exact_mod_cast le_rfl)
      · have e : (fun x => D1 x q) = fderiv ℝ (fun x => F x q) := funext fun x => hD1 x q
        rw [e, norm_iteratedFDeriv_fderiv]
        exact hb q (k + 1) (by omega) x
    have hfd : ∀ x, HasFDerivAt F (ContinuousLinearMap.flip (D1 x)) x := by
      intro x
      obtain ⟨δ, hδ, hδw⟩ := Metric.eventually_nhds_iff_ball.1
        (hw.continuousAt.eventually (gt_mem_nhds (show w x < w x + 1 by linarith)))
      rw [hasFDerivAt_iff_isLittleO_nhds_zero]
      have hO : (fun h => F (x + h) - F x - (ContinuousLinearMap.flip (D1 x)) h) =O[𝓝 0] fun h => ‖h‖ ^ 2 := by
        refine Asymptotics.IsBigO.of_bound (w x + 1) ?_
        filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hh
        have hh' : ‖h‖ < δ := by simpa using hh
        have hw1 : 0 ≤ w x + 1 := by linarith [hw0 x]
        rw [Real.norm_of_nonneg (by positivity)]
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun q => ?_
        have h2 : ContDiff ℝ 2 (fun x => F x q) := (h1 q).of_le (by exact_mod_cast Nat.le_add_left 2 n)
        have := s8g_taylor h2 (x := x) (δ := δ) (B := (w x + 1) * ‖q‖) (fun z hz => by
          have hz' : z ∈ Metric.ball x δ := hz
          exact (hb q 2 (by omega) z).trans (mul_le_mul_of_nonneg_right (hδw z hz').le (norm_nonneg _))) hh'
        simp only [sub_apply, ContinuousLinearMap.flip_apply, hD1]
        calc _ ≤ (w x + 1) * ‖q‖ * ‖h‖ ^ 2 := this
          _ = _ := by ring
      exact hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num))
    have hfdr : fderiv ℝ F = fun x => ContinuousLinearMap.flip (D1 x) := funext fun x => (hfd x).fderiv
    have hcd : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ F) := by
      rw [hfdr]
      let L : (V →L[ℝ] E →L[ℝ] Z) →L[ℝ] (E →L[ℝ] V →L[ℝ] Z) :=
        (ContinuousLinearMap.flipₗᵢ ℝ V E Z).toContinuousLinearEquiv.toContinuousLinearMap
      have hL : ∀ A, L A = A.flip := fun A => rfl
      have := ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := V →L[ℝ] E →L[ℝ] Z) (F := E →L[ℝ] V →L[ℝ] Z)
        (n := (n : WithTop ℕ∞)) L
      simp only [← hL]
      exact this.comp hD1c
    have := (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := (n : WithTop ℕ∞)) (f := F)).2
      ⟨fun x => (hfd x).differentiableAt, fun h => absurd h (by simp), hcd⟩
    exact_mod_cast this

end HRS.MS.Wad
