import HRS.MS.UniqQAux5

/-!
# UNIQ-Q, part 6: from difference bounds to bounds on the gradient

`uniqq_deriv_le`, `uniqq_grad_inner`, `uniqq_grad_of_diff` (`|f(x+e) - f(x)| ≤ D|e|` ⇒ `|∇f(x)| ≤ D`),
`uniqq_grad_holder` (second differences ⇒ Hölder bound for `∇f`), and the window versions for `u`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.UniqQ

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Lc

variable {d : ℕ}

theorem uniqq_deriv_le {g : ℝ → ℝ} {g' K : ℝ} (hg : HasDerivAt g g' 0)
    (hK : ∀ t : ℝ, 0 < t → |g t - g 0| ≤ K * t) : |g'| ≤ K := by
  have h := hg.tendsto_slope_zero_right
  have h2 : Tendsto (fun t : ℝ => |t⁻¹ • (g (0 + t) - g 0)|) (𝓝[>] 0) (𝓝 |g'|) := h.abs
  refine le_of_tendsto h2 (eventually_nhdsWithin_of_forall fun t ht => ?_)
  have ht' : 0 < t := ht
  simp only [smul_eq_mul, zero_add, abs_mul, abs_inv, abs_of_pos ht']
  rw [inv_mul_le_iff₀ ht']
  linarith [hK t ht']

theorem uniqq_grad_inner (f : Euc d → ℝ) (x v : Euc d) :
    inner ℝ (gradient f x) v = fderiv ℝ f x v := by
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]

theorem uniqq_vec_bound {v : Euc d} {K : ℝ} (hK : 0 ≤ K) (h : ∀ w : Euc d, |inner ℝ v w| ≤ K * ‖w‖) :
    ‖v‖ ≤ K := by
  by_cases hv : v = 0
  · rw [hv, norm_zero]; exact hK
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have := h v
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at this
  nlinarith

theorem uniqq_grad_of_diff {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ x e : Euc d, |f (x + e) - f x| ≤ D * ‖e‖) (x : Euc d) : ‖gradient f x‖ ≤ D := by
  refine uniqq_vec_bound hD fun w => ?_
  rw [uniqq_grad_inner]
  set g : ℝ → ℝ := fun t => f (x + t • w) with hg
  have hd : HasDerivAt g (fderiv ℝ f x w) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
    have h2 : HasFDerivAt f (fderiv ℝ f (x + (0 : ℝ) • w)) (x + (0 : ℝ) • w) := by
      simpa using (hf.differentiable one_ne_zero x).hasFDerivAt
    have := h2.comp_hasDerivAt (0 : ℝ) h1
    simp only [zero_smul, add_zero] at this
    exact this
  refine uniqq_deriv_le hd fun t ht => ?_
  simp only [hg, zero_smul, add_zero]
  have := h x (t • w)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht] at this
  calc _ ≤ D * (t * ‖w‖) := this
    _ = _ := by ring

theorem uniqq_grad_holder {f : Euc d → ℝ} (hf : ContDiff ℝ 1 f) {D : ℝ} (hD : 0 ≤ D) (x a : Euc d)
    (h : ∀ e : Euc d, |f (x + a + e) - f (x + a) - f (x + e) + f x| ≤ D * ‖e‖) :
    ‖gradient f (x + a) - gradient f x‖ ≤ D := by
  refine uniqq_vec_bound hD fun w => ?_
  rw [inner_sub_left, uniqq_grad_inner, uniqq_grad_inner]
  set g : ℝ → ℝ := fun t => f (x + a + t • w) - f (x + t • w) with hg
  have hd1 : ∀ y : Euc d, HasDerivAt (fun t : ℝ => f (y + t • w)) (fderiv ℝ f y w) 0 := by
    intro y
    have h1 : HasDerivAt (fun t : ℝ => y + t • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add y
    have h2 : HasFDerivAt f (fderiv ℝ f (y + (0 : ℝ) • w)) (y + (0 : ℝ) • w) := by
      simpa using (hf.differentiable one_ne_zero y).hasFDerivAt
    have := h2.comp_hasDerivAt (0 : ℝ) h1
    simp only [zero_smul, add_zero] at this
    exact this
  have hd : HasDerivAt g (fderiv ℝ f (x + a) w - fderiv ℝ f x w) 0 := (hd1 (x + a)).sub (hd1 x)
  refine uniqq_deriv_le hd fun t ht => ?_
  simp only [hg, zero_smul, add_zero]
  have := h (t • w)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht] at this
  have e : f (x + a + t • w) - f (x + t • w) - (f (x + a) - f x) =
      f (x + a + t • w) - f (x + a) - f (x + t • w) + f x := by ring
  rw [e]
  calc _ ≤ D * (t * ‖w‖) := this
    _ = _ := by ring

/-- **gradient and Hölder bounds of `u(r)` on a window** -/
theorem uniqq_window (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ {t : ℝ} {u S : ℝ → Euc d → ℝ}, UqSol Q ν t u S →
      ∀ {r t1 m : ℝ}, 0 ≤ r → r < t1 → t1 ≤ t → t1 - r ≤ 1 → (∀ y, u t1 y = 0) →
        (∀ σ ∈ Ioo r t1, ∀ x, |S σ x| ≤ m) → 0 ≤ m →
        (∀ x, ‖gradient (u r) x‖ ≤ C1 * m * (t1 - r) ^ (1 / 2 : ℝ)) ∧
        (∀ x a, ‖gradient (u r) (x + a) - gradient (u r) x‖ ≤
          C2 * m * (t1 - r) ^ ((1 - β) / 2) * ‖a‖ ^ β) := by
  obtain ⟨C1, hC10, hC1⟩ := uniqq_first Q hν
  obtain ⟨C2, hC20, hC2⟩ := uniqq_second Q hν hβ0 hβ1
  refine ⟨C1, C2, hC10, hC20, fun {t u S} hu {r t1 m} hr0 hrt ht1 hl hz hS hm => ⟨fun x => ?_, fun x a => ?_⟩⟩
  · have hr : r ∈ Icc 0 t := ⟨hr0, hrt.le.trans ht1⟩
    refine uniqq_grad_of_diff ((hu.c2 r hr).of_le (by norm_num)) (by positivity) ?_ x
    intro y e
    have := hC1 hu hr0 hrt ht1 hl hz hS hm y e
    linarith [this]
  · have hr : r ∈ Icc 0 t := ⟨hr0, hrt.le.trans ht1⟩
    refine uniqq_grad_holder ((hu.c2 r hr).of_le (by norm_num)) (by positivity) x a ?_
    intro e
    have := hC2 hu hr0 hrt ht1 hl hz hS hm x a e
    calc _ ≤ _ := this
      _ = _ := by ring

end HRS.MS.UniqQ
