import HRS.MS.MovAdjAux18

/-!
# S6.7 (packet P4, part 5): differentiation of a parameter integral and the sup-norm bounds of its derivatives

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

`s67_param_deriv`: if `Φ(x) = ∫_0^σ G(s,x) ds` with `G(s,·) ∈ C^K`, `s ↦ G(s,x)` continuous, `‖D^i G(s,x)‖ ≤ g(s)` (`i ≤ K`, `g` interval integrable)
and `Φ ∈ C^K`, then `D^iΦ(x) w = ∫_0^σ D^iG(s,x) w ds` and `‖D^iΦ(x)‖ ≤ ∫_0^σ g` for `i ≤ K`.  Induction on `i`: the difference quotients of the integrand are
dominated by `g(s) ∏‖w_l‖` (mean value theorem) and converge pointwise.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole

variable {d : ℕ}

/-- The evaluation `x ↦ D^i f(x) w` has derivative `D^{i+1} f(x) (Fin.cons v w)` in the direction `v`. -/
theorem s67_iter_hasDeriv {f : Euc d → ℝ} {K i : ℕ} (hf : ContDiff ℝ (K : WithTop ℕ∞) f) (hi : i + 1 ≤ K)
    (x v : Euc d) (w : Fin i → Euc d) :
    HasDerivAt (fun h : ℝ => iteratedFDeriv ℝ i f (x + h • v) w)
      (iteratedFDeriv ℝ (i + 1) f x (Fin.cons v w)) 0 := by
  have hdi : DifferentiableAt ℝ (iteratedFDeriv ℝ i f) x :=
    (hf.differentiable_iteratedFDeriv (m := i) (by exact_mod_cast Nat.lt_of_succ_le hi)) x
  have hline : HasDerivAt (fun h : ℝ => x + h • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h1 : HasFDerivAt (iteratedFDeriv ℝ i f) (fderiv ℝ (iteratedFDeriv ℝ i f) x) x := hdi.hasFDerivAt
  have h1' : HasFDerivAt (iteratedFDeriv ℝ i f) (fderiv ℝ (iteratedFDeriv ℝ i f) x) (x + (0 : ℝ) • v) := by
    simpa using h1
  have h2 := h1'.comp_hasDerivAt (0 : ℝ) hline
  have h3 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => Euc d) ℝ w).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) h2
  have hx : (x + (0 : ℝ) • v) = x := by simp
  simp only [hx] at h3
  have e : iteratedFDeriv ℝ (i + 1) f x (Fin.cons v w) = fderiv ℝ (iteratedFDeriv ℝ i f) x v w := by
    rw [iteratedFDeriv_succ_apply_left]
    simp
  rw [e]
  exact h3

/-- Derivative of the evaluation along a line, at every base point. -/
theorem s67_iter_hasDeriv_at {f : Euc d → ℝ} {K i : ℕ} (hf : ContDiff ℝ (K : WithTop ℕ∞) f) (hi : i + 1 ≤ K)
    (x v : Euc d) (w : Fin i → Euc d) (h' : ℝ) :
    HasDerivAt (fun h : ℝ => iteratedFDeriv ℝ i f (x + h • v) w)
      (iteratedFDeriv ℝ (i + 1) f (x + h' • v) (Fin.cons v w)) h' := by
  have := s67_iter_hasDeriv hf hi (x + h' • v) v w
  have h2 : HasDerivAt (fun k : ℝ => iteratedFDeriv ℝ i f (x + h' • v + k • v) w)
      (iteratedFDeriv ℝ (i + 1) f (x + h' • v) (Fin.cons v w)) (h' - h') := by simpa using this
  have h3 := h2.comp_sub_const h' h'
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun h => ?_)
  simp only [add_assoc, ← add_smul]
  congr 3
  ring

set_option maxHeartbeats 3200000 in
theorem s67_param_deriv {σ : ℝ} (hσ : 0 ≤ σ) {G : ℝ → Euc d → ℝ} {g : ℝ → ℝ} {K : ℕ}
    (hGc : ∀ x, ContinuousOn (fun s => G s x) (Icc 0 σ))
    (hGk : ∀ s ∈ Icc (0 : ℝ) σ, ContDiff ℝ (K : WithTop ℕ∞) (G s))
    (hg : ∀ s ∈ Icc (0 : ℝ) σ, ∀ i, 1 ≤ i → i ≤ K → ∀ x, ‖iteratedFDeriv ℝ i (G s) x‖ ≤ g s)
    (hgi : IntervalIntegrable g volume 0 σ)
    {Φ : Euc d → ℝ} (hΦ : ∀ x, Φ x = ∫ s in (0 : ℝ)..σ, G s x) (hΦK : ContDiff ℝ (K : WithTop ℕ∞) Φ) :
    ∀ i ≤ K, ∀ (x : Euc d) (w : Fin i → Euc d),
      IntervalIntegrable (fun s => iteratedFDeriv ℝ i (G s) x w) volume 0 σ ∧
      iteratedFDeriv ℝ i Φ x w = ∫ s in (0 : ℝ)..σ, iteratedFDeriv ℝ i (G s) x w := by
  intro i
  induction i with
  | zero =>
    intro _ x w
    refine ⟨?_, ?_⟩
    · have := (hGc x).intervalIntegrable_of_Icc (μ := volume) hσ
      simpa [iteratedFDeriv_zero_apply] using this
    · simp only [iteratedFDeriv_zero_apply]
      exact hΦ x
  | succ i ih =>
    intro hi x w
    obtain ⟨v, w', rfl⟩ : ∃ (v : Euc d) (w' : Fin i → Euc d), w = Fin.cons v w' :=
      ⟨w 0, Fin.tail w, (Fin.cons_self_tail w).symm⟩
    have hiK : i ≤ K := (Nat.le_succ i).trans hi
    set Pw : ℝ := ∏ l : Fin (i + 1), ‖(Fin.cons v w' : Fin (i + 1) → Euc d) l‖ with hPw
    have hPw0 : 0 ≤ Pw := Finset.prod_nonneg fun l _ => norm_nonneg _
    -- mean value bound
    have hmv : ∀ s ∈ Icc (0 : ℝ) σ, ∀ h : ℝ, |iteratedFDeriv ℝ i (G s) (x + h • v) w' -
        iteratedFDeriv ℝ i (G s) x w'| ≤ g s * Pw * |h| := by
      intro s hs h
      set lam : ℝ → ℝ := fun h => iteratedFDeriv ℝ i (G s) (x + h • v) w' with hlam
      have hd : ∀ h' : ℝ, HasDerivAt lam
          (iteratedFDeriv ℝ (i + 1) (G s) (x + h' • v) (Fin.cons v w')) h' :=
        fun h' => s67_iter_hasDeriv_at (hGk s hs) hi x v w' h'
      have hbound : ∀ h' : ℝ, ‖deriv lam h'‖ ≤ g s * Pw := by
        intro h'
        rw [(hd h').deriv]
        refine ((iteratedFDeriv ℝ (i + 1) (G s) (x + h' • v)).le_opNorm _).trans ?_
        exact mul_le_mul_of_nonneg_right (hg s hs (i + 1) (Nat.succ_pos _) hi _) hPw0
      have := Convex.norm_image_sub_le_of_norm_deriv_le (f := lam) (s := Set.univ)
        (fun h' _ => (hd h').differentiableAt) (fun h' _ => hbound h') convex_univ
        (Set.mem_univ 0) (Set.mem_univ h)
      simp only [hlam, zero_smul, add_zero, Real.norm_eq_abs, sub_zero] at this
      exact this
    -- the difference quotients
    set Fh : ℝ → ℝ → ℝ := fun h s => h⁻¹ * (iteratedFDeriv ℝ i (G s) (x + h • v) w' -
      iteratedFDeriv ℝ i (G s) x w') with hFh
    have hFint : ∀ h : ℝ, IntervalIntegrable (Fh h) volume 0 σ := by
      intro h
      exact ((ih hiK (x + h • v) w').1.sub (ih hiK x w').1).const_mul h⁻¹
    have hslope : ∀ h : ℝ, h⁻¹ * (iteratedFDeriv ℝ i Φ (x + h • v) w' - iteratedFDeriv ℝ i Φ x w') =
        ∫ s in (0 : ℝ)..σ, Fh h s := by
      intro h
      rw [(ih hiK (x + h • v) w').2, (ih hiK x w').2, ← intervalIntegral.integral_sub
        (ih hiK (x + h • v) w').1 (ih hiK x w').1, ← intervalIntegral.integral_const_mul]
    have hlimF : ∀ s ∈ Icc (0 : ℝ) σ, Tendsto (fun h => Fh h s) (𝓝[≠] 0)
        (𝓝 (iteratedFDeriv ℝ (i + 1) (G s) x (Fin.cons v w'))) := by
      intro s hs
      have := (s67_iter_hasDeriv (hGk s hs) hi x v w')
      have h2 := hasDerivAt_iff_tendsto_slope_zero.1 this
      refine h2.congr (fun h => ?_)
      simp [hFh]
    have hlimΦ : Tendsto (fun h : ℝ => h⁻¹ * (iteratedFDeriv ℝ i Φ (x + h • v) w' -
        iteratedFDeriv ℝ i Φ x w')) (𝓝[≠] 0) (𝓝 (iteratedFDeriv ℝ (i + 1) Φ x (Fin.cons v w'))) := by
      have := hasDerivAt_iff_tendsto_slope_zero.1 (s67_iter_hasDeriv hΦK hi x v w')
      refine this.congr (fun h => ?_)
      simp
    -- dominated convergence
    have hgv : IntervalIntegrable (fun s => g s * Pw) volume 0 σ := hgi.mul_const Pw
    have hDCT : Tendsto (fun h : ℝ => ∫ s in (0 : ℝ)..σ, Fh h s) (𝓝[≠] 0)
        (𝓝 (∫ s in (0 : ℝ)..σ, iteratedFDeriv ℝ (i + 1) (G s) x (Fin.cons v w'))) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun s => g s * Pw) ?_ ?_
        hgv ?_
      · exact Eventually.of_forall fun h => by
          rw [uIoc_of_le hσ]
          exact (hFint h).1.aestronglyMeasurable
      · refine Eventually.of_forall fun h => Eventually.of_forall fun s hs => ?_
        rw [uIoc_of_le hσ] at hs
        by_cases hh : h = 0
        · have hs' : s ∈ Icc (0 : ℝ) σ := ⟨hs.1.le, hs.2⟩
          have hgn : 0 ≤ g s := (norm_nonneg _).trans (hg s hs' (i + 1) (Nat.succ_pos _) hi 0)
          subst hh; simp [hFh]; exact mul_nonneg hgn hPw0
        · have hs' : s ∈ Icc (0 : ℝ) σ := ⟨hs.1.le, hs.2⟩
          have := hmv s hs' h
          simp only [hFh, Real.norm_eq_abs, abs_mul, abs_inv]
          rw [inv_mul_le_iff₀ (abs_pos.2 hh)]
          calc _ ≤ g s * Pw * |h| := this
            _ = |h| * (g s * Pw) := by ring
            _ = _ := by ring
      · refine Eventually.of_forall fun s hs => ?_
        rw [uIoc_of_le hσ] at hs
        exact hlimF s ⟨hs.1.le, hs.2⟩
    haveI : (𝓝[≠] (0 : ℝ)).NeBot := inferInstance
    have hEq : iteratedFDeriv ℝ (i + 1) Φ x (Fin.cons v w') =
        ∫ s in (0 : ℝ)..σ, iteratedFDeriv ℝ (i + 1) (G s) x (Fin.cons v w') := by
      refine tendsto_nhds_unique hlimΦ ?_
      refine hDCT.congr (fun h => ?_)
      exact (hslope h).symm
    refine ⟨?_, hEq⟩
    -- interval integrability of the limit
    have hmeas : AEStronglyMeasurable (fun s => iteratedFDeriv ℝ (i + 1) (G s) x (Fin.cons v w'))
        (volume.restrict (Ioc 0 σ)) := by
      refine aestronglyMeasurable_of_tendsto_ae (u := 𝓝[≠] (0 : ℝ)) (f := fun h s => Fh h s) ?_ ?_
      · exact fun h => (hFint h).1.aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
        exact hlimF s ⟨hs.1.le, hs.2⟩
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hσ).2 ?_
    refine Integrable.mono' ((intervalIntegrable_iff_integrableOn_Ioc_of_le hσ).1 hgv) hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs]
    have hs' : s ∈ Icc (0 : ℝ) σ := ⟨hs.1.le, hs.2⟩
    refine ((iteratedFDeriv ℝ (i + 1) (G s) x).le_opNorm _).trans ?_
    exact mul_le_mul_of_nonneg_right (hg s hs' (i + 1) (Nat.succ_pos _) hi x) hPw0

end HRS.MS.MovAdj
