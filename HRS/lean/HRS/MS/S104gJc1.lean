import HRS.MS.S104gConv

/-!
# S10.4 packet S104G, part 2: joint continuity from uniform Lipschitz bounds

Prefix `s104g_`, namespace `HRS.MS.R2WinOrbNL`.

`s104g_jcont_abstract`: let `G t r x` (`0 ≤ r ≤ t ≤ T0`) be continuous in `(r,x)` on `[0,t] × E` for each `t`, Lipschitz in `t` uniformly in `(r,x)`
(`‖G t r x - G t' r x‖ ≤ K |t - t'|` for `r ≤ t, t'`), and Lipschitz in `r` towards the terminal value (`‖G t r x - G t t x‖ ≤ M (t - r)`).  Then `(t,r,x) ↦ G t r x`
is continuous on `{0 ≤ r ≤ t ≤ T0}`.

`s104g_norm_gradient`, `s104g_gradient_sub`: the gradient as the Riesz image of `fderiv`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole

variable {d : ℕ}

theorem s104g_norm_gradient (f : Euc d → ℝ) (x : Euc d) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  simp [gradient]

theorem s104g_gradient_sub {f g : Euc d → ℝ} {x : Euc d} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y - g y) x = gradient f x - gradient g x := by
  have e : (fun y => f y - g y) = f - g := rfl
  simp only [gradient, e, fderiv_sub hf hg, map_sub]

theorem s104g_jcont_abstract {E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F] {G : ℝ → ℝ → E → F}
    {T0 K M : ℝ} (hK0 : 0 ≤ K) (hM0 : 0 ≤ M)
    (hc : ∀ t ∈ Set.Icc (0 : ℝ) T0, ContinuousOn (fun p : ℝ × E => G t p.1 p.2) (Set.Icc (0 : ℝ) t ×ˢ Set.univ))
    (hK : ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ t' ∈ Set.Icc (0 : ℝ) T0, ∀ r : ℝ, 0 ≤ r → r ≤ t → r ≤ t' → ∀ x,
      ‖G t r x - G t' r x‖ ≤ K * |t - t'|)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ r : ℝ, 0 ≤ r → r ≤ t → ∀ x, ‖G t r x - G t t x‖ ≤ M * (t - r)) :
    ContinuousOn (fun q : ℝ × ℝ × E => G q.1 q.2.1 q.2.2) {q : ℝ × ℝ × E | 0 ≤ q.2.1 ∧ q.2.1 ≤ q.1 ∧ q.1 ≤ T0} := by
  rintro ⟨t0, r0, x0⟩ ⟨hr0, hr0t, ht0T⟩
  have ht0 : 0 ≤ t0 := hr0.trans hr0t
  have ht0I : t0 ∈ Set.Icc (0 : ℝ) T0 := ⟨ht0, ht0T⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hct := hc t0 ht0I (r0, x0) ⟨⟨hr0, hr0t⟩, Set.mem_univ _⟩
  rw [Metric.continuousWithinAt_iff] at hct
  obtain ⟨η, hη, hη'⟩ := hct (ε / 2) (half_pos hε)
  set c : ℝ := 2 * M + K + 1 with hc_
  have hcpos : 0 < c := by positivity
  refine ⟨min η (ε / (2 * c)), lt_min hη (by positivity), ?_⟩
  rintro ⟨t, r, x⟩ ⟨hr, hrt, htT⟩ hd
  have hd' : dist t t0 < min η (ε / (2 * c)) ∧ dist r r0 < min η (ε / (2 * c)) ∧ dist x x0 < min η (ε / (2 * c)) := by
    rw [Prod.dist_eq, Prod.dist_eq, max_lt_iff, max_lt_iff] at hd
    exact ⟨hd.1, hd.2.1, hd.2.2⟩
  obtain ⟨hdt, hdr, hdx⟩ := hd'
  have htI : t ∈ Set.Icc (0 : ℝ) T0 := ⟨hr.trans hrt, htT⟩
  set r' : ℝ := min r t0 with hr'
  have hr'0 : 0 ≤ r' := le_min hr ht0
  have hr't : r' ≤ t0 := min_le_right _ _
  have hr'r0 : dist r' r0 < η := by
    have e : r0 = min r0 t0 := (min_eq_left hr0t).symm
    rw [Real.dist_eq, e, hr']
    have := abs_min_sub_min_le_max r t0 r0 t0
    simp only [sub_self, abs_zero] at this
    have h2 : |min r t0 - min r0 t0| ≤ |r - r0| := by
      refine this.trans ?_
      exact max_le (le_refl _) (abs_nonneg _)
    rw [Real.dist_eq] at hdr
    exact lt_of_le_of_lt h2 (hdr.trans_le (min_le_left _ _))
  have hnear : dist (G t0 r' x) (G t0 r0 x0) < ε / 2 := by
    have := hη' (x := (r', x)) ⟨⟨hr'0, hr't⟩, Set.mem_univ _⟩
      (by rw [Prod.dist_eq]; exact max_lt hr'r0 (hdx.trans_le (min_le_left _ _)))
    simpa using this
  have hLip : ‖G t r x - G t0 r' x‖ ≤ c * |t - t0| := by
    have hcK : K ≤ c := by rw [hc_]; linarith
    have hc2M : 2 * M ≤ c := by rw [hc_]; linarith
    by_cases hrt0 : r ≤ t0
    · have e : r' = r := min_eq_left hrt0
      rw [e]
      exact (hK t htI t0 ht0I r hr hrt hrt0 x).trans (mul_le_mul_of_nonneg_right hcK (abs_nonneg _))
    · replace hrt0 := not_le.1 hrt0
      have e : r' = t0 := min_eq_right hrt0.le
      rw [e]
      have ht0t : t0 ≤ t := hrt0.le.trans hrt
      have a1 := hM t htI r hr hrt x
      have a2 := hM t htI t0 ht0 ht0t x
      have a3 := hK t htI t0 ht0I t0 ht0 ht0t le_rfl x
      have hab : |t - t0| = t - t0 := abs_of_nonneg (by linarith)
      rw [hab] at a3 ⊢
      calc ‖G t r x - G t0 t0 x‖ = ‖(G t r x - G t t x) + ((G t t x - G t t0 x) + (G t t0 x - G t0 t0 x))‖ := by
            congr 1; abel
        _ ≤ ‖G t r x - G t t x‖ + (‖G t t x - G t t0 x‖ + ‖G t t0 x - G t0 t0 x‖) :=
            (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ ≤ M * (t - r) + (M * (t - t0) + K * (t - t0)) := by
            refine add_le_add a1 (add_le_add ?_ a3)
            have : G t t x - G t t0 x = -(G t t0 x - G t t x) := by abel
            rw [this, norm_neg]; exact a2
        _ ≤ c * (t - t0) := by
            have h1 : M * (t - r) ≤ M * (t - t0) := mul_le_mul_of_nonneg_left (by linarith) hM0
            have h2 : 0 ≤ t - t0 := by linarith
            nlinarith
  have hsmall : c * |t - t0| < ε / 2 := by
    have : |t - t0| < ε / (2 * c) := by
      rw [← Real.dist_eq]; exact hdt.trans_le (min_le_right _ _)
    calc c * |t - t0| < c * (ε / (2 * c)) := mul_lt_mul_of_pos_left this hcpos
      _ = ε / 2 := by field_simp
  show dist (G t r x) (G t0 r0 x0) < ε
  calc dist (G t r x) (G t0 r0 x0) ≤ dist (G t r x) (G t0 r' x) + dist (G t0 r' x) (G t0 r0 x0) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        rw [dist_eq_norm]
        exact add_lt_add (lt_of_le_of_lt hLip hsmall) hnear
    _ = ε := by ring

end HRS.MS.R2WinOrbNL

end
