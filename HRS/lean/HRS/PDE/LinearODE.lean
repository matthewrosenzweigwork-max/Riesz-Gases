import Mathlib

/-!
# Global well-posedness of linear ODEs with continuous coefficients

Auxiliary file of the torus PDE layer (package ADJ-01).  The Fourier–Galerkin approximation of
the adjoint equation (`B:eq:adjoint-forward`, main manuscript L1720–1727) is a linear ODE
`x' = A(t) x` in a finite-dimensional space with `A` continuous in time.  This file provides
global existence and uniqueness on `[0,T]` for such equations in any real Banach space.
-/

noncomputable section

open MeasureTheory Set

namespace HRS.PDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ### Auxiliary: the Volterra map on `C([0,T], E)` -/

section Volterra

variable (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (T : ℝ) (hT : 0 ≤ T) (x₀ : E)

/-- The Picard–Volterra map `y ↦ x₀ + ∫₀ᵗ B s (y s) ds` on `C([0,T], E)`. -/
def volterra (y : C(Icc (0 : ℝ) T, E)) : C(Icc (0 : ℝ) T, E) where
  toFun t := x₀ + ∫ s in (0 : ℝ)..t, B s (IccExtend hT y s)
  continuous_toFun := by
    have hg : Continuous fun s : ℝ => B s (IccExtend hT y s) :=
      hB.clm_apply y.continuous.Icc_extend'
    exact (continuous_const.add (intervalIntegral.continuous_primitive
      (fun a b => hg.intervalIntegrable a b) 0)).comp continuous_subtype_val

include hB in
omit [CompleteSpace E] in
lemma volterra_dist_le (C : ℝ) (hC : ∀ s ∈ Icc (0 : ℝ) T, ‖B s‖ ≤ C) (d : ℝ)
    (n : ℕ) (w₁ w₂ : C(Icc (0 : ℝ) T, E))
    (h : ∀ s : Icc (0 : ℝ) T, dist (w₁ s) (w₂ s) ≤ (C * s) ^ n / n.factorial * d) :
    ∀ t : Icc (0 : ℝ) T, dist (volterra B hB T hT x₀ w₁ t) (volterra B hB T hT x₀ w₂ t) ≤
      (C * t) ^ (n + 1) / (n + 1).factorial * d := by
  rintro ⟨t, ht0, htT⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, hT⟩)
  have hg : ∀ w : C(Icc (0 : ℝ) T, E), Continuous fun s : ℝ => B s (IccExtend hT w s) :=
    fun w => hB.clm_apply w.continuous.Icc_extend'
  simp only [volterra, ContinuousMap.coe_mk, dist_add_left]
  rw [dist_eq_norm, ← intervalIntegral.integral_sub
    ((hg w₁).intervalIntegrable _ _) ((hg w₂).intervalIntegrable _ _)]
  have key : ∀ s ∈ Ioc (0 : ℝ) t,
      ‖B s (IccExtend hT w₁ s) - B s (IccExtend hT w₂ s)‖ ≤ C * ((C * s) ^ n / n.factorial * d) := by
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.trans htT⟩
    have := h ⟨s, hsI⟩
    rw [dist_eq_norm] at this
    rw [← map_sub]
    calc ‖B s (IccExtend hT w₁ s - IccExtend hT w₂ s)‖
        ≤ ‖B s‖ * ‖IccExtend hT w₁ s - IccExtend hT w₂ s‖ := (B s).le_opNorm _
      _ ≤ C * ((C * s) ^ n / n.factorial * d) := by
          rw [IccExtend_of_mem hT _ hsI, IccExtend_of_mem hT _ hsI]
          exact mul_le_mul (hC s hsI) this (norm_nonneg _) hC0
  have hint : ∫ s in (0 : ℝ)..t, C * ((C * s) ^ n / n.factorial * d)
      = (C * t) ^ (n + 1) / (n + 1).factorial * d := by
    have : ∀ s : ℝ, C * ((C * s) ^ n / n.factorial * d)
        = (C ^ (n + 1) * d / n.factorial) * s ^ n := by
      intro s; ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul, integral_pow, Nat.factorial_succ]
    push_cast
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [← hint]
  exact intervalIntegral.norm_integral_le_of_norm_le ht0
    (Filter.Eventually.of_forall key)
    ((by fun_prop : Continuous fun s : ℝ => C * ((C * s) ^ n / n.factorial * d)).intervalIntegrable _ _)

end Volterra

lemma linear_ode_exists_aux (B : ℝ → E →L[ℝ] E) (hB : Continuous B) (T : ℝ) (hT : 0 ≤ T)
    (x₀ : E) :
    ∃ x : ℝ → E, Continuous x ∧ ∀ t ∈ Icc (0 : ℝ) T,
      x t = x₀ + ∫ s in (0 : ℝ)..t, B s (x s) := by
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := B) (s := Icc (0 : ℝ) T) hB.continuousOn
  set C := |C₀| with hCdef
  have hC : ∀ s ∈ Icc (0 : ℝ) T, ‖B s‖ ≤ C := fun s hs => (hC₀ s hs).trans (le_abs_self _)
  set Φ := volterra B hB T hT x₀ with hΦ
  -- the `n`-fold iterate is Lipschitz with constant `(C T)^n / n!`
  have hiter : ∀ (n : ℕ) (y z : C(Icc (0 : ℝ) T, E)) (t : Icc (0 : ℝ) T),
      dist (Φ^[n] y t) (Φ^[n] z t) ≤ (C * t) ^ n / n.factorial * dist y z := by
    intro n
    induction n with
    | zero =>
        intro y z t
        simpa using ContinuousMap.dist_apply_le_dist (f := y) (g := z) t
    | succ n ih =>
        intro y z
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        exact volterra_dist_le B hB T hT x₀ C hC (dist y z) n _ _ (fun s => ih y z s)
  have hC0 : 0 ≤ C := abs_nonneg _
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (C * T) ^ n / n.factorial < 1 :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (C * T)).eventually
      (gt_mem_nhds one_pos) |>.exists
  have hK0 : 0 ≤ (C * T) ^ n / n.factorial := by positivity
  have hcontr : ContractingWith (Real.toNNReal ((C * T) ^ n / n.factorial)) (Φ^[n]) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun y z => ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hK0]; simpa using hn
    · rw [Real.coe_toNNReal _ hK0]
      refine (ContinuousMap.dist_le (by positivity)).2 fun t => ?_
      refine (hiter n y z t).trans ?_
      have : (C * t) ^ n ≤ (C * T) ^ n := by
        apply pow_le_pow_left₀ (mul_nonneg hC0 t.2.1) (mul_le_mul_of_nonneg_left t.2.2 hC0)
      gcongr
  have hfix := hcontr.isFixedPt_fixedPoint_iterate
  set y := hcontr.fixedPoint (Φ^[n]) with hy
  refine ⟨IccExtend hT y, y.continuous.Icc_extend', fun t ht => ?_⟩
  have := congrArg (fun w : C(Icc (0 : ℝ) T, E) => w ⟨t, ht⟩) hfix
  simp only [hΦ, volterra, ContinuousMap.coe_mk] at this
  rw [IccExtend_of_mem hT _ ht]
  exact this.symm

/-- Global existence for `x' = A(t) x`, `x(0) = x₀` on `[0,T]`, `A` continuous on `[0,T]`,
in integral form and with one-sided derivatives within `[0,T]`. -/
theorem linear_ode_exists (A : ℝ → E →L[ℝ] E) (T : ℝ) (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc 0 T)) (x₀ : E) :
    ∃ x : ℝ → E, x 0 = x₀ ∧ ContinuousOn x (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, x t = x₀ + ∫ s in (0 : ℝ)..t, A s (x s)) ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt x (A t (x t)) (Icc 0 T) t := by
  set B : ℝ → E →L[ℝ] E := IccExtend hT (fun t : Icc (0 : ℝ) T => A t) with hBdef
  have hB : Continuous B := hA.domRestrict.Icc_extend'
  have hBA : ∀ s ∈ Icc (0 : ℝ) T, B s = A s := fun s hs => IccExtend_of_mem hT _ hs
  obtain ⟨x, hxc, hx⟩ := linear_ode_exists_aux B hB T hT x₀
  have hx' : ∀ t ∈ Icc (0 : ℝ) T, x t = x₀ + ∫ s in (0 : ℝ)..t, A s (x s) := by
    intro t ht
    rw [hx t ht]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [hBA s (uIcc_subset_Icc ⟨le_rfl, hT⟩ ht hs)]
  have hg : Continuous fun s : ℝ => B s (x s) := hB.clm_apply hxc
  refine ⟨x, ?_, hxc.continuousOn, hx', fun t ht => ?_⟩
  · have := hx' 0 ⟨le_rfl, hT⟩
    simpa using this
  · have h1 : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, B s (x s)) (B t (x t)) t :=
      (hg.integral_hasStrictDerivAt 0 t).hasDerivAt
    have h2 := (h1.const_add x₀).hasDerivWithinAt (s := Icc 0 T)
    rw [hBA t ht] at h2
    refine h2.congr (fun u hu => hx u hu) (hx t ht)

/-- Uniqueness: two continuous solutions of the integral equation on `[0,T]` agree there. -/
theorem linear_ode_unique (A : ℝ → E →L[ℝ] E) (T : ℝ)
    (hA : ContinuousOn A (Icc 0 T)) (x y : ℝ → E)
    (hx : ContinuousOn x (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    (hxe : ∀ t ∈ Icc 0 T, x t = x 0 + ∫ s in (0 : ℝ)..t, A s (x s))
    (hye : ∀ t ∈ Icc 0 T, y t = y 0 + ∫ s in (0 : ℝ)..t, A s (y s))
    (h0 : x 0 = y 0) :
    ∀ t ∈ Icc 0 T, x t = y t := by
  intro t₁ ht₁
  have hT : 0 ≤ T := ht₁.1.trans ht₁.2
  set B : ℝ → E →L[ℝ] E := IccExtend hT (fun t : Icc (0 : ℝ) T => A t) with hBdef
  have hB : Continuous B := hA.domRestrict.Icc_extend'
  have hBA : ∀ s ∈ Icc (0 : ℝ) T, B s = A s := fun s hs => IccExtend_of_mem hT _ hs
  set x' : ℝ → E := IccExtend hT (fun t : Icc (0 : ℝ) T => x t) with hx'def
  set y' : ℝ → E := IccExtend hT (fun t : Icc (0 : ℝ) T => y t) with hy'def
  have hxc : Continuous x' := hx.domRestrict.Icc_extend'
  have hyc : Continuous y' := hy.domRestrict.Icc_extend'
  have hxx : ∀ s ∈ Icc (0 : ℝ) T, x' s = x s := fun s hs => IccExtend_of_mem hT _ hs
  have hyy : ∀ s ∈ Icc (0 : ℝ) T, y' s = y s := fun s hs => IccExtend_of_mem hT _ hs
  set z : ℝ → E := fun t => x' t - y' t with hz
  have hzc : Continuous z := hxc.sub hyc
  have hg : Continuous fun s : ℝ => B s (z s) := hB.clm_apply hzc
  have hzeq : ∀ t ∈ Icc (0 : ℝ) T, z t = ∫ s in (0 : ℝ)..t, B s (z s) := by
    intro t ht
    have hsub : ∀ s ∈ uIcc (0 : ℝ) t, s ∈ Icc (0 : ℝ) T :=
      fun s hs => uIcc_subset_Icc ⟨le_rfl, hT⟩ ht hs
    have h1 : ∫ s in (0 : ℝ)..t, B s (x' s) = ∫ s in (0 : ℝ)..t, A s (x s) :=
      intervalIntegral.integral_congr fun s hs => by
        simp only [hBA s (hsub s hs), hxx s (hsub s hs)]
    have h2 : ∫ s in (0 : ℝ)..t, B s (y' s) = ∫ s in (0 : ℝ)..t, A s (y s) :=
      intervalIntegral.integral_congr fun s hs => by
        simp only [hBA s (hsub s hs), hyy s (hsub s hs)]
    have h3 : ∫ s in (0 : ℝ)..t, B s (z s)
        = (∫ s in (0 : ℝ)..t, B s (x' s)) - ∫ s in (0 : ℝ)..t, B s (y' s) := by
      rw [← intervalIntegral.integral_sub ((hB.clm_apply hxc).intervalIntegrable _ _)
        ((hB.clm_apply hyc).intervalIntegrable _ _)]
      exact intervalIntegral.integral_congr fun s _ => map_sub _ _ _
    have h0' : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    rw [h3, h1, h2]
    simp only [hz, hxx t ht, hyy t ht, hxe t ht, hye t ht, h0]
    abel
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := B) (s := Icc (0 : ℝ) T) hB.continuousOn
  have hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt z (B t (z t)) (Ici t) t := by
    intro t ht
    have h1 : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, B s (z s)) (B t (z t)) t :=
      (hg.integral_hasStrictDerivAt 0 t).hasDerivAt
    have h2 : HasDerivWithinAt z (B t (z t)) (Icc 0 T) t :=
      (h1.hasDerivWithinAt (s := Icc 0 T)).congr (fun u hu => hzeq u hu)
        (hzeq t (Ico_subset_Icc_self ht))
    exact h2.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  have := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := z) (f' := fun t => B t (z t))
    (K := |C₀|) (a := 0) (b := T) hzc.continuousOn hderiv
    (by simpa using hzeq 0 ⟨le_rfl, hT⟩) (fun t ht => by
      have htI : t ∈ Icc (0 : ℝ) T := Ico_subset_Icc_self ht
      calc ‖B t (z t)‖ ≤ ‖B t‖ * ‖z t‖ := (B t).le_opNorm _
        _ ≤ |C₀| * ‖z t‖ := mul_le_mul_of_nonneg_right ((hC₀ t htI).trans (le_abs_self _))
            (norm_nonneg _)) t₁ ht₁
  have h := sub_eq_zero.1 this
  rwa [hxx t₁ ht₁, hyy t₁ ht₁] at h

end HRS.PDE
