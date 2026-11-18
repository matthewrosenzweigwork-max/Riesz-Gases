import HRS.MS.SA16E1E2
import HRS.MS.SA16StrongApprox

/-!
# S.A.16 E14 (part a): joint continuity of a parametrised family from weak continuity and
uniform bounds on the derivatives
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Deriv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem e14_taylor {g : E → F} (hd : Differentiable ℝ g) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ L * ‖x - y‖) (x v : E) {h : ℝ} (hh : 0 ≤ h) :
    ‖g (x + h • v) - g x - h • fderiv ℝ g x v‖ ≤ L * h * ‖v‖ ^ 2 * h := by
  set φ : ℝ → F := fun t => g (x + t • v) - g x - t • fderiv ℝ g x v with hφ
  have hder : ∀ t : ℝ, HasDerivAt φ (fderiv ℝ g (x + t • v) v - fderiv ℝ g x v) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have h2 := (hd (x + t • v)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => t • fderiv ℝ g x v) (fderiv ℝ g x v) t := by
      simpa using (hasDerivAt_id t).smul_const (fderiv ℝ g x v)
    have h4 := (h2.sub_const (g x)).sub h3
    exact h4
  have hb : ∀ t ∈ Icc (0:ℝ) h, ‖fderiv ℝ g (x + t • v) v - fderiv ℝ g x v‖ ≤ L * h * ‖v‖ ^ 2 := by
    intro t ht
    have h1 := ContinuousLinearMap.le_opNorm (fderiv ℝ g (x + t • v) - fderiv ℝ g x) v
    have h2 := hlip (x + t • v) x
    have h3 : ‖x + t • v - x‖ = t * ‖v‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
    rw [h3] at h2
    have h4 : ‖fderiv ℝ g (x + t • v) v - fderiv ℝ g x v‖ ≤ L * (t * ‖v‖) * ‖v‖ := by
      calc ‖fderiv ℝ g (x + t • v) v - fderiv ℝ g x v‖
          = ‖(fderiv ℝ g (x + t • v) - fderiv ℝ g x) v‖ := by simp
        _ ≤ ‖fderiv ℝ g (x + t • v) - fderiv ℝ g x‖ * ‖v‖ := h1
        _ ≤ (L * (t * ‖v‖)) * ‖v‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    refine h4.trans ?_
    have : L * (t * ‖v‖) * ‖v‖ ≤ L * (h * ‖v‖) * ‖v‖ := by
      gcongr
      exact ht.2
    refine this.trans (le_of_eq ?_)
    ring
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
    (f := φ) (f' := fun t => fderiv ℝ g (x + t • v) v - fderiv ℝ g x v) (s := Icc (0:ℝ) h)
    (C := L * h * ‖v‖ ^ 2) (fun t _ => (hder t).hasDerivWithinAt) hb (convex_Icc 0 h)
    (left_mem_Icc.2 hh) (right_mem_Icc.2 hh)
  have e0 : φ 0 = 0 := by simp [hφ]
  simp only [e0, sub_zero, Real.norm_of_nonneg hh] at hmv
  simpa [hφ] using hmv

theorem e14_deriv_continuousOn {X : Type*} [TopologicalSpace X] {S : Set X} {g : X → E → F}
    {L : ℝ} (hL : 0 ≤ L) (hdiff : ∀ r ∈ S, Differentiable ℝ (g r))
    (hlip : ∀ r ∈ S, ∀ x y, ‖fderiv ℝ (g r) x - fderiv ℝ (g r) y‖ ≤ L * ‖x - y‖)
    (hcont : ContinuousOn (fun q : X × E => g q.1 q.2) (S ×ˢ univ)) :
    ContinuousOn (fun q : X × E => fderiv ℝ (g q.1) q.2) (S ×ˢ univ) := by
  rw [continuousOn_clm_apply]
  intro v
  set Fn : ℕ → X × E → F := fun n q =>
    ((n : ℝ) + 1) • (g q.1 (q.2 + (1 / ((n : ℝ) + 1)) • v) - g q.1 q.2) with hFn
  have hunif : TendstoUniformlyOn Fn (fun q : X × E => fderiv ℝ (g q.1) q.2 v) atTop
      (S ×ˢ univ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (L * ‖v‖ ^ 2 / ε)
    filter_upwards [eventually_ge_atTop N] with n hn q hq
    have hn1 : (0:ℝ) < (n : ℝ) + 1 := by positivity
    have hT := e14_taylor (hdiff q.1 hq.1) hL (hlip q.1 hq.1) q.2 v
      (h := 1 / ((n : ℝ) + 1)) (by positivity)
    have hdist : dist (fderiv ℝ (g q.1) q.2 v) (Fn n q) =
        ((n : ℝ) + 1) * ‖g q.1 (q.2 + (1 / ((n : ℝ) + 1)) • v) - g q.1 q.2 -
          (1 / ((n : ℝ) + 1)) • fderiv ℝ (g q.1) q.2 v‖ := by
      rw [dist_eq_norm, hFn]
      simp only []
      have : fderiv ℝ (g q.1) q.2 v - ((n : ℝ) + 1) • (g q.1 (q.2 + (1 / ((n : ℝ) + 1)) • v) - g q.1 q.2)
          = -(((n : ℝ) + 1) • (g q.1 (q.2 + (1 / ((n : ℝ) + 1)) • v) - g q.1 q.2 -
            (1 / ((n : ℝ) + 1)) • fderiv ℝ (g q.1) q.2 v)) := by
        simp only [smul_sub, smul_smul, mul_one_div_cancel hn1.ne', one_smul]
        abel
      rw [this, norm_neg, norm_smul, Real.norm_of_nonneg hn1.le]
    rw [hdist]
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left hT hn1.le) ?_
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have : ((n : ℝ) + 1) * (L * (1 / ((n : ℝ) + 1)) * ‖v‖ ^ 2 * (1 / ((n : ℝ) + 1))) =
        L * ‖v‖ ^ 2 / ((n : ℝ) + 1) := by field_simp
    rw [this, div_lt_iff₀ hn1]
    have h5 : L * ‖v‖ ^ 2 < ε * N := by
      rw [div_lt_iff₀ hε] at hN; linarith
    nlinarith
  refine hunif.continuousOn ((Eventually.of_forall fun n => ?_).frequently)
  have hmap : MapsTo (fun q : X × E => (q.1, q.2 + (1 / ((n : ℝ) + 1)) • v)) (S ×ˢ univ)
      (S ×ˢ univ) := fun q hq => ⟨hq.1, trivial⟩
  have h1 : ContinuousOn (fun q : X × E => g q.1 (q.2 + (1 / ((n : ℝ) + 1)) • v)) (S ×ˢ univ) :=
    hcont.comp (continuous_fst.prodMk (continuous_snd.add continuous_const)).continuousOn hmap
  exact (h1.sub hcont).const_smul _

end Deriv

end HRS.Whole.AppendixA.Phase2SA16Evolution
