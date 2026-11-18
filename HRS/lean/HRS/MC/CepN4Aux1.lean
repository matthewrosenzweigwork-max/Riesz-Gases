import Mathlib
import HRS.MC.CepK1Aux1
import HRS.Stochastic.EmpiricalIto

/-!
# Packet CEPN4 (aux 1): elementary real-variable bounds for the gap dynamics

* `cepn4_cot_bound`: `|π cot(π u)| ≤ π/(2r)` when `u` is at distance `≥ r` from `ℤ`.
* `cepn4_H_bound`: `π cot(π u) - 1/u` is bounded on `(0, 1/4)`.
* `cepn4_periodic_bound`: a continuous 1-periodic function is bounded.
* `cepn4_grad_bound`: `y ↦ (∇V (mk y)) 0` is bounded and continuous for `V` of class `C¹`.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators

noncomputable section

namespace HRS.MC.CepN4

open HRS Real

/-- `|sin (π v)| ≥ 2 |v|` for `|v| ≤ 1/2`. -/
lemma cepn4_abs_sin_ge {v : ℝ} (hv : |v| ≤ 1 / 2) : 2 * |v| ≤ |Real.sin (π * v)| := by
  have hpi := Real.pi_pos
  have h1 : 2 / π * (π * |v|) ≤ Real.sin (π * |v|) := by
    refine Real.mul_le_sin (by positivity) ?_
    nlinarith [abs_nonneg v]
  have h2 : 2 / π * (π * |v|) = 2 * |v| := by field_simp
  rw [h2] at h1
  rcases le_total 0 v with h | h
  · rw [abs_of_nonneg h] at h1 ⊢
    rw [abs_of_nonneg]; exact h1
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [abs_of_nonneg h])
  · rw [abs_of_nonpos h] at h1 ⊢
    have : Real.sin (π * -v) = - Real.sin (π * v) := by rw [mul_neg, Real.sin_neg]
    rw [this] at h1
    calc 2 * -v ≤ -Real.sin (π * v) := h1
      _ ≤ |Real.sin (π * v)| := neg_le_abs _

lemma cepn4_cot_bound {r u : ℝ} (hr : 0 < r) (h : ∀ m : ℤ, r ≤ |u - m|) :
    |π * (Real.cos (π * u) / Real.sin (π * u))| ≤ π / (2 * r) := by
  have hpi := Real.pi_pos
  have hv : |u - (round u : ℤ)| ≤ 1 / 2 := abs_sub_round u
  have hrv : r ≤ |u - (round u : ℤ)| := h (round u)
  have hu : π * u = π * (u - (round u : ℤ)) + ((round u : ℤ) : ℝ) * π := by ring
  have hsin : |Real.sin (π * u)| = |Real.sin (π * (u - (round u : ℤ)))| := by
    rw [hu, Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have hge : 2 * r ≤ |Real.sin (π * u)| := by
    rw [hsin]
    exact le_trans (by linarith) (cepn4_abs_sin_ge hv)
  have h2r : 0 < 2 * r := by positivity
  rw [abs_mul, abs_div, abs_of_pos hpi]
  have : |Real.cos (π * u)| / |Real.sin (π * u)| ≤ 1 / (2 * r) := by
    rw [div_le_div_iff₀ (lt_of_lt_of_le h2r hge) h2r]
    nlinarith [Real.abs_cos_le_one (π * u)]
  calc π * (|Real.cos (π * u)| / |Real.sin (π * u)|) ≤ π * (1 / (2 * r)) :=
        mul_le_mul_of_nonneg_left this hpi.le
    _ = π / (2 * r) := by ring

lemma cepn4_H_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ, 0 < u → u < 1 / 4 →
      |π * (Real.cos (π * u) / Real.sin (π * u)) - 1 / u| ≤ B := by
  have hcont : ContinuousOn HRS.MC.CepK1.cepk1_H (Set.Icc 0 (1 / 4)) := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with h0 | hpos
    · subst h0
      exact HRS.MC.CepK1.cepk1_H_analyticAt.continuousAt.continuousWithinAt
    · refine ContinuousAt.continuousWithinAt ?_
      have hsin : Real.sin (π * u) ≠ 0 := by
        refine (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
        have := hu.2; nlinarith [Real.pi_pos]
      have hg : ContinuousAt (fun u : ℝ => π * (Real.cos (π * u) / Real.sin (π * u)) - 1 / u) u := by
        refine ContinuousAt.sub (ContinuousAt.mul continuousAt_const (ContinuousAt.div ?_ ?_ hsin)) ?_
        · fun_prop
        · fun_prop
        · exact ContinuousAt.div continuousAt_const continuousAt_id hpos.ne'
      refine hg.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hpos.ne'] with v hv
      exact (HRS.MC.CepK1.cepk1_H_eq hv).symm
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun u hu hu1 => ?_⟩
  have := hC u ⟨hu.le, hu1.le⟩
  rw [← HRS.MC.CepK1.cepk1_H_eq hu.ne']
  exact le_trans this (le_max_left _ _)

lemma cepn4_periodic_bound {f : ℝ → ℝ} (hc : Continuous f) (hp : ∀ u, f (u + 1) = f u) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u, |f u| ≤ B := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.continuousOn (s := Set.Icc (0 : ℝ) 1))
  refine ⟨max C 0, le_max_right _ _, fun u => ?_⟩
  have hper : Function.Periodic f 1 := hp
  have h1 : f (u - (⌊u⌋ : ℤ) * 1) = f u := hper.sub_int_mul_eq ⌊u⌋
  have h2 : u - (⌊u⌋ : ℤ) * 1 = Int.fract u := by rw [mul_one]; rfl
  rw [h2] at h1
  rw [← h1]
  have := hC (Int.fract u) ⟨Int.fract_nonneg u, (Int.fract_lt_one u).le⟩
  exact le_trans this (le_max_left _ _)

/-- The potential force on the covering line, `y ↦ (∇V (mk y)) 0`. -/
def cepn4_gV (V : Torus 1 → ℝ) (y : Euc 1) : ℝ := (Torus.grad V (Torus.mk y)) 0

lemma cepn4_continuous_gradient_comp {V : Torus 1 → ℝ} (hV : Torus.IsCk 1 V) :
    Continuous fun z : Euc 1 => (gradient (Torus.lift V) z) 0 := by
  have h1 : Continuous fun z : Euc 1 => fderiv ℝ (Torus.lift V) z (EuclideanSpace.single 0 1) :=
    (hV.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine h1.congr fun z => ?_
  have : fderiv ℝ (Torus.lift V) z (EuclideanSpace.single 0 1) =
      inner ℝ (gradient (Torus.lift V) z) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) := by
    unfold gradient
    rw [InnerProductSpace.toDual_symm_apply]
  rw [this, EuclideanSpace.inner_single_right]
  simp

lemma cepn4_gV_eq {V : Torus 1 → ℝ} (y : Euc 1) :
    cepn4_gV V y = (gradient (Torus.lift V) y) 0 := by
  unfold cepn4_gV
  rw [grad_mk]

lemma cepn4_continuous_gV {V : Torus 1 → ℝ} (hV : Torus.IsCk 1 V) : Continuous (cepn4_gV V) := by
  have : cepn4_gV V = fun z : Euc 1 => (gradient (Torus.lift V) z) 0 := funext cepn4_gV_eq
  rw [this]
  exact cepn4_continuous_gradient_comp hV

lemma cepn4_gV_bound {V : Torus 1 → ℝ} (hV : Torus.IsCk 1 V) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : Euc 1, |cepn4_gV V y| ≤ B := by
  let ι : ℝ → Euc 1 := fun u => WithLp.toLp 2 (fun _ => u)
  have hι : Continuous ι := by
    unfold ι
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_id)
  have hK : IsCompact (ι '' Set.Icc (0 : ℝ) 1) := isCompact_Icc.image hι
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((cepn4_continuous_gradient_comp hV).continuousOn)
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  have hrep : Torus.rep (Torus.mk y) ∈ ι '' Set.Icc (0 : ℝ) 1 := by
    refine ⟨(Torus.rep (Torus.mk y)) 0, ?_, ?_⟩
    · have h := (AddCircle.equivIco (1 : ℝ) 0 ((Torus.mk y) 0)).2
      have e : (Torus.rep (Torus.mk y)) 0 = ((AddCircle.equivIco (1 : ℝ) 0 ((Torus.mk y) 0) :
        Set.Ico (0 : ℝ) (0 + 1)) : ℝ) := rfl
      rw [e]
      exact ⟨h.1, by have := h.2; linarith⟩
    · ext i
      have : i = 0 := Subsingleton.elim _ _
      subst this
      rfl
  have := hC _ hrep
  have e : cepn4_gV V y = (gradient (Torus.lift V) (Torus.rep (Torus.mk y))) 0 := rfl
  rw [e]
  exact le_trans (by simpa using this) (le_max_left _ _)

end HRS.MC.CepN4
