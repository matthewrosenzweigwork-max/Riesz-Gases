import Mathlib

/-!
# S8P: a total-boundedness criterion in `C_0(E, 𝕜)` (generic, for compactness of `B P^0_t` on `C_M`, S8.3)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_c0_totallyBounded`: a bounded family in `C_0(E, 𝕜)` (`E` proper) that is uniformly
small outside some compact set and uniformly equicontinuous on each compact set is totally bounded (Arzela–Ascoli with a
cutoff).  `s8p_isCompactOperator_of_c0`: the corresponding criterion for an operator.
-/

noncomputable section

open Metric Set
open scoped ZeroAtInfty

namespace HRS.MS.Spec

theorem s8p_c0_totallyBounded {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {𝕜 : Type*} [RCLike 𝕜]
    (F : Set C₀(E, 𝕜)) (C : ℝ) (hb : ∀ f ∈ F, ‖f‖ ≤ C)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ K : Set E, IsCompact K ∧ ∀ f ∈ F, ∀ x, x ∉ K → ‖f x‖ ≤ ε)
    (hequi : ∀ K : Set E, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ F, ∀ x ∈ K, ∀ y ∈ K,
      dist x y < δ → dist (f x) (f y) < ε) :
    TotallyBounded F := by
  classical
  refine Metric.totallyBounded_of_finite_discretization fun ε hε => ?_
  set η : ℝ := ε / 8 with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨K, hK, hKt⟩ := htail η hη0
  obtain ⟨δ, hδ, hδ'⟩ := hequi K hK η hη0
  obtain ⟨tx, htxK, htxfin, hcover⟩ := hK.finite_cover_balls hδ
  obtain ⟨tc, -, htcfin, hcc⟩ := (isCompact_closedBall (0 : 𝕜) C).finite_cover_balls hη0
  haveI : Fintype tx := htxfin.fintype
  haveI : Fintype tc := htcfin.fintype
  have hval : ∀ (f : F) (x : tx), ∃ c : tc, dist (f.1 x.1) (c : 𝕜) < η := by
    intro f x
    have hf : f.1 x.1 ∈ closedBall (0 : 𝕜) C := by
      rw [mem_closedBall, dist_zero_right]
      refine (f.1.toBCF.norm_coe_le_norm x.1).trans ?_
      rw [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]; exact hb f.1 f.2
    have := hcc hf
    simp only [mem_iUnion, mem_ball] at this
    obtain ⟨c, hc, hdist⟩ := this
    exact ⟨⟨c, hc⟩, hdist⟩
  choose P hP using hval
  refine ⟨tx → tc, inferInstance, fun f x => P f x, fun f g hfg => ?_⟩
  have hbd : ∀ y, ‖(f.1 - g.1) y‖ ≤ ε / 2 := by
    intro y
    simp only [ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply]
    by_cases hy : y ∈ K
    · have := hcover hy
      simp only [mem_iUnion, mem_ball] at this
      obtain ⟨x, hx, hyx⟩ := this
      have hxK : x ∈ K := htxK hx
      have hfx := hδ' f.1 f.2 y hy x hxK hyx
      have hgx := hδ' g.1 g.2 y hy x hxK hyx
      have hpx : P f ⟨x, hx⟩ = P g ⟨x, hx⟩ := congrFun hfg ⟨x, hx⟩
      have h1 := hP f ⟨x, hx⟩
      have h2 := hP g ⟨x, hx⟩
      rw [hpx] at h1
      calc ‖f.1 y - g.1 y‖ = dist (f.1 y) (g.1 y) := (dist_eq_norm _ _).symm
        _ ≤ dist (f.1 y) (f.1 x) + dist (f.1 x) (P g ⟨x, hx⟩) +
            (dist (g.1 x) (P g ⟨x, hx⟩) + dist (g.1 y) (g.1 x)) := by
          have := dist_triangle4 (f.1 y) (f.1 x) ((P g ⟨x, hx⟩ : tc) : 𝕜) (g.1 x)
          have h3 := dist_triangle (g.1 x) (g.1 y) (g.1 x)
          calc dist (f.1 y) (g.1 y) ≤ dist (f.1 y) (f.1 x) + dist (f.1 x) ((P g ⟨x, hx⟩ : tc) : 𝕜) +
              dist ((P g ⟨x, hx⟩ : tc) : 𝕜) (g.1 x) + dist (g.1 x) (g.1 y) := by
                have := dist_triangle4 (f.1 y) (f.1 x) ((P g ⟨x, hx⟩ : tc) : 𝕜) (g.1 x)
                have h4 := dist_triangle (f.1 y) (g.1 x) (g.1 y)
                linarith [dist_comm (f.1 y) (g.1 y)]
            _ = _ := by rw [dist_comm ((P g ⟨x, hx⟩ : tc) : 𝕜) (g.1 x), dist_comm (g.1 x) (g.1 y)]; ring
        _ ≤ ε / 2 := by rw [hη] at *; linarith
    · calc ‖f.1 y - g.1 y‖ ≤ ‖f.1 y‖ + ‖g.1 y‖ := norm_sub_le _ _
        _ ≤ η + η := add_le_add (hKt f.1 f.2 y hy) (hKt g.1 g.2 y hy)
        _ ≤ ε / 2 := by rw [hη]; linarith
  have : ‖f.1 - g.1‖ ≤ ε / 2 := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact (BoundedContinuousFunction.norm_le (by positivity)).2 hbd
  rw [dist_eq_norm]
  linarith

set_option maxHeartbeats 800000 in
/-- Operator form: if the image of the closed unit ball satisfies the hypotheses of `s8p_c0_totallyBounded`,
`T` is a compact operator on `C_0(E, 𝕜)`. -/
theorem s8p_isCompactOperator_of_c0 {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {𝕜 : Type*}
    [RCLike 𝕜] (T : C₀(E, 𝕜) →L[𝕜] C₀(E, 𝕜)) (C : ℝ)
    (hb : ∀ f : C₀(E, 𝕜), ‖f‖ ≤ 1 → ‖T f‖ ≤ C)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ K : Set E, IsCompact K ∧ ∀ f : C₀(E, 𝕜), ‖f‖ ≤ 1 →
      ∀ x, x ∉ K → ‖T f x‖ ≤ ε)
    (hequi : ∀ K : Set E, IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ f : C₀(E, 𝕜), ‖f‖ ≤ 1 → ∀ x ∈ K, ∀ y ∈ K, dist x y < δ → dist (T f x) (T f y) < ε) :
    IsCompactOperator T := by
  have hF : TotallyBounded (T '' Metric.closedBall (0 : C₀(E, 𝕜)) 1) := by
    refine s8p_c0_totallyBounded _ C ?_ ?_ ?_
    · rintro _ ⟨f, hf, rfl⟩
      exact hb f (by simpa using hf)
    · intro ε hε
      obtain ⟨K, hK, hK'⟩ := htail ε hε
      exact ⟨K, hK, by rintro _ ⟨f, hf, rfl⟩ x hx; exact hK' f (by simpa using hf) x hx⟩
    · intro K hK ε hε
      obtain ⟨δ, hδ, h⟩ := hequi K hK ε hε
      exact ⟨δ, hδ, by rintro _ ⟨f, hf, rfl⟩ x hx y hy hxy; exact h f (by simpa using hf) x hx y hy hxy⟩
  have hc : IsCompact (closure (T '' Metric.closedBall (0 : C₀(E, 𝕜)) 1)) :=
    hF.closure.isCompact_of_isClosed isClosed_closure
  have key : ∃ K : Set C₀(E, 𝕜), IsCompact K ∧
      (T : C₀(E, 𝕜) →ₗ[𝕜] C₀(E, 𝕜)) '' Metric.closedBall 0 1 ⊆ K := ⟨_, hc, subset_closure⟩
  exact (isCompactOperator_iff_image_closedBall_subset_compact
    (T : C₀(E, 𝕜) →ₗ[𝕜] C₀(E, 𝕜)) (r := 1) one_pos).2 key

end HRS.MS.Spec
