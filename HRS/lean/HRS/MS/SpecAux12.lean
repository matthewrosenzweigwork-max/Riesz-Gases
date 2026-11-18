import HRS.MS.SpecAux5

/-!
# S8P: an equivalent Hilbert structure `⟨x, B y⟩` on the same topological vector space (generic, for S8.7)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  Given a bounded symmetric `B` on a real inner product space `H` with
`c ‖x‖² ≤ ⟨x, B x⟩ ≤ C ‖x‖²`, the type synonym `BSp D` carries the inner product `⟨x, B y⟩` with the topology of `H`.
Used to solve the generalized eigenproblem `G B e = μ e` (`G = L⁻¹`, `B = A⁻¹`) of S8.7 with `s8p_compact_selfadjoint_basis`.
-/

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace

namespace HRS.MS.Spec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Data of an equivalent inner product `⟨x, B y⟩`. -/
structure BData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  B : H →L[ℝ] H
  symm : ∀ x y, ⟪B x, y⟫ = ⟪x, B y⟫
  c : ℝ
  c_pos : 0 < c
  low : ∀ x, c * ‖x‖ ^ 2 ≤ ⟪x, B x⟫

/-- The type synonym carrying the new inner product. -/
def BSp (_D : BData H) : Type _ := H

instance (D : BData H) : AddCommGroup (BSp D) := inferInstanceAs (AddCommGroup H)
instance (D : BData H) : Module ℝ (BSp D) := inferInstanceAs (Module ℝ H)
instance (D : BData H) : TopologicalSpace (BSp D) := inferInstanceAs (TopologicalSpace H)
instance (D : BData H) : IsTopologicalAddGroup (BSp D) := inferInstanceAs (IsTopologicalAddGroup H)
instance (D : BData H) : ContinuousConstSMul ℝ (BSp D) := inferInstanceAs (ContinuousConstSMul ℝ H)

/-- The core inner product structure. -/
def bcore (D : BData H) : InnerProductSpace.Core ℝ (BSp D) where
  inner x y := ⟪(show H from x), D.B (show H from y)⟫
  conj_inner_symm x y := by
    show (starRingEnd ℝ) ⟪(show H from y), D.B (show H from x)⟫ = ⟪(show H from x), D.B (show H from y)⟫
    rw [conj_trivial, real_inner_comm, D.symm]
  re_inner_nonneg x := by
    show 0 ≤ RCLike.re ⟪(show H from x), D.B (show H from x)⟫
    simp only [RCLike.re_to_real]
    exact le_trans (mul_nonneg D.c_pos.le (sq_nonneg _)) (D.low _)
  add_left x y z := by
    show ⟪(show H from x) + (show H from y), D.B (show H from z)⟫ = _
    rw [inner_add_left]
  smul_left x y r := by
    show ⟪r • (show H from x), D.B (show H from y)⟫ = _
    rw [real_inner_smul_left]; simp
  definite x hx := by
    have h1 : ⟪(show H from x), D.B (show H from x)⟫ = 0 := hx
    have h2 := D.low (show H from x)
    rw [h1] at h2
    have : ‖(show H from x)‖ ^ 2 ≤ 0 := by
      by_contra hne
      push Not at hne
      nlinarith [D.c_pos]
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg (show H from x)])

theorem bsp_cont (D : BData H) :
    ContinuousAt (fun v : BSp D => (bcore D).inner v v) 0 := by
  have : Continuous fun v : H => ⟪v, D.B v⟫ := continuous_id.inner D.B.continuous
  exact this.continuousAt

theorem bsp_vonN (D : BData H) :
    Bornology.IsVonNBounded ℝ {v : BSp D | RCLike.re ((bcore D).inner v v) < 1} := by
  have : Bornology.IsVonNBounded ℝ {v : H | RCLike.re ⟪v, D.B v⟫ < 1} := by
    rw [NormedSpace.isVonNBounded_iff, isBounded_iff_forall_norm_le]
    refine ⟨1 / D.c + 1, fun v hv => ?_⟩
    simp only [Set.mem_setOf_eq, RCLike.re_to_real] at hv
    have h1 := D.low v
    have h2 : ‖v‖ ^ 2 ≤ 1 / D.c := by
      rw [le_div_iff₀ D.c_pos]; nlinarith
    nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - 1)]
  exact this

instance (D : BData H) : NormedAddCommGroup (BSp D) :=
  (bcore D).toNormedAddCommGroupOfTopology (bsp_cont D) (bsp_vonN D)

instance (D : BData H) : InnerProductSpace ℝ (BSp D) :=
  InnerProductSpace.ofCoreOfTopology (bcore D) (bsp_cont D) (bsp_vonN D)

theorem bsp_inner (D : BData H) (x y : BSp D) :
    ⟪x, y⟫ = ⟪(show H from x), D.B (show H from y)⟫ := rfl

theorem bsp_norm_sq (D : BData H) (x : BSp D) : ‖x‖ ^ 2 = ⟪(show H from x), D.B (show H from x)⟫ := by
  rw [← real_inner_self_eq_norm_sq]; rfl

instance bsp_complete [CompleteSpace H] (D : BData H) : CompleteSpace (BSp D) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hlow : ∀ z : BSp D, Real.sqrt D.c * ‖(show H from z)‖ ≤ ‖z‖ := by
    intro z
    rw [← Real.sqrt_sq (norm_nonneg z), bsp_norm_sq, ← Real.sqrt_sq (norm_nonneg (show H from z)),
      ← Real.sqrt_mul D.c_pos.le]
    exact Real.sqrt_le_sqrt (by simpa [mul_pow, Real.sq_sqrt, norm_nonneg] using D.low (show H from z))
  have hc : 0 < Real.sqrt D.c := Real.sqrt_pos.2 D.c_pos
  have hu' : CauchySeq (fun n => (show H from u n)) := by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu (Real.sqrt D.c * ε) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    rw [dist_eq_norm] at h1 ⊢
    have h2 := hlow (u m - u n)
    have h3 : (show H from (u m - u n)) = (show H from u m) - (show H from u n) := rfl
    rw [h3] at h2
    nlinarith
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hu'
  exact ⟨a, ha⟩

end HRS.MS.Spec
