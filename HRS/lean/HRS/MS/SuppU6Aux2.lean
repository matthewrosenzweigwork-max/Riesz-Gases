import HRS.MS.SuppU6Aux1

/-!
# U6 aux 2: charts `F_x(u) = x + A_x u`, basic estimates, separated nets
-/

noncomputable section

open scoped RealInnerProductSpace
open MeasureTheory Metric

namespace HRS.U6

variable {d : ℕ}

/-- The chart `F_x(u) = x + A_x u`. -/
def u6F (x u : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) := x + u6A x u

/-- The inverse chart `y ↦ B_x (y - x)`. -/
def u6Fi (x y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) := u6B x (y - x)

lemma u6F_Fi (x y : EuclideanSpace ℝ (Fin d)) : u6F x (u6Fi x y) = y := by
  simp [u6F, u6Fi, u6A_B]

lemma u6Fi_F (x u : EuclideanSpace ℝ (Fin d)) : u6Fi x (u6F x u) = u := by
  simp [u6F, u6Fi, u6B_A]

lemma continuous_u6F (x : EuclideanSpace ℝ (Fin d)) : Continuous (u6F x) :=
  continuous_const.add (u6A x).continuous

lemma continuous_u6Fi (x : EuclideanSpace ℝ (Fin d)) : Continuous (u6Fi x) :=
  (u6B x).continuous.comp (continuous_id.sub continuous_const)

lemma norm_u6F_sub_le (x u : EuclideanSpace ℝ (Fin d)) : ‖u6F x u - x‖ ≤ ‖u‖ := by
  simpa [u6F] using norm_u6A_le x u

lemma abs_normsq_u6F (x u : EuclideanSpace ℝ (Fin d)) :
    |‖u6F x u‖ ^ 2 - ‖x‖ ^ 2| ≤ 2 * ‖u‖ + ‖u‖ ^ 2 := by
  have h1 : ‖u6F x u‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, u6A x u⟫ + ‖u6A x u‖ ^ 2 := by
    unfold u6F; rw [norm_add_sq_real]
  have h2 : ⟪x, u6A x u⟫ = ⟪u6A x x, u⟫ := inner_u6A x x u
  have h3 : |⟪u6A x x, u⟫| ≤ ‖u‖ := by
    calc |⟪u6A x x, u⟫| ≤ ‖u6A x x‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * ‖u‖ := by gcongr; exact norm_u6A_self_le x
      _ = ‖u‖ := one_mul _
  have h4 : ‖u6A x u‖ ≤ ‖u‖ := norm_u6A_le x u
  have h5 : ‖u6A x u‖ ^ 2 ≤ ‖u‖ ^ 2 := by gcongr
  have h6 := abs_le.mp h3
  rw [h1, abs_le]
  constructor <;> nlinarith [sq_nonneg ‖u6A x u‖, norm_nonneg u]

lemma norm_u6Fi_le (x y : EuclideanSpace ℝ (Fin d)) :
    ‖u6Fi x y‖ ≤ ‖y - x‖ + (|‖y‖ ^ 2 - ‖x‖ ^ 2| + ‖y - x‖ ^ 2) / 2 := by
  set v := y - x with hv
  have h1 : ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, v⟫ + ‖v‖ ^ 2 := by
    rw [← norm_add_sq_real]; simp [hv]
  have h2 : |⟪x, v⟫| ≤ (|‖y‖ ^ 2 - ‖x‖ ^ 2| + ‖v‖ ^ 2) / 2 := by
    have : ⟪x, v⟫ = ((‖y‖ ^ 2 - ‖x‖ ^ 2) - ‖v‖ ^ 2) / 2 := by linarith
    rw [this, abs_div, abs_two]
    have := abs_sub (‖y‖ ^ 2 - ‖x‖ ^ 2) (‖v‖ ^ 2)
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖v‖ ^ 2)] at this
    linarith
  have h3 : ‖u6Fi x y‖ ^ 2 = ‖v‖ ^ 2 + ⟪x, v⟫ ^ 2 := norm_u6B_sq x v
  set c := (|‖y‖ ^ 2 - ‖x‖ ^ 2| + ‖v‖ ^ 2) / 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have h4 : ⟪x, v⟫ ^ 2 ≤ c ^ 2 := by
    have := abs_le.mp h2
    nlinarith [sq_abs ⟪x, v⟫, abs_nonneg ⟪x, v⟫]
  have : ‖u6Fi x y‖ ^ 2 ≤ (‖v‖ + c) ^ 2 := by
    rw [h3]; nlinarith [norm_nonneg v]
  exact le_of_sq_le_sq this (by positivity) |>.trans_eq rfl

/-- Separation relation. -/
def u6Sep (ε : ℝ) (x y : EuclideanSpace ℝ (Fin d)) : Prop :=
  ε ≤ ‖x - y‖ ∨ ε ≤ |‖x‖ ^ 2 - ‖y‖ ^ 2|

lemma u6Sep_symm (ε : ℝ) : Symmetric (u6Sep (d := d) ε) := by
  intro x y h
  rcases h with h | h
  · left; rwa [norm_sub_rev]
  · right; rwa [abs_sub_comm]

lemma u6_exists_net (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Set (EuclideanSpace ℝ (Fin d)), S.Pairwise (u6Sep ε) ∧
      ∀ z, ∃ s ∈ S, ‖z - s‖ < ε ∧ |‖z‖ ^ 2 - ‖s‖ ^ 2| < ε := by
  obtain ⟨S, hS⟩ := zorn_subset {S : Set (EuclideanSpace ℝ (Fin d)) | S.Pairwise (u6Sep ε)}
    (fun c hc hchain => ⟨⋃₀ c, by
      rw [Set.mem_setOf_eq, Set.pairwise_sUnion hchain.directedOn]
      exact fun a ha => hc ha, fun s hs => Set.subset_sUnion_of_mem hs⟩)
  refine ⟨S, hS.1, fun z => ?_⟩
  by_contra hcon
  push_neg at hcon
  have hsep : ∀ s ∈ S, u6Sep ε z s := by
    intro s hs
    by_contra hns
    unfold u6Sep at hns
    push_neg at hns
    exact absurd (hcon s hs hns.1) (not_le.mpr hns.2)
  have hz : z ∉ S := by
    intro hz
    have := hsep z hz
    unfold u6Sep at this
    simp at this
    linarith [this]
  have hins : (insert z S).Pairwise (u6Sep ε) :=
    Set.pairwise_insert.mpr ⟨hS.1, fun b hb _ => ⟨hsep b hb, u6Sep_symm ε (hsep b hb)⟩⟩
  have := hS.2 hins (Set.subset_insert z S)
  exact hz (this (Set.mem_insert z S))

end HRS.U6
