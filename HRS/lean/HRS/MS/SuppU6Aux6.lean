import HRS.MS.SuppU6Aux5

/-!
# U6 aux 6: the partition `χ_k = ψ_k G(Ψ)` over a maximal separated net
-/

noncomputable section

open scoped RealInnerProductSpace ContDiff
open MeasureTheory Metric Filter Topology Finset

namespace HRS.U6

variable {d : ℕ}

/-- The transported bump `ψ_k(x) = ψ(F_k⁻¹ x)`. -/
def u6psik (S : Set (EuclideanSpace ℝ (Fin d))) (k : S) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  u6psi d (u6Fi k.1 x)

/-- `Ψ = ∑_k ψ_k²`. -/
def u6Psi (S : Set (EuclideanSpace ℝ (Fin d))) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑' k : S, u6psik S k x ^ 2

/-- The partition functions. -/
def u6chi (S : Set (EuclideanSpace ℝ (Fin d))) (k : S) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  u6psik S k x * u6G (u6Psi S x)

section Net

variable {S : Set (EuclideanSpace ℝ (Fin d))}

lemma u6_locfin (hS : S.Pairwise (u6Sep (1 / 16 : ℝ))) (y : EuclideanSpace ℝ (Fin d)) :
    ∃ V : Set (EuclideanSpace ℝ (Fin d)), IsOpen V ∧ y ∈ V ∧
      {k : S | ∃ z ∈ V, u6psik S k z ≠ 0}.Finite := by
  refine ⟨{z | ‖u6Fi y z‖ < 1}, isOpen_lt ((continuous_u6Fi y).norm) continuous_const, ?_, ?_⟩
  · simp [u6Fi]
  · obtain ⟨K, hK⟩ := u6_count_sub (d := d) (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num) hS
      (1 / 4) 1 (by norm_num) (by norm_num)
    refine (hK y _ ?_).1
    rintro k ⟨z, hz, hne⟩
    refine ⟨u6Fi k.1 z, u6Fi y z, ?_, hz.le, by rw [u6F_Fi, u6F_Fi]⟩
    by_contra hcon
    push Not at hcon
    exact hne (u6psi_eq_zero hcon.le)

lemma u6_Psi_local (hS : S.Pairwise (u6Sep (1 / 16 : ℝ))) (y : EuclideanSpace ℝ (Fin d)) :
    ∃ V : Set (EuclideanSpace ℝ (Fin d)), IsOpen V ∧ y ∈ V ∧ ∃ T : Finset S,
      ∀ z ∈ V, u6Psi S z = ∑ k ∈ T, u6psik S k z ^ 2 ∧ ∀ k ∉ T, u6psik S k z = 0 := by
  obtain ⟨V, hV, hyV, hfin⟩ := u6_locfin hS y
  refine ⟨V, hV, hyV, hfin.toFinset, fun z hz => ?_⟩
  have h0 : ∀ k ∉ hfin.toFinset, u6psik S k z = 0 := by
    intro k hk
    by_contra hne
    exact hk (by simpa using ⟨z, hz, hne⟩)
  refine ⟨?_, h0⟩
  unfold u6Psi
  exact tsum_eq_sum (fun k hk => by rw [h0 k hk]; ring)

lemma u6_Psi_summable (hS : S.Pairwise (u6Sep (1 / 16 : ℝ))) (x : EuclideanSpace ℝ (Fin d)) :
    Summable (fun k : S => u6psik S k x ^ 2) := by
  obtain ⟨V, -, hxV, T, hT⟩ := u6_Psi_local hS x
  exact summable_of_ne_finset_zero (s := T) (fun k hk => by rw [(hT x hxV).2 k hk]; ring)

lemma u6psik_contDiff (k : S) : ContDiff ℝ ∞ (u6psik S k) := by
  unfold u6psik u6Fi
  exact (u6psi_contDiff d).comp ((u6B k.1).contDiff.comp (contDiff_id.sub contDiff_const))

lemma u6_Psi_contDiff (hS : S.Pairwise (u6Sep (1 / 16 : ℝ))) : ContDiff ℝ ∞ (u6Psi S) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  obtain ⟨V, hV, hyV, T, hT⟩ := u6_Psi_local hS y
  have h1 : ContDiffAt ℝ ∞ (fun z => ∑ k ∈ T, u6psik S k z ^ 2) y :=
    (ContDiff.sum (fun k _ => (u6psik_contDiff k).pow 2)).contDiffAt
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hV.mem_nhds hyV] with z hz using (hT z hz).1

lemma u6_Psi_ge_one (hS : S.Pairwise (u6Sep (1 / 16 : ℝ)))
    (hcov : ∀ z : EuclideanSpace ℝ (Fin d), ∃ s ∈ S, ‖z - s‖ < 1 / 16 ∧
      |‖z‖ ^ 2 - ‖s‖ ^ 2| < 1 / 16) (x : EuclideanSpace ℝ (Fin d)) : 1 ≤ u6Psi S x := by
  obtain ⟨s, hs, h1, h2⟩ := hcov x
  have h3 : ‖u6Fi s x‖ ≤ 1 / 8 := by
    refine (norm_u6Fi_le s x).trans ?_
    have e1 : ‖x - s‖ ^ 2 ≤ (1 / 16) ^ 2 := by gcongr
    have := norm_nonneg (x - s)
    have : |‖x‖ ^ 2 - ‖s‖ ^ 2| ≤ 1 / 16 := h2.le
    nlinarith
  have h4 : u6psik S ⟨s, hs⟩ x ^ 2 = 1 := by
    unfold u6psik
    rw [u6psi_eq_one h3]; norm_num
  calc (1 : ℝ) = u6psik S ⟨s, hs⟩ x ^ 2 := h4.symm
    _ ≤ u6Psi S x := (u6_Psi_summable hS x).le_tsum ⟨s, hs⟩ (fun j _ => sq_nonneg _)

lemma u6chi_contDiff (hS : S.Pairwise (u6Sep (1 / 16 : ℝ))) (k : S) :
    ContDiff ℝ ∞ (u6chi S k) :=
  (u6psik_contDiff k).mul (u6G_contDiff.comp (u6_Psi_contDiff hS))

lemma u6chi_tsupport (k : S) :
    tsupport (u6chi S k) ⊆ u6F k.1 '' closedBall 0 (1 / 4) := by
  have hclosed : IsClosed (u6F k.1 '' closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 4)) :=
    ((isCompact_closedBall _ _).image (continuous_u6F k.1)).isClosed
  refine closure_minimal ?_ hclosed
  intro x hx
  have hx' : u6psik S k x ≠ 0 := left_ne_zero_of_mul hx
  refine ⟨u6Fi k.1 x, ?_, u6F_Fi _ _⟩
  rw [mem_closedBall, dist_zero_right]
  by_contra hcon
  push Not at hcon
  exact hx' (u6psi_eq_zero hcon.le)

lemma u6chi_sq (hS : S.Pairwise (u6Sep (1 / 16 : ℝ)))
    (hcov : ∀ z : EuclideanSpace ℝ (Fin d), ∃ s ∈ S, ‖z - s‖ < 1 / 16 ∧
      |‖z‖ ^ 2 - ‖s‖ ^ 2| < 1 / 16) (k : S) (x : EuclideanSpace ℝ (Fin d)) :
    u6chi S k x ^ 2 = u6psik S k x ^ 2 * (u6Psi S x)⁻¹ := by
  unfold u6chi
  rw [mul_pow, u6G_sq (u6_Psi_ge_one hS hcov x)]

lemma u6chi_sum (hS : S.Pairwise (u6Sep (1 / 16 : ℝ)))
    (hcov : ∀ z : EuclideanSpace ℝ (Fin d), ∃ s ∈ S, ‖z - s‖ < 1 / 16 ∧
      |‖z‖ ^ 2 - ‖s‖ ^ 2| < 1 / 16) (x : EuclideanSpace ℝ (Fin d)) :
    Summable (fun k : S => u6chi S k x ^ 2) ∧ ∑' k : S, u6chi S k x ^ 2 = 1 := by
  have e : (fun k : S => u6chi S k x ^ 2) = fun k => u6psik S k x ^ 2 * (u6Psi S x)⁻¹ :=
    funext (fun k => u6chi_sq hS hcov k x)
  rw [e]
  refine ⟨(u6_Psi_summable hS x).mul_right _, ?_⟩
  rw [tsum_mul_right]
  have : u6Psi S x ≠ 0 := by have := u6_Psi_ge_one hS hcov x; positivity
  show u6Psi S x * (u6Psi S x)⁻¹ = 1
  exact mul_inv_cancel₀ this

end Net

end HRS.U6
