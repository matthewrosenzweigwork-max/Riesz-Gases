import HRS.MS.SuppU6Aux3
import HRS.MS.SuppU6Aux4

/-!
# U6 aux 5: the cutoff `ψ`, the normalising function `G`, local finiteness
-/

noncomputable section

open scoped RealInnerProductSpace ContDiff
open MeasureTheory Metric Filter Topology Finset

namespace HRS.U6

variable {d : ℕ}

/-! ### The bump -/

/-- The fixed bump: `1` on `closedBall 0 (1/8)`, support in `closedBall 0 (1/4)`. -/
def u6bump (d : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The cutoff `ψ`. -/
def u6psi (d : ℕ) : EuclideanSpace ℝ (Fin d) → ℝ := ⇑(u6bump d)

lemma u6psi_contDiff (d : ℕ) : ContDiff ℝ ∞ (u6psi d) := (u6bump d).contDiff

lemma u6psi_eq_one {v : EuclideanSpace ℝ (Fin d)} (hv : ‖v‖ ≤ 1 / 8) : u6psi d v = 1 :=
  (u6bump d).one_of_mem_closedBall (by simpa [u6bump] using hv)

lemma u6psi_eq_zero {v : EuclideanSpace ℝ (Fin d)} (hv : 1 / 4 ≤ ‖v‖) : u6psi d v = 0 :=
  (u6bump d).zero_of_le_dist (by simpa [u6bump] using hv)

lemma u6psi_nonneg (v : EuclideanSpace ℝ (Fin d)) : 0 ≤ u6psi d v := (u6bump d).nonneg

lemma u6psi_le_one (v : EuclideanSpace ℝ (Fin d)) : u6psi d v ≤ 1 := (u6bump d).le_one

lemma u6psi_tsupport (d : ℕ) : tsupport (u6psi d) = closedBall (0 : EuclideanSpace ℝ (Fin d)) (1 / 4) := by
  exact (u6bump d).tsupport_eq

lemma u6psi_hasCompactSupport (d : ℕ) : HasCompactSupport (u6psi d) := (u6bump d).hasCompactSupport

lemma u6psi_bound (d : ℕ) : ∃ M : ℕ → ℝ, ∀ n x, ‖iteratedFDeriv ℝ n (u6psi d) x‖ ≤ M n := by
  have : ∀ n : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n (u6psi d) x‖ ≤ C := fun n => by
    obtain ⟨C, -, hC⟩ := (u6psi_hasCompactSupport d).exists_bound_iteratedFDeriv (u6psi_contDiff d) n
    exact ⟨C, fun x => hC n le_rfl x⟩
  choose M hM using this
  exact ⟨M, hM⟩

/-! ### The normalising function -/

/-- `G(t) = t^{-1/2}` for `t ≥ 1`, smooth on `ℝ`. -/
def u6G (t : ℝ) : ℝ := Real.smoothTransition ((t - 1 / 2) * 2) * (Real.sqrt t)⁻¹

lemma u6G_of_one_le {t : ℝ} (ht : 1 ≤ t) : u6G t = (Real.sqrt t)⁻¹ := by
  unfold u6G
  rw [Real.smoothTransition.one_of_one_le (by linarith), one_mul]

lemma u6G_sq {t : ℝ} (ht : 1 ≤ t) : u6G t ^ 2 = t⁻¹ := by
  rw [u6G_of_one_le ht, inv_pow, Real.sq_sqrt (by linarith)]

lemma u6G_contDiff : ContDiff ℝ ∞ u6G := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t < 1 / 2
  · have : u6G =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      unfold u6G
      rw [Real.smoothTransition.zero_of_nonpos (by simp at hs; linarith), zero_mul]
    exact (contDiffAt_const).congr_of_eventuallyEq this
  · have ht := not_lt.mp ht
    have h0 : t ≠ 0 := by intro h; rw [h] at ht; norm_num at ht
    unfold u6G
    refine ContDiffAt.mul ?_ ?_
    · exact Real.smoothTransition.contDiffAt.comp t
        (((contDiff_id.sub contDiff_const).mul contDiff_const).contDiffAt)
    · exact ((Real.contDiffAt_sqrt h0).inv (Real.sqrt_pos.mpr (by linarith)).ne')

/-! ### Finiteness helper -/

lemma u6_finite_of_card_le {α : Type*} {s : Set α} {K : ℕ}
    (h : ∀ T : Finset α, (↑T : Set α) ⊆ s → T.card ≤ K) : s.Finite := by
  by_contra hinf
  obtain ⟨T, hT, hc⟩ := Set.Infinite.exists_subset_card_eq hinf (K + 1)
  have := h T hT
  omega

lemma u6_encard_le_of_card_le {α : Type*} {s : Set α} {K : ℕ}
    (h : ∀ T : Finset α, (↑T : Set α) ⊆ s → T.card ≤ K) : s.encard ≤ K := by
  have hfin := u6_finite_of_card_le h
  rw [hfin.encard_eq_coe_toFinset_card]
  exact_mod_cast h hfin.toFinset (by simp)

/-- The counting lemma for index type `↥S`. -/
lemma u6_count_sub {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {S : Set (EuclideanSpace ℝ (Fin d))}
    (hS : S.Pairwise (u6Sep ε)) (R R0 : ℝ) (hR : 0 ≤ R) (hR0 : 0 ≤ R0) :
    ∃ K : ℕ, ∀ (p : EuclideanSpace ℝ (Fin d)) (s : Set S), (∀ k ∈ s, ∃ u v, ‖u‖ ≤ R ∧ ‖v‖ ≤ R0 ∧
      u6F k.1 u = u6F p v) → s.Finite ∧ s.encard ≤ K := by
  obtain ⟨K, hK⟩ := u6_count hε hε1 hS R R0 hR hR0
  refine ⟨K, fun p s hs => ?_⟩
  have h : ∀ T : Finset S, (↑T : Set S) ⊆ s → T.card ≤ K := by
    intro T hT
    have := hK p (T.map (Function.Embedding.subtype _)) (by
      intro y hy
      simp only [Finset.coe_map, Set.mem_image] at hy
      obtain ⟨k, _, rfl⟩ := hy
      exact k.2) (by
      intro y hy
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      exact hs k (hT hk))
    simpa using this
  exact ⟨u6_finite_of_card_le h, u6_encard_le_of_card_le h⟩

end HRS.U6
