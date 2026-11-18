import Mathlib
import HRS.MS.SuppU5Aux4

/-!
# Packet U5 (aux 5): orthonormal truncations of a separable Hilbert space
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix

noncomputable section

namespace HRS.U5

open InnerProductSpace (gramSchmidt gramSchmidtNormed span_gramSchmidt span_gramSchmidtNormed_range
  gramSchmidtNormed_orthonormal')

section Hilb

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E]

lemma u5_seq_dense (S : Set E) (hS : S.Nonempty) :
    ∃ u : ℕ → E, (∀ n, u n ∈ S) ∧ S ⊆ closure (Set.range u) := by
  haveI : SecondCountableTopology E := UniformSpace.secondCountable_of_separable E
  haveI : Nonempty S := hS.to_subtype
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq S
  refine ⟨fun n => (u n : E), fun n => (u n).2, fun y hy => ?_⟩
  exact hu.induction_on (p := fun z : S => (z : E) ∈ closure (Set.range fun n => (u n : E)))
    ⟨y, hy⟩ (isClosed_closure.preimage continuous_subtype_val) (fun n => subset_closure ⟨n, rfl⟩)

/-- A sequence in a dense subspace, orthonormal where nonzero, with Parseval. -/
lemma u5_orthoseq (R : Submodule ℝ E) (hR : Rᗮ = ⊥) :
    ∃ g : ℕ → E, (∀ n, g n ∈ R) ∧ (∀ n, ‖g n‖ = 0 ∨ ‖g n‖ = 1) ∧
      (∀ m n, m ≠ n → ⟪g m, g n⟫ = 0) ∧ ∀ x, HasSum (fun n => (⟪g n, x⟫) ^ 2) (‖x‖ ^ 2) := by
  obtain ⟨u, huR, hud⟩ := u5_seq_dense (R : Set E) ⟨0, R.zero_mem⟩
  have hgR : ∀ n, gramSchmidtNormed ℝ u n ∈ R := by
    intro n
    have h1 : gramSchmidt ℝ u n ∈ R := by
      have : gramSchmidt ℝ u n ∈ Submodule.span ℝ (Set.range u) := by
        rw [← span_gramSchmidt]; exact Submodule.subset_span ⟨n, rfl⟩
      exact (Submodule.span_le.2 (by rintro _ ⟨m, rfl⟩; exact huR m)) this
    exact R.smul_mem _ h1
  have hon := gramSchmidtNormed_orthonormal' (𝕜 := ℝ) u
  refine ⟨gramSchmidtNormed ℝ u, hgR, fun n => ?_, fun m n hmn => ?_, fun x => ?_⟩
  · by_cases h : gramSchmidtNormed ℝ u n = 0
    · left; simp [h]
    · right
      exact hon.norm_eq_one (⟨n, h⟩ : {i | gramSchmidtNormed ℝ u i ≠ 0})
  · by_cases hm : gramSchmidtNormed ℝ u m = 0
    · simp [hm]
    by_cases hn : gramSchmidtNormed ℝ u n = 0
    · simp [hn]
    exact hon.inner_eq_zero (i := (⟨m, hm⟩ : {i | gramSchmidtNormed ℝ u i ≠ 0}))
      (j := (⟨n, hn⟩ : {i | gramSchmidtNormed ℝ u i ≠ 0})) (fun h => hmn (congrArg Subtype.val h))
  · set v : {i | gramSchmidtNormed ℝ u i ≠ 0} → E := fun i => gramSchmidtNormed ℝ u i with hv
    have hsp : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      have hle : Submodule.span ℝ (Set.range (gramSchmidtNormed ℝ u)) ≤
          Submodule.span ℝ (Set.range v) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨n, rfl⟩
        by_cases hn : gramSchmidtNormed ℝ u n = 0
        · rw [hn]; exact Submodule.zero_mem _
        · exact Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩
      have hy' := Submodule.orthogonal_le hle hy
      have hu : ∀ n, ⟪u n, y⟫ = 0 := by
        intro n
        have : u n ∈ Submodule.span ℝ (Set.range (gramSchmidtNormed ℝ u)) := by
          rw [span_gramSchmidtNormed_range, span_gramSchmidt]; exact Submodule.subset_span ⟨n, rfl⟩
        exact (Submodule.mem_orthogonal _ _).1 hy' _ this
      have hclosed : IsClosed {z : E | ⟪z, y⟫ = 0} := isClosed_eq (by fun_prop) continuous_const
      have hsub : Set.range u ⊆ {z : E | ⟪z, y⟫ = 0} := by
        rintro _ ⟨n, rfl⟩; exact hu n
      have hRy : y ∈ Rᗮ := by
        rw [Submodule.mem_orthogonal]
        intro r hr
        exact (closure_minimal hsub hclosed) (hud hr)
      rw [hR] at hRy
      exact hRy
    let b : HilbertBasis {i | gramSchmidtNormed ℝ u i ≠ 0} ℝ E :=
      HilbertBasis.mkOfOrthogonalEqBot hon hsp
    have hb : ∀ i, b i = gramSchmidtNormed ℝ u i := fun i =>
      congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot hon hsp) i
    have h1 := b.hasSum_inner_mul_inner x x
    rw [real_inner_self_eq_norm_sq] at h1
    have h2 : HasSum (fun i : {i | gramSchmidtNormed ℝ u i ≠ 0} =>
        (⟪gramSchmidtNormed ℝ u i, x⟫) ^ 2) (‖x‖ ^ 2) := by
      convert h1 using 2 with i
      rw [hb i, real_inner_comm, sq]
    have hsupp : Function.support (fun n => (⟪gramSchmidtNormed ℝ u n, x⟫) ^ 2) ⊆
        {i | gramSchmidtNormed ℝ u i ≠ 0} := by
      intro n hn
      by_contra hc
      apply hn
      have : gramSchmidtNormed ℝ u n = 0 := by simpa using hc
      simp [this]
    exact (hasSum_subtype_iff_of_support_subset hsupp).1 h2

end Hilb

section Trunc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Coordinates of `F` along `g_0,…,g_{L-1}`. -/
def u5_tau (g : ℕ → E) (L : ℕ) : E →L[ℝ] Ek L :=
  (EuclideanSpace.equiv (Fin L) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun ℓ : Fin L => innerSL ℝ (g ℓ))

/-- Synthesis along `g_0,…,g_{L-1}`. -/
def u5_iota (g : ℕ → E) (L : ℕ) : Ek L →L[ℝ] E :=
  ∑ ℓ : Fin L, (EuclideanSpace.proj ℓ : Ek L →L[ℝ] ℝ).smulRight (g ℓ)

lemma u5_tau_apply (g : ℕ → E) (L : ℕ) (F : E) (ℓ : Fin L) : (u5_tau g L F) ℓ = ⟪g ℓ, F⟫ := by
  simp [u5_tau]

lemma u5_iota_apply (g : ℕ → E) (L : ℕ) (y : Ek L) : u5_iota g L y = ∑ ℓ : Fin L, y ℓ • g ℓ := by
  simp [u5_iota]

variable {g : ℕ → E} (hg0 : ∀ n, ‖g n‖ = 0 ∨ ‖g n‖ = 1) (hgo : ∀ m n, m ≠ n → ⟪g m, g n⟫ = 0)
  (hpar : ∀ x, HasSum (fun n => (⟪g n, x⟫) ^ 2) (‖x‖ ^ 2))

include hpar in
lemma u5_tau_sq_eq (L : ℕ) (F : E) :
    ‖u5_tau g L F‖ ^ 2 = ∑ n ∈ Finset.range L, (⟪g n, F⟫) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [u5_tau_apply]
  exact Fin.sum_univ_eq_sum_range (fun n => (⟪g n, F⟫) ^ 2) L

include hpar in
lemma u5_tau_sq_le (L : ℕ) (F : E) : ‖u5_tau g L F‖ ^ 2 ≤ ‖F‖ ^ 2 := by
  rw [u5_tau_sq_eq hpar]
  exact sum_le_hasSum (Finset.range L) (fun i _ => sq_nonneg _) (hpar F)

include hpar in
lemma u5_tau_norm_le (L : ℕ) (F : E) : ‖u5_tau g L F‖ ≤ ‖F‖ :=
  le_of_sq_le_sq (u5_tau_sq_le hpar L F) (norm_nonneg _)

include hpar in
lemma u5_tau_sq_mono (L : ℕ) (F : E) : ‖u5_tau g L F‖ ^ 2 ≤ ‖u5_tau g (L + 1) F‖ ^ 2 := by
  rw [u5_tau_sq_eq hpar, u5_tau_sq_eq hpar, Finset.sum_range_succ]
  linarith [sq_nonneg (⟪g L, F⟫)]

include hpar in
lemma u5_tau_sq_tendsto (F : E) :
    Tendsto (fun L => ‖u5_tau g L F‖ ^ 2) atTop (𝓝 (‖F‖ ^ 2)) := by
  simp_rw [u5_tau_sq_eq hpar]
  exact (hpar F).tendsto_sum_nat

include hg0 hgo in
lemma u5_iota_norm_sq (L : ℕ) (y : Ek L) :
    ‖u5_iota g L y‖ ^ 2 = ∑ ℓ : Fin L, (y ℓ) ^ 2 * ‖g ℓ‖ ^ 2 := by
  rw [u5_iota_apply, ← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.sum_eq_single ℓ]
  · simp [real_inner_self_eq_norm_sq]; ring
  · intro m _ hm
    have : ⟪g ℓ, g m⟫ = 0 := hgo ℓ m (fun h => hm (Fin.ext h.symm))
    simp [this]
  · simp

include hg0 hgo in
lemma u5_iota_norm_le (L : ℕ) (y : Ek L) : ‖u5_iota g L y‖ ≤ ‖y‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [u5_iota_norm_sq hg0 hgo, EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_le_sum fun ℓ _ => ?_
  rcases hg0 ℓ with h | h
  · rw [h]; nlinarith [sq_nonneg (y ℓ)]
  · rw [h]; linarith

include hg0 hgo in
lemma u5_sub_iota_tau_sq (L : ℕ) (F : E) :
    ‖F - u5_iota g L (u5_tau g L F)‖ ^ 2 = ‖F‖ ^ 2 - ‖u5_tau g L F‖ ^ 2 := by
  have h1 : ⟪F, u5_iota g L (u5_tau g L F)⟫ = ∑ ℓ : Fin L, (⟪g ℓ, F⟫) ^ 2 := by
    rw [u5_iota_apply, inner_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [inner_smul_right, u5_tau_apply, real_inner_comm]; ring
  have h2 : ‖u5_iota g L (u5_tau g L F)‖ ^ 2 = ∑ ℓ : Fin L, (⟪g ℓ, F⟫) ^ 2 := by
    rw [u5_iota_norm_sq hg0 hgo]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    simp_rw [u5_tau_apply]
    rcases hg0 ℓ with h | h
    · have : g ℓ = 0 := norm_eq_zero.1 h
      simp [this]
    · rw [h]; ring
  have h3 : ‖u5_tau g L F‖ ^ 2 = ∑ ℓ : Fin L, (⟪g ℓ, F⟫) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; simp_rw [u5_tau_apply]
  rw [norm_sub_sq_real, h1, h2, h3]; ring

include hg0 hgo hpar in
lemma u5_sub_iota_tau_tendsto (F : E) :
    Tendsto (fun L => ‖F - u5_iota g L (u5_tau g L F)‖) atTop (𝓝 0) := by
  have h : Tendsto (fun L => ‖F - u5_iota g L (u5_tau g L F)‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [u5_sub_iota_tau_sq hg0 hgo]
    have h2 := (tendsto_const_nhds (x := ‖F‖ ^ 2)).sub (u5_tau_sq_tendsto hpar F)
    rwa [sub_self] at h2
  have := h.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

include hg0 hgo hpar in
lemma u5_iota_tau_norm_le (L : ℕ) (F : E) : ‖u5_iota g L (u5_tau g L F)‖ ≤ ‖F‖ :=
  (u5_iota_norm_le hg0 hgo L _).trans (u5_tau_norm_le hpar L F)

end Trunc

end HRS.U5
