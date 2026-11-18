import HRS.MS.SpecAux3
import HRS.MS.SpecAux4

/-!
# S8P: eigen-sequence of a compact operator and dimension counting (generic, for S8.7)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.

* `s8p_eigen_sequence`: on an infinite-dimensional real Hilbert space, a compact symmetric positive injective `T` has a Hilbert basis
  `b : HilbertBasis ℕ ℝ H` with `T (b n) = lam n • b n`, `lam` positive, antitone, tending to `0`.
* `s8p_dim_count`: if a finite-dimensional subspace `W` carries the form `∑ lam_k ⟨b_k, v⟩²` bounded by `M ‖v‖²` and `lam_k ≥ M' > M`
  off a finite set `F`, then `finrank W ≤ |F|` (min–max counting used for `ω_ℓ ≥ c ℓ^{1/d}`).
-/

noncomputable section

open Filter Topology Module
open scoped RealInnerProductSpace

namespace HRS.MS.Spec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem s8p_dim_count {κ : Type*} (b : HilbertBasis κ ℝ H) (lam : κ → ℝ) (F : Finset κ)
    (W : Submodule ℝ H) [FiniteDimensional ℝ W] {M M' : ℝ} (hMM' : M < M')
    (hF : ∀ k, k ∉ F → M' ≤ lam k)
    (hq : ∀ v ∈ W, Summable (fun k => lam k * ⟪b k, v⟫ ^ 2) ∧
      ∑' k, lam k * ⟪b k, v⟫ ^ 2 ≤ M * ‖v‖ ^ 2) :
    finrank ℝ W ≤ F.card := by
  classical
  let L : W →ₗ[ℝ] (F → ℝ) :=
    { toFun := fun v k => ⟪b k, (v : H)⟫
      map_add' := fun v w => by ext k; simp [inner_add_right]
      map_smul' := fun c v => by ext k; simp [inner_smul_right] }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h0 : ∀ k ∈ F, ⟪b k, (v : H)⟫ = 0 := fun k hk => by
      have := congrFun hv ⟨k, hk⟩
      simpa [L] using this
    obtain ⟨hs, hle⟩ := hq v v.2
    have hpar : HasSum (fun k => ⟪(v : H), b k⟫ * ⟪b k, (v : H)⟫) ⟪(v : H), (v : H)⟫ :=
      b.hasSum_inner_mul_inner _ _
    have hpar' : ∑' k, ⟪b k, (v : H)⟫ ^ 2 = ‖(v : H)‖ ^ 2 := by
      have := hpar.tsum_eq
      rw [real_inner_self_eq_norm_sq] at this
      rw [← this]
      refine tsum_congr fun k => ?_
      rw [real_inner_comm]; ring
    have hsq : Summable fun k => ⟪b k, (v : H)⟫ ^ 2 := by
      have := hpar.summable
      refine this.congr fun k => ?_
      rw [real_inner_comm]; ring
    have hpt : ∀ k, M' * ⟪b k, (v : H)⟫ ^ 2 ≤ lam k * ⟪b k, (v : H)⟫ ^ 2 := by
      intro k
      by_cases hk : k ∈ F
      · rw [h0 k hk]; simp
      · exact mul_le_mul_of_nonneg_right (hF k hk) (sq_nonneg _)
    have h1 : ∑' k, M' * ⟪b k, (v : H)⟫ ^ 2 ≤ ∑' k, lam k * ⟪b k, (v : H)⟫ ^ 2 :=
      Summable.tsum_le_tsum hpt (hsq.mul_left M') hs
    rw [tsum_mul_left, hpar'] at h1
    have h2 : (M' - M) * ‖(v : H)‖ ^ 2 ≤ 0 := by nlinarith
    have h3 : ‖(v : H)‖ ^ 2 = 0 := by
      by_contra hne
      have : 0 < ‖(v : H)‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
      nlinarith
    have : ‖(v : H)‖ = 0 := by simpa using h3
    exact Subtype.ext (norm_eq_zero.1 this)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

/-- Eigen-sequence of a compact, symmetric, positive, injective operator on an infinite-dimensional Hilbert space. -/
theorem s8p_eigen_sequence (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (hs : (T : H →ₗ[ℝ] H).IsSymmetric) (hpos : ∀ x, 0 ≤ ⟪x, T x⟫) (hinj : Function.Injective T)
    (hinf : ¬ FiniteDimensional ℝ H) :
    ∃ (b : HilbertBasis ℕ ℝ H) (lam : ℕ → ℝ), (∀ n, 0 < lam n) ∧ (∀ n, T (b n) = lam n • b n) ∧
      Antitone lam ∧ Tendsto lam atTop (𝓝 0) := by
  classical
  obtain ⟨ι, b, lam, hpos', heig, hfin⟩ := s8p_compact_selfadjoint_basis T hT hs hpos hinj
  have hall : ∀ i, ∃ n : ℕ, ((n : ℝ) + 1)⁻¹ ≤ lam i := fun i => by
    obtain ⟨n, hn⟩ := exists_nat_gt (lam i)⁻¹
    exact ⟨n, by rw [inv_le_comm₀ (by positivity) (hpos' i)]; linarith⟩
  have hcount : Countable ι := by
    have hc : (Set.univ : Set ι).Countable := by
      have : (Set.univ : Set ι) = ⋃ n : ℕ, {i | ((n : ℝ) + 1)⁻¹ ≤ lam i} := by
        ext i
        simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
        exact hall i
      rw [this]
      exact Set.countable_iUnion fun n => (hfin _ (by positivity)).countable
    exact Set.countable_univ_iff.1 hc
  have hinfι : Infinite ι := by
    by_contra hfi
    rw [not_infinite_iff_finite] at hfi
    apply hinf
    have hfd : FiniteDimensional ℝ (Submodule.span ℝ (Set.range b)) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    have hcl : IsClosed ((Submodule.span ℝ (Set.range b) : Submodule ℝ H) : Set H) :=
      Submodule.closed_of_finiteDimensional _
    have htop : Submodule.span ℝ (Set.range b) = ⊤ := by
      have := b.dense_span
      rwa [hcl.submodule_topologicalClosure_eq] at this
    have : FiniteDimensional ℝ (⊤ : Submodule ℝ H) := htop ▸ hfd
    exact LinearEquiv.finiteDimensional (Submodule.topEquiv : (⊤ : Submodule ℝ H) ≃ₗ[ℝ] H)
  have hsub : ∀ c : ℝ, {i | (lam i)⁻¹ ≤ c}.Finite := by
    intro c
    by_cases hc : 0 < c
    · refine (hfin c⁻¹ (by positivity)).subset fun i hi => ?_
      simp only [Set.mem_setOf_eq] at hi ⊢
      rwa [inv_le_comm₀ (hpos' i) hc] at hi
    · convert Set.finite_empty
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_le_of_lt (not_lt.1 hc) (inv_pos.2 (hpos' i))
  obtain ⟨σ, hσ⟩ := s8p_enum_monotone (fun i => (lam i)⁻¹) hsub
  have hdense : ⊤ ≤ (Submodule.span ℝ (Set.range (b ∘ σ))).topologicalClosure := by
    rw [Set.range_comp, σ.surjective.range_eq, Set.image_univ] 
    exact b.dense_span.ge
  have hon : Orthonormal ℝ (b ∘ σ) := b.orthonormal.comp σ σ.injective
  refine ⟨HilbertBasis.mk hon hdense, fun n => lam (σ n), fun n => hpos' _, fun n => ?_, ?_, ?_⟩
  · rw [HilbertBasis.coe_mk]; exact heig _
  · intro n m hnm
    have := hσ hnm
    simp only [Function.comp] at this
    exact (inv_le_inv₀ (hpos' _) (hpos' _)).1 this
  · rw [tendsto_order]
    refine ⟨fun a ha => Eventually.of_forall fun n => lt_trans ha (hpos' _), fun c hc => ?_⟩
    have hfs : {n | c ≤ lam (σ n)}.Finite :=
      Set.Finite.preimage (f := σ) σ.injective.injOn (hfin c hc)
    have := hfs.eventually_cofinite_notMem
    rw [Nat.cofinite_eq_atTop] at this
    filter_upwards [this] with n hn
    simpa using hn

end HRS.MS.Spec
