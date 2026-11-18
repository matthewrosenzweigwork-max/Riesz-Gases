import HRS.MS.SpecAux3
import HRS.Prob.HilbertCLT

/-!
# S21H2, packet R26-T3.S14a (part C): `ℕ`-indexed eigenbasis of a compact symmetric positive operator (generic)

`s21h2_eigen_basis`: on a separable infinite-dimensional real Hilbert space `E`, a compact symmetric operator `T` with `⟪x, T x⟫ ≥ 0` has a Hilbert basis
`b : HilbertBasis ℕ ℝ E` of eigenvectors with nonnegative eigenvalues.  The injective case `HRS.MS.Spec.s8p_compact_selfadjoint_basis` is applied on `(ker T)ᗮ`,
a Hilbert basis of `ker T` is added, and the (countable, infinite) index set is enumerated by `ℕ`.
-/

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace

namespace HRS.MS.R26T3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem s21h2_eigen_basis [SecondCountableTopology E] (T : E →L[ℝ] E) (hT : IsCompactOperator T)
    (hs : (T : E →ₗ[ℝ] E).IsSymmetric) (hpos : ∀ x, 0 ≤ ⟪x, T x⟫) (hinf : ¬ FiniteDimensional ℝ E) :
    ∃ (b : HilbertBasis ℕ ℝ E) (lam : ℕ → ℝ), (∀ k, 0 ≤ lam k) ∧ ∀ k, T (b k) = lam k • b k := by
  classical
  set K0 : Submodule ℝ E := LinearMap.ker (T : E →ₗ[ℝ] E) with hK0
  have hK0c : IsClosed (K0 : Set E) := by
    have : (K0 : Set E) = T ⁻¹' {0} := by ext x; simp [hK0]
    rw [this]; exact isClosed_singleton.preimage T.continuous
  haveI : CompleteSpace K0 := hK0c.completeSpace_coe
  set S : Submodule ℝ E := K0ᗮ with hS
  have hSc : IsClosed (S : Set E) := Submodule.isClosed_orthogonal _
  haveI : CompleteSpace S := hSc.completeSpace_coe
  have hmaps : ∀ x : S, T (x : E) ∈ S := by
    intro x
    show T (x : E) ∈ K0ᗮ
    rw [Submodule.mem_orthogonal]
    intro y hy
    have hy0 : T y = 0 := hy
    have : ⟪T y, (x : E)⟫ = ⟪y, T (x : E)⟫ := hs y x
    rw [hy0, inner_zero_left] at this
    exact this.symm
  let TS : S →L[ℝ] S := (T.comp S.subtypeL).codRestrict S hmaps
  have hTS : ∀ x : S, ((TS x : S) : E) = T x := fun x => rfl
  have hcomp : IsCompactOperator TS := (hT.comp_clm S.subtypeL).codRestrict hmaps hSc
  have hsymm : (TS : S →ₗ[ℝ] S).IsSymmetric := fun x y => by
    show ⟪((TS x : S) : E), (y : E)⟫ = ⟪(x : E), ((TS y : S) : E)⟫
    rw [hTS, hTS]; exact hs x y
  have hposS : ∀ x : S, 0 ≤ ⟪x, TS x⟫ := fun x => by
    show 0 ≤ ⟪(x : E), ((TS x : S) : E)⟫
    rw [hTS]; exact hpos x
  have hinj : Function.Injective TS := by
    refine (injective_iff_map_eq_zero TS).2 fun x hx => ?_
    have h1 : T (x : E) = 0 := by rw [← hTS, hx]; rfl
    have h2 : (x : E) ∈ K0 := h1
    have h3 : ⟪(x : E), (x : E)⟫ = 0 := (Submodule.mem_orthogonal K0 _).1 x.2 _ h2
    exact Subtype.ext (inner_self_eq_zero.1 h3)
  obtain ⟨ι1, b1, lam1, hlam1, heig1, -⟩ :=
    HRS.MS.Spec.s8p_compact_selfadjoint_basis TS hcomp hsymm hposS hinj
  obtain ⟨w, b2, -⟩ := exists_hilbertBasis ℝ K0
  let v : ι1 ⊕ w → E := Sum.elim (fun i => (b1 i : E)) (fun j => ((b2 j : K0) : E))
  have hperp : ∀ i j, ⟪(b1 i : E), ((b2 j : K0) : E)⟫ = 0 := fun i j => by
    rw [real_inner_comm]; exact (Submodule.mem_orthogonal K0 _).1 (b1 i).2 _ (b2 j).2
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    rintro (i | j) (i' | j')
    · have := (orthonormal_iff_ite.1 b1.orthonormal) i i'
      simpa [v] using this
    · simpa [v] using hperp i j'
    · rw [real_inner_comm]; simpa [v] using hperp i' j
    · have := (orthonormal_iff_ite.1 b2.orthonormal) j j'
      simpa [v] using this
  have hsp : (Submodule.span ℝ (Set.range v))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hvx : ∀ i, ⟪v i, x⟫ = 0 := fun i =>
      (Submodule.mem_orthogonal _ _).1 hx _ (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨yK, hyK, zS, hzS, hxe⟩ := Submodule.exists_add_mem_mem_orthogonal (K := K0) x
    have hK : (⟨yK, hyK⟩ : K0) = 0 := by
      have : b2.repr ⟨yK, hyK⟩ = 0 := by
        refine lp.ext (funext fun j => ?_)
        rw [HilbertBasis.repr_apply_apply]
        show ⟪((b2 j : K0) : E), yK⟫ = 0
        have e1 : ⟪((b2 j : K0) : E), zS⟫ = 0 := by
          rw [real_inner_comm]; exact (Submodule.mem_orthogonal' K0 _).1 hzS _ (b2 j).2
        have := hvx (Sum.inr j)
        simp only [v, Sum.elim_inr] at this
        rw [hxe, inner_add_right, e1] at this
        linarith
      exact b2.repr.injective (by rw [this, map_zero])
    have hS' : (⟨zS, hzS⟩ : S) = 0 := by
      have : b1.repr ⟨zS, hzS⟩ = 0 := by
        refine lp.ext (funext fun i => ?_)
        rw [HilbertBasis.repr_apply_apply]
        show ⟪(b1 i : E), zS⟫ = 0
        have e1 : ⟪(b1 i : E), yK⟫ = 0 := by
          rw [real_inner_comm]; exact (Submodule.mem_orthogonal K0 _).1 (b1 i).2 _ hyK
        have := hvx (Sum.inl i)
        simp only [v, Sum.elim_inl] at this
        rw [hxe, inner_add_right, e1] at this
        linarith
      exact b1.repr.injective (by rw [this, map_zero])
    have h1 : zS = 0 := congrArg Subtype.val hS'
    have h2 : yK = 0 := congrArg Subtype.val hK
    rw [hxe, h1, h2, add_zero]
  have hcount : Countable (ι1 ⊕ w) := HRS.HilbertCLTAux.countable_of_orthonormal hv
  have hinfι : Infinite (ι1 ⊕ w) := by
    by_contra hfi
    rw [not_infinite_iff_finite] at hfi
    apply hinf
    have hb := HilbertBasis.mkOfOrthogonalEqBot hv hsp
    have hfd : FiniteDimensional ℝ (Submodule.span ℝ (Set.range hb)) :=
      FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    have hcl : IsClosed ((Submodule.span ℝ (Set.range hb) : Submodule ℝ E) : Set E) :=
      Submodule.closed_of_finiteDimensional _
    have htop : Submodule.span ℝ (Set.range hb) = ⊤ := by
      have := hb.dense_span
      rwa [hcl.submodule_topologicalClosure_eq] at this
    have : FiniteDimensional ℝ (⊤ : Submodule ℝ E) := htop ▸ hfd
    exact LinearEquiv.finiteDimensional (Submodule.topEquiv : (⊤ : Submodule ℝ E) ≃ₗ[ℝ] E)
  obtain ⟨σ⟩ := nonempty_equiv_of_countable (α := ι1 ⊕ w) (β := ℕ)
  have hu : Orthonormal ℝ (v ∘ σ.symm) := hv.comp σ.symm σ.symm.injective
  have hsp' : (Submodule.span ℝ (Set.range (v ∘ σ.symm)))ᗮ = ⊥ := by
    rw [Function.Surjective.range_comp σ.symm.surjective]; exact hsp
  refine ⟨HilbertBasis.mkOfOrthogonalEqBot hu hsp', Sum.elim lam1 (fun _ => 0) ∘ σ.symm,
    fun k => ?_, fun k => ?_⟩
  · rcases h : σ.symm k with i | j
    · simpa [h] using (hlam1 i).le
    · simp [h]
  · rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
    rcases h : σ.symm k with i | j
    · simp only [Function.comp, h, v, Sum.elim_inl]
      have := congrArg (fun z : S => (z : E)) (heig1 i)
      simpa [hTS] using this
    · simp only [Function.comp, h, v, Sum.elim_inr]
      have : (((b2 j : K0)) : E) ∈ K0 := (b2 j).2
      have h0 : T ((b2 j : K0) : E) = 0 := this
      simp [h0]

end HRS.MS.R26T3
