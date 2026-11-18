import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# S8P: eigenbasis of a compact, symmetric, positive, injective operator (generic, for S8.7)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.

`s8p_compact_selfadjoint_basis`: for `T` compact, symmetric, `⟨x, T x⟩ ≥ 0`, injective on a real Hilbert space `H`, there is a
Hilbert basis `b : HilbertBasis ι ℝ H` of eigenvectors, `T (b i) = lam i • b i`, `lam i > 0`, and `{i | c ≤ lam i}` is finite for
every `c > 0` (so the eigenvalues tend to `0` along any enumeration).
-/

noncomputable section

open Filter Topology Module
open scoped RealInnerProductSpace

namespace HRS.MS.Spec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Eigenvectors for distinct eigenvalues are orthogonal. -/
theorem s8p_eig_orth {T : H →L[ℝ] H} (hs : (T : H →ₗ[ℝ] H).IsSymmetric) {μ ν : ℝ} (hμν : μ ≠ ν)
    {x y : H} (hx : x ∈ Module.End.eigenspace (T : Module.End ℝ H) μ)
    (hy : y ∈ Module.End.eigenspace (T : Module.End ℝ H) ν) : ⟪x, y⟫ = 0 := by
  have := hs.orthogonalFamily_eigenspaces hμν ⟨x, hx⟩ ⟨y, hy⟩
  simpa using this

/-- No infinite orthonormal family of eigenvectors with eigenvalues bounded below by `c > 0`. -/
theorem s8p_finite_sublevel {T : H →L[ℝ] H} (hT : IsCompactOperator T) {ι : Type*} (e : ι → H)
    (he : Orthonormal ℝ e) (lam : ι → ℝ) (hlam : ∀ i, T (e i) = lam i • e i) {c : ℝ} (hc : 0 < c) :
    {i | c ≤ lam i}.Finite := by
  classical
  by_contra hinf
  have hinf' : {i | c ≤ lam i}.Infinite := hinf
  let f : ℕ ↪ {i | c ≤ lam i} := Set.Infinite.natEmbedding _ hinf'
  obtain ⟨K, hK, hKsub⟩ := hT.image_closedBall_subset_compact 1
  have hmem : ∀ n, T (e (f n)) ∈ K := fun n =>
    hKsub ⟨e (f n), by simp [he.1 (f n)], rfl⟩
  obtain ⟨y, -, φ, hφ, hy⟩ := hK.tendsto_subseq hmem
  have hcau := hy.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcau
  obtain ⟨N, hN⟩ := hcau c hc
  have hne : φ (N + 1) ≠ φ N := (hφ.injective).ne (by omega)
  have hdist := hN (N + 1) (by omega)
  have hij : (f (φ (N + 1))).1 ≠ (f (φ N)).1 := fun h => hne (f.injective (Subtype.ext h))
  set a := (f (φ (N + 1))).1
  set b := (f (φ N)).1
  have ha : c ≤ lam a := (f (φ (N + 1))).2
  have hb : c ≤ lam b := (f (φ N)).2
  have hinner : ⟪e a, e b⟫ = 0 := by
    have := (orthonormal_iff_ite.1 he) a b
    simpa [hij] using this
  have hsq : ‖T (e a) - T (e b)‖ ^ 2 = lam a ^ 2 + lam b ^ 2 := by
    rw [hlam, hlam, norm_sub_sq_real, norm_smul, norm_smul, he.1 a, he.1 b, inner_smul_left,
      inner_smul_right, hinner]
    simp [Real.norm_eq_abs, sq_abs]
  have h1 : c ^ 2 + c ^ 2 ≤ ‖T (e a) - T (e b)‖ ^ 2 := by
    rw [hsq]; nlinarith
  rw [dist_eq_norm] at hdist
  have h2 : ‖T (e a) - T (e b)‖ < c := hdist
  nlinarith [norm_nonneg (T (e a) - T (e b))]

/-- Spectral theorem for compact, symmetric, positive, injective operators: Hilbert basis of eigenvectors. -/
theorem s8p_compact_selfadjoint_basis (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (hs : (T : H →ₗ[ℝ] H).IsSymmetric) (hpos : ∀ x, 0 ≤ ⟪x, T x⟫) (hinj : Function.Injective T) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ H) (lam : ι → ℝ), (∀ i, 0 < lam i) ∧
      (∀ i, T (b i) = lam i • b i) ∧ ∀ c : ℝ, 0 < c → {i | c ≤ lam i}.Finite := by
  classical
  let V : ℝ → Submodule ℝ H := fun μ => Module.End.eigenspace (T : Module.End ℝ H) μ
  let Eig := {μ : ℝ // Module.End.HasEigenvalue (T : Module.End ℝ H) μ}
  have hμpos : ∀ μ : Eig, 0 < μ.1 := by
    intro μ
    have h0 : 0 ≤ μ.1 := eigenvalue_nonneg_of_nonneg μ.2 (fun x => by simpa using hpos x)
    refine lt_of_le_of_ne h0 fun h => ?_
    obtain ⟨x, hx1, hx2⟩ := μ.2.exists_hasEigenvector
    rw [Module.End.mem_eigenspace_iff] at hx1
    rw [← h, zero_smul] at hx1
    exact hx2 (hinj (by simpa using hx1))
  have hfin : ∀ μ : Eig, FiniteDimensional ℝ (V μ.1) := fun μ =>
    ContinuousLinearMap.finite_dimensional_eigenspace hT μ.1 (hμpos μ).ne'
  have hex : ∀ μ : Eig, ∃ (n : ℕ) (v : Fin n → H), Orthonormal ℝ v ∧ (∀ k, v k ∈ V μ.1) ∧
      ∀ x ∈ V μ.1, x ∈ Submodule.span ℝ (Set.range v) := by
    intro μ
    have := hfin μ
    let bb := stdOrthonormalBasis ℝ (V μ.1)
    refine ⟨_, fun k => (bb k : H), ?_, fun k => (bb k).2, fun x hx => ?_⟩
    · exact bb.orthonormal.comp_linearIsometry (V μ.1).subtypeₗᵢ
    · have := bb.sum_repr ⟨x, hx⟩
      have h2 : x = ∑ k, (bb.repr ⟨x, hx⟩ k) • (bb k : H) := by
        have := congrArg (fun z : V μ.1 => (z : H)) this
        simpa using this.symm
      rw [h2]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  choose n v hv hvmem hvspan using hex
  let e : (Σ μ : Eig, Fin (n μ)) → H := fun i => v i.1 i.2
  have he : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    rintro ⟨μ, k⟩ ⟨ν, l⟩
    by_cases hμν : μ = ν
    · subst hμν
      have := (orthonormal_iff_ite.1 (hv μ)) k l
      by_cases hkl : k = l
      · subst hkl; simpa [e] using this
      · have hne : (⟨μ, k⟩ : Σ μ : Eig, Fin (n μ)) ≠ ⟨μ, l⟩ := by
          intro h; exact hkl (eq_of_heq (Sigma.mk.inj_iff.1 h).2)
        simpa [e, hkl, hne] using this
    · have hne : (⟨μ, k⟩ : Σ μ : Eig, Fin (n μ)) ≠ ⟨ν, l⟩ := by
        intro h; exact hμν (Sigma.mk.inj_iff.1 h).1
      have := s8p_eig_orth hs (fun h => hμν (Subtype.ext h)) (hvmem μ k) (hvmem ν l)
      simpa [e, hne] using this
  let lam : (Σ μ : Eig, Fin (n μ)) → ℝ := fun i => i.1.1
  have hlam : ∀ i, T (e i) = lam i • e i := fun i => by
    have := hvmem i.1 i.2
    rwa [Module.End.mem_eigenspace_iff] at this
  have hsp : (Submodule.span ℝ (Set.range e))ᗮ = ⊥ := by
    have hle : (⨆ μ : ℝ, V μ) ≤ Submodule.span ℝ (Set.range e) := by
      refine iSup_le fun μ => ?_
      by_cases hμ : Module.End.HasEigenvalue (T : Module.End ℝ H) μ
      · intro x hx
        have := hvspan ⟨μ, hμ⟩ x hx
        refine Submodule.span_mono ?_ this
        rintro _ ⟨k, rfl⟩
        exact ⟨⟨⟨μ, hμ⟩, k⟩, rfl⟩
      · have : V μ = ⊥ := by
          by_contra h
          exact hμ (Module.End.hasEigenvalue_iff.2 h)
        rw [this]; exact bot_le
    have h0 := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hs
    exact eq_bot_iff.2 (le_trans (Submodule.orthogonal_le hle) h0.le)
  refine ⟨_, HilbertBasis.mkOfOrthogonalEqBot he hsp, lam, fun i => hμpos i.1, fun i => ?_, fun c hc => ?_⟩
  · rw [HilbertBasis.coe_mkOfOrthogonalEqBot]; exact hlam i
  · exact s8p_finite_sublevel hT e he lam hlam hc

end HRS.MS.Spec
