import HRS.Uniform.Q07cAux1
import HRS.Uniform.RelativeCov
import HRS.Uniform.KotTrace

/-!
# Q07c, part 2: the trace norm of `D^{1/2} C^{1/2}` (TN lemma)
-/

noncomputable section

open HRS
open MeasureTheory Filter Topology HRS.HilbertCLTAux
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Q07c

section Eigen

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Expansion of a bilinear form on combinations of a family. -/
lemma form_comb {m : ℕ} (C : H →L[ℝ] H →L[ℝ] ℝ) (w : Fin m → H) (v u : Fin m → ℝ) :
    C (∑ a, v a • w a) (∑ b, u b • w b) = ∑ a, ∑ b, v a * u b * C (w a) (w b) := by
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring


lemma dot_mulVec_eq {m : ℕ} (C : H →L[ℝ] H →L[ℝ] ℝ) (w : Fin m → H) (v u : Fin m → ℝ) :
    v ⬝ᵥ ((Matrix.of fun a b => C (w a) (w b)) *ᵥ u) = ∑ a, ∑ b, v a * u b * C (w a) (w b) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- Diagonalisation of a nonnegative operator on the span of a finite orthonormal family. -/
lemma exists_diag_family {T : H →L[ℝ] H} (hT : IsPSDOp T) {m : ℕ} (w : Fin m → H)
    (hw : Orthonormal ℝ w) :
    ∃ f : Fin m → H, Orthonormal ℝ f ∧ (∀ i j, i ≠ j → inner ℝ (T (f i)) (T (f j)) = 0) ∧
      ∑ i, inner ℝ (T (f i)) (f i) = ∑ i, inner ℝ (T (w i)) (w i) := by
  classical
  set C2 : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ).bilinearComp T T with hC2
  set C1 : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ).comp T with hC1
  have hC2a : ∀ x y, C2 x y = inner ℝ (T x) (T y) := fun x y => by simp [hC2]
  have hC1a : ∀ x y, C1 x y = inner ℝ (T x) y := fun x y => by simp [hC1]
  have hC0a : ∀ x y, (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ) x y = inner ℝ x y := fun x y => by simp
  set M : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun a b => C2 (w a) (w b) with hM
  set G : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun a b => C1 (w a) (w b) with hG
  have hMpsd : M.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun v => ?_⟩
    · ext i j
      simp only [hM, Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial, hC2a]
      exact real_inner_comm _ _
    · simp only [star_trivial]
      rw [hM, dot_mulVec_eq, ← form_comb, hC2a]
      exact real_inner_self_nonneg
  set b := hMpsd.1.eigenvectorBasis with hb
  set μ : Fin m → ℝ := hMpsd.1.eigenvalues with hμ
  have hbM : ∀ k, M *ᵥ (b k).ofLp = μ k • (b k).ofLp := fun k => hMpsd.1.mulVec_eigenvectorBasis k
  have hbo : ∀ k l, (b k).ofLp ⬝ᵥ (b l).ofLp = if k = l then 1 else 0 := by
    intro k l
    have h := orthonormal_iff_ite.1 b.orthonormal k l
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa [dotProduct_comm] using h
  set f : Fin m → H := fun k => ∑ a, (b k).ofLp a • w a with hf
  have hcomb : ∀ (C : H →L[ℝ] H →L[ℝ] ℝ) k l,
      C (f k) (f l) = (b k).ofLp ⬝ᵥ ((Matrix.of fun a c => C (w a) (w c)) *ᵥ (b l).ofLp) := by
    intro C k l
    rw [dot_mulVec_eq]
    exact form_comb C w _ _
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro k l
    have := hcomb (innerSL ℝ) k l
    rw [hC0a] at this
    rw [this]
    have h1 : (Matrix.of fun a c => (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ) (w a) (w c)) = 1 := by
      ext a c
      simp only [Matrix.of_apply, hC0a, Matrix.one_apply]
      exact orthonormal_iff_ite.1 hw a c
    rw [h1, Matrix.one_mulVec, hbo]
  · intro k l hkl
    have := hcomb C2 k l
    rw [hC2a] at this
    rw [this]
    change (b k).ofLp ⬝ᵥ (M *ᵥ (b l).ofLp) = 0
    rw [hbM, dotProduct_smul, hbo, if_neg hkl]; simp
  · have h1 : ∀ k, inner ℝ (T (f k)) (f k) = (b k).ofLp ⬝ᵥ (G *ᵥ (b k).ofLp) := fun k => by
      rw [← hC1a]; exact hcomb C1 k k
    have h2 : ∀ a, inner ℝ (T (w a)) (w a) = G a a := fun a => by
      simp [hG, hC1a]
    simp only [h1, h2]
    simp only [Matrix.mulVec, dotProduct, hG]
    have hcomp : ∀ a c : Fin m, ∑ k, (b k).ofLp a * (b k).ofLp c = if a = c then 1 else 0 := by
      intro a c
      have h := b.sum_inner_mul_inner (EuclideanSpace.single a (1:ℝ)) (EuclideanSpace.single c (1:ℝ))
      simp only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] at h
      simpa [EuclideanSpace.single_apply, mul_comm, eq_comm] using h
    calc ∑ k, ∑ a, (b k).ofLp a * ∑ c, G a c * (b k).ofLp c
        = ∑ a, ∑ c, G a c * ∑ k, (b k).ofLp a * (b k).ofLp c := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          refine Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ a, G a a := by
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [hcomp]
          simp
      _ = _ := rfl

end Eigen


section TN

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- Bessel-type bound for the diagonal sum of a trace-class form. -/
lemma bessel_trace_le {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) {m : ℕ} (v : Fin m → H)
    (hv : ∀ x, ∑ a, inner ℝ (v a) x ^ 2 ≤ ‖x‖ ^ 2) : ∑ a, C (v a) (v a) ≤ traceNormForm C := by
  obtain ⟨ℓ, hs, hℓ⟩ := hC.exists_decomp'
  have hd : ∀ x, C x x = ∑' j, inner ℝ (ℓ j) x ^ 2 := fun x => by
    rw [← (hℓ x x).tsum_eq]; exact tsum_congr fun j => (sq _).symm
  have hsm : ∀ a, Summable fun j => inner ℝ (ℓ j) (v a) ^ 2 := fun a =>
    (hℓ (v a) (v a)).summable.congr fun j => (sq _).symm
  calc ∑ a, C (v a) (v a) = ∑ a, ∑' j, inner ℝ (ℓ j) (v a) ^ 2 :=
        Finset.sum_congr rfl fun a _ => hd _
    _ = ∑' j, ∑ a, inner ℝ (ℓ j) (v a) ^ 2 := (Summable.tsum_finsetSum fun a _ => hsm a).symm
    _ ≤ ∑' j, ‖ℓ j‖ ^ 2 := by
        refine Summable.tsum_le_tsum (fun j => ?_) (summable_sum fun a _ => hsm a) hs
        have := hv (ℓ j)
        refine le_trans (le_of_eq ?_) this
        exact Finset.sum_congr rfl fun a _ => by rw [real_inner_comm]
    _ ≤ traceNormForm C := by
        obtain ⟨ι₀, -, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
        refine le_trans (le_of_eq ?_) (hC.tsum_basis_le b)
        rw [← (hasSum_diag_decomp hs b).tsum_eq]
        exact tsum_congr fun i => (hd (b i)).symm

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma inner_eq_of_norm_eq {B T : H →L[ℝ] H} (h : ∀ x, ‖B x‖ = ‖T x‖) (x y : H) :
    inner ℝ (B x) (B y) = inner ℝ (T x) (T y) := by
  have e : ∀ (u v : H), inner ℝ u v = (‖u + v‖ * ‖u + v‖ - ‖u‖ * ‖u‖ - ‖v‖ * ‖v‖) / 2 :=
    fun u v => real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two u v
  rw [e (B x) (B y), e (T x) (T y), ← map_add, ← map_add, h, h x, h y]


lemma lower_aux {S₁ S₂ T : H →L[ℝ] H} (h1 : IsPSDOp S₁) (h2 : IsPSDOp S₂) (hT : IsPSDOp T)
    (hBT : ∀ x, ‖S₁ (S₂ x)‖ = ‖T x‖) {ι : Type*} (e : HilbertBasis ι ℝ H)
    (hA : Summable fun j => ‖S₁ (e j)‖ ^ 2) (hB : Summable fun j => ‖S₂ (e j)‖ ^ 2) {m : ℕ}
    (w : Fin m → H) (hw : Orthonormal ℝ w) :
    ∑ i, inner ℝ (T (w i)) (w i) ≤ traceNormForm ((innerSL ℝ).comp (S₂.comp S₁)) := by
  classical
  obtain ⟨f, hfo, hfT, hsum⟩ := exists_diag_family hT w hw
  rw [← hsum]
  set P : Finset (Fin m) := Finset.univ.filter (fun i => T (f i) ≠ 0) with hP
  set σ : Fin P.card ≃ {i // i ∈ P} := P.equivFin.symm with hσ
  have hσinj : Function.Injective fun a : Fin P.card => (σ a).1 :=
    Subtype.val_injective.comp σ.injective
  set v : Fin P.card → H := fun a => f (σ a).1 with hv
  set u : Fin P.card → H := fun a => ‖T (f (σ a).1)‖⁻¹ • S₁ (S₂ (f (σ a).1)) with hu
  have hTne : ∀ a, T (f (σ a).1) ≠ 0 := fun a => (Finset.mem_filter.1 (σ a).2).2
  have hnp : ∀ a, 0 < ‖T (f (σ a).1)‖ := fun a => norm_pos_iff.2 (hTne a)
  have hvo : Orthonormal ℝ v := hfo.comp _ hσinj
  have hBT' : ∀ x y, inner ℝ (S₁ (S₂ x)) (S₁ (S₂ y)) = inner ℝ (T x) (T y) :=
    inner_eq_of_norm_eq (B := S₁.comp S₂) (T := T) (fun x => hBT x)
  have huo : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite]
    intro a b
    simp only [hu, inner_smul_left, inner_smul_right, conj_trivial, hBT']
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, real_inner_self_eq_norm_sq]
      have := (hnp a).ne'
      field_simp
    · rw [if_neg hab, hfT _ _ (fun h => hab (hσinj h))]; simp
  have hsumP : ∑ a, inner ℝ (S₂ (S₁ (u a))) (v a) = ∑ a, ‖T (f (σ a).1)‖ := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hu, hv]
    rw [h2.symm, h1.symm, inner_smul_left, conj_trivial, real_inner_self_eq_norm_sq, hBT]
    field_simp [(hnp a).ne']
  have hle := HRS.Uniform.RelCov.sum_inner_le_traceNormForm e S₁ S₂ h2.symm hA hB u v huo hvo
  have hP2 : ∑ a, ‖T (f (σ a).1)‖ = ∑ i ∈ P, ‖T (f i)‖ :=
    (Equiv.sum_comp σ (fun i : {i // i ∈ P} => ‖T (f i.1)‖)).trans
      (Finset.sum_coe_sort P (fun i => ‖T (f i)‖))
  have hzero : ∀ i, i ∉ P → inner ℝ (T (f i)) (f i) = 0 := by
    intro i hi
    have : T (f i) = 0 := by simpa [hP] using hi
    simp [this]
  calc ∑ i, inner ℝ (T (f i)) (f i) = ∑ i ∈ P, inner ℝ (T (f i)) (f i) :=
        (Finset.sum_subset (Finset.subset_univ P) (fun i _ hi => hzero i hi)).symm
    _ ≤ ∑ i ∈ P, ‖T (f i)‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := real_inner_le_norm (T (f i)) (f i)
        rwa [hfo.norm_eq_one i, mul_one] at this
    _ = ∑ a, inner ℝ (S₂ (S₁ (u a))) (v a) := by rw [hsumP, hP2]
    _ ≤ _ := hle


lemma polar_contraction {T : H →L[ℝ] H} (hT : IsPSDOp T) (B : H →L[ℝ] H) (hBT : ∀ x, ‖B x‖ = ‖T x‖) :
    ∃ U : H →L[ℝ] H, (∀ x, U (T x) = B x) ∧ ∀ x, ‖U x‖ ≤ ‖x‖ := by
  obtain ⟨U, Q, -, -, hsym, hid, -, hUS, hUQ⟩ := exists_polar hT B hBT
  refine ⟨U, hUS, fun x => ?_⟩
  rw [hUQ]
  have h1 : ‖Q x‖ ^ 2 = inner ℝ (Q x) x := by
    rw [← real_inner_self_eq_norm_sq, hsym x (Q x), hid x]
    exact real_inner_comm _ _
  have h2 := real_inner_le_norm (Q x) x
  by_cases h0 : ‖Q x‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have : 0 < ‖Q x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

lemma bessel_orthonormal {m : ℕ} (g : Fin m → H) (hg : Orthonormal ℝ g) (x : H) :
    ∑ a, inner ℝ (g a) x ^ 2 ≤ ‖x‖ ^ 2 := by
  have := hg.sum_inner_products_le x (s := Finset.univ)
  simpa [Real.norm_eq_abs, sq_abs] using this

/-- **TN**: `‖S₂ S₁‖₁ = tr T` when `‖S₁ S₂ x‖ = ‖T x‖`. -/
theorem trace_norm_prod {S₁ S₂ T : H →L[ℝ] H} (h1 : IsPSDOp S₁) (h2 : IsPSDOp S₂) (hT : IsPSDOp T)
    (hBT : ∀ x, ‖S₁ (S₂ x)‖ = ‖T x‖) {ι : Type*} (e : HilbertBasis ι ℝ H)
    (hA : Summable fun j => ‖S₁ (e j)‖ ^ 2) (hB : Summable fun j => ‖S₂ (e j)‖ ^ 2) :
    IsTraceClassCov ((innerSL ℝ).comp T) ∧
      traceNormForm ((innerSL ℝ).comp (S₂.comp S₁)) = traceNormForm ((innerSL ℝ).comp T) := by
  classical
  set F : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ).comp (S₂.comp S₁) with hF
  set CT : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ).comp T with hCT
  have hCTa : ∀ x y, CT x y = inner ℝ (T x) y := fun x y => by simp [hCT]
  have hFa : ∀ x y, F x y = inner ℝ (S₂ (S₁ x)) y := fun x y => by simp [hF]
  set N := traceNormForm F with hN
  have hN0 : 0 ≤ N := traceNormForm_nonneg _
  have hlow := fun {m : ℕ} (w : Fin m → H) (hw : Orthonormal ℝ w) =>
    lower_aux h1 h2 hT hBT e hA hB w hw
  have htc : IsTraceClassCov CT := by
    refine ⟨fun x y => ?_, fun x => ?_, ?_⟩
    · rw [hCTa, hCTa, hT.symm, real_inner_comm]
    · rw [hCTa]; exact hT.nonneg x
    · obtain ⟨ι₀, -, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
      refine ⟨ι₀, b, summable_of_sum_le (c := N) (fun i => by rw [hCTa]; exact hT.nonneg _)
        (fun s => ?_)⟩
      have hinj : Function.Injective fun t : Fin s.card => ((s.equivFin.symm t).val : ι₀) :=
        Subtype.val_injective.comp s.equivFin.symm.injective
      have hon : Orthonormal ℝ fun t : Fin s.card => b ((s.equivFin.symm t).val) :=
        b.orthonormal.comp _ hinj
      have h3 := hlow _ hon
      have h4 : ∑ i ∈ s, CT (b i) (b i) = ∑ t : Fin s.card, inner ℝ (T (b ((s.equivFin.symm t).val)))
          (b ((s.equivFin.symm t).val)) := by
        calc ∑ i ∈ s, CT (b i) (b i) = ∑ i : ↥s, CT (b i.val) (b i.val) :=
              (Finset.sum_coe_sort s (fun i => CT (b i) (b i))).symm
          _ = ∑ t : Fin s.card, CT (b ((s.equivFin.symm t).val)) (b ((s.equivFin.symm t).val)) :=
              (Equiv.sum_comp (s.equivFin.symm) (fun i : ↥s => CT (b i.val) (b i.val))).symm
          _ = _ := Finset.sum_congr rfl fun t _ => hCTa _ _
      rw [h4]; exact h3
  refine ⟨htc, le_antisymm ?_ ?_⟩
  · -- upper bound
    obtain ⟨U, hUT, hUn⟩ := polar_contraction hT (S₁.comp S₂) (fun x => hBT x)
    refine Real.iSup_le (fun p => ?_) (traceNormForm_nonneg _)
    set m := p.1.1 with hm
    set g := p.1.2.1 with hg
    set f := p.1.2.2 with hf
    have hgo : Orthonormal ℝ g := p.2.1
    have hfo : Orthonormal ℝ f := p.2.2
    set v : Fin m → H := fun a => (ContinuousLinearMap.adjoint U) (g a) with hv
    have hvB : ∀ x, ∑ a, inner ℝ (v a) x ^ 2 ≤ ‖x‖ ^ 2 := by
      intro x
      have : ∀ a, inner ℝ (v a) x = inner ℝ (g a) (U x) := fun a => by
        simp only [hv]; rw [ContinuousLinearMap.adjoint_inner_left]
      simp only [this]
      exact (bessel_orthonormal g hgo (U x)).trans (by gcongr; exact hUn x)
    set τ := traceNormForm CT with hτ
    have hS1 : ∑ a, CT (v a) (v a) ≤ τ := bessel_trace_le htc v hvB
    have hS2 : ∑ a, CT (f a) (f a) ≤ τ := bessel_trace_le htc f (bessel_orthonormal f hfo)
    have hterm : ∀ a, |F (g a) (f a)| ≤ Real.sqrt (CT (v a) (v a)) * Real.sqrt (CT (f a) (f a)) := by
      intro a
      have e1 : F (g a) (f a) = CT (v a) (f a) := by
        rw [hFa, hCTa]
        calc inner ℝ (S₂ (S₁ (g a))) (f a) = inner ℝ (g a) (S₁ (S₂ (f a))) := by
              rw [h2.symm, h1.symm]
          _ = inner ℝ (g a) (U (T (f a))) := by rw [hUT]; rfl
          _ = inner ℝ (v a) (T (f a)) := by
              simp only [hv]; rw [ContinuousLinearMap.adjoint_inner_left]
          _ = inner ℝ (T (v a)) (f a) := (hT.symm (v a) (f a)).symm
      rw [e1]
      have := hT.cs (v a) (f a)
      rw [← hCTa, ← hCTa, ← hCTa] at this
      rw [← Real.sqrt_mul (by rw [hCTa]; exact hT.nonneg _)]
      exact Real.abs_le_sqrt this
    calc ∑ a, |F (g a) (f a)| ≤ ∑ a, Real.sqrt (CT (v a) (v a)) * Real.sqrt (CT (f a) (f a)) :=
          Finset.sum_le_sum fun a _ => hterm a
      _ ≤ Real.sqrt (∑ a, CT (v a) (v a)) * Real.sqrt (∑ a, CT (f a) (f a)) := by
          have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun a => Real.sqrt (CT (v a) (v a)))
            (fun a => Real.sqrt (CT (f a) (f a)))
          simpa [Real.sq_sqrt, hCTa, hT.nonneg] using this
      _ ≤ Real.sqrt τ * Real.sqrt τ := by
          gcongr
      _ = τ := Real.mul_self_sqrt (traceNormForm_nonneg _)
  · -- lower bound
    refine Real.iSup_le (fun p => ?_) hN0
    set m := p.1.1 with hm
    set g := p.1.2.1 with hg
    set f := p.1.2.2 with hf
    have hgo : Orthonormal ℝ g := p.2.1
    have hfo : Orthonormal ℝ f := p.2.2
    have hg' := hlow g hgo
    have hf' := hlow f hfo
    calc ∑ a, |CT (g a) (f a)| ≤ ∑ a, (1 / 2) * (inner ℝ (T (g a)) (g a) + inner ℝ (T (f a)) (f a)) := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [hCTa]
          have := hT.cs (g a) (f a)
          have hg0 := hT.nonneg (g a)
          have hf0 := hT.nonneg (f a)
          rw [abs_le]
          constructor <;> nlinarith [sq_nonneg (inner ℝ (T (g a)) (g a) - inner ℝ (T (f a)) (f a)),
            abs_nonneg (inner ℝ (T (g a)) (f a)), sq_abs (inner ℝ (T (g a)) (f a)),
            le_abs_self (inner ℝ (T (g a)) (f a)), neg_abs_le (inner ℝ (T (g a)) (f a))]
      _ = (1 / 2) * (∑ a, inner ℝ (T (g a)) (g a) + ∑ a, inner ℝ (T (f a)) (f a)) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ N := by linarith

end TN

end HRS.Uniform.Q07c
