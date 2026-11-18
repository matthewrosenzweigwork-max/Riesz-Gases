import HRS.Uniform.Q07cAux2

/-!
# Q07c, part 3: the tight-frame identity for an orthonormal family of sequences
-/

noncomputable section

open HRS
open MeasureTheory Filter Topology HRS.HilbertCLTAux
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q07c

section Frame

open Classical

variable {α ι : Type*}

/-- If `(ψ_j)` is an orthonormal family in `ℓ²(α)` (given by `HasSum` identities), then
`c ↦ (∑_j ψ_j(a) c_j)_a` is an isometry `ℓ²(ι) → ℓ²(α)`. -/
theorem frame_identity (ψ : ι → α → ℝ)
    (ho : ∀ i j, HasSum (fun a => ψ i a * ψ j a) (if i = j then (1 : ℝ) else 0))
    {c : ι → ℝ} (hc : Summable fun j => c j ^ 2) :
    (∀ a, HasSum (fun j => ψ j a * c j) (∑' j, ψ j a * c j)) ∧
      HasSum (fun a => (∑' j, ψ j a * c j) ^ 2) (∑' j, c j ^ 2) := by
  classical
  have hmem : ∀ j, Memℓp (ψ j) 2 := fun j => by
    refine memℓp_gen ?_
    have := (ho j j).summable
    simpa [Real.rpow_two, sq] using this
  set E := lp (fun _ : α => ℝ) 2 with hE
  set ψE : ι → E := fun j => ⟨ψ j, hmem j⟩ with hψE
  have hv : Orthonormal ℝ ψE := by
    rw [orthonormal_iff_ite]
    intro i j
    have h1 : inner ℝ (ψE i) (ψE j) = ∑' a, ψ i a * ψ j a := by
      rw [lp.inner_eq_tsum]
      refine tsum_congr fun a => ?_
      simp [hψE, mul_comm]
    rw [h1, (ho i j).tsum_eq]
  have hcm : Memℓp c 2 := by
    refine memℓp_gen ?_
    simpa [Real.rpow_two, sq] using hc
  set f : lp (fun _ : ι => ℝ) 2 := ⟨c, hcm⟩ with hf
  set L := hv.orthogonalFamily.linearIsometry with hL
  have hsum := hv.orthogonalFamily.hasSum_linearIsometry f
  -- coordinates
  have hcoord : ∀ a, HasSum (fun j => ψ j a * c j) ((L f) a) := by
    intro a
    have := hsum.mapL (innerSL ℝ (lp.single 2 a (1 : ℝ)))
    convert this using 1
    · funext j
      simp [hψE, hf, LinearIsometry.toSpanSingleton_apply, lp.inner_single_left, mul_comm]
    · simp [lp.inner_single_left]; rfl
  have hsq : ∀ (g : lp (fun _ : ι => ℝ) 2), HasSum (fun b => (g b) ^ 2) (‖g‖ ^ 2) := by
    intro g
    have h1 := lp.hasSum_norm (p := 2) (by norm_num) g
    simpa [Real.rpow_two, sq_abs] using h1
  have hsqα : ∀ (g : lp (fun _ : α => ℝ) 2), HasSum (fun b => (g b) ^ 2) (‖g‖ ^ 2) := by
    intro g
    have h1 := lp.hasSum_norm (p := 2) (by norm_num) g
    simpa [Real.rpow_two, sq_abs] using h1
  have hn : ‖L f‖ ^ 2 = ∑' j, c j ^ 2 := by
    have e1 : ‖L f‖ = ‖f‖ := L.norm_map f
    rw [e1]
    have h := (hsq f).tsum_eq
    simpa [hf] using h.symm
  refine ⟨fun a => by rw [(hcoord a).tsum_eq]; exact hcoord a, ?_⟩
  have h2 := hsqα (L f)
  rw [hn] at h2
  convert h2 using 2 with a
  rw [(hcoord a).tsum_eq]


lemma rowsum_le_one (ψ : ι → α → ℝ)
    (ho : ∀ i j, HasSum (fun a => ψ i a * ψ j a) (if i = j then (1 : ℝ) else 0)) (a : α) :
    Summable fun j => ψ j a ^ 2 := by
  refine summable_of_sum_le (c := 1) (fun j => sq_nonneg _) (fun F => ?_)
  set s : ℝ := ∑ j ∈ F, ψ j a ^ 2 with hs
  have hc : Summable fun j => (if j ∈ F then ψ j a else 0) ^ 2 :=
    summable_of_ne_finset_zero (s := F) fun j hj => by simp [hj]
  obtain ⟨-, h2⟩ := frame_identity ψ ho hc
  have h3 := le_hasSum h2 a (fun _ _ => sq_nonneg _)
  have e1 : ∑' j, ψ j a * (if j ∈ F then ψ j a else 0) = s := by
    rw [tsum_eq_sum (s := F) (fun j hj => by simp [hj])]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp [hj, sq]
  have e2 : ∑' j, (if j ∈ F then ψ j a else 0) ^ 2 = s := by
    rw [tsum_eq_sum (s := F) (fun j hj => by simp [hj])]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp [hj]
  rw [e1, e2] at h3
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => sq_nonneg _
  nlinarith

end Frame

section Polar

open Classical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ιe κ : Type*} [Countable κ] (e : HilbertBasis ιe ℝ H)

/-- `Ψ̃_a = ∑_j ψ_j(a) e_j`. -/
def PsiVec (ψ : ιe → κ ⊕ ιe → ℝ) (a : κ ⊕ ιe) : H := pcVec e (fun j => ψ j a)

variable {e}
variable {ψ : ιe → κ ⊕ ιe → ℝ}
  (ho : ∀ i j, HasSum (fun a => ψ i a * ψ j a) (if i = j then (1 : ℝ) else 0))
include ho

lemma psiVec_frame (x : H) : HasSum (fun a => inner ℝ (PsiVec e ψ a) x ^ 2) (‖x‖ ^ 2) := by
  classical
  have hs := RelCov.hasSum_sq_inner e x
  have hrow := rowsum_le_one ψ ho
  obtain ⟨-, h2⟩ := frame_identity ψ ho hs.summable
  have e1 : ∀ a, inner ℝ (PsiVec e ψ a) x = ∑' j, ψ j a * inner ℝ (e j) x := fun a =>
    (pcVec_hasSum_inner e (hrow a) x).tsum_eq.symm
  simp only [e1]
  rw [← hs.tsum_eq]
  exact h2

lemma psiVec_frame_hs {R : H →L[ℝ] H} (hR : ∀ x y, inner ℝ (R x) y = inner ℝ x (R y))
    (hHS : Summable fun i => ‖R (e i)‖ ^ 2) :
    HasSum (fun a => ‖R (PsiVec e ψ a)‖ ^ 2) (∑' i, ‖R (e i)‖ ^ 2) := by
  have hrow : ∀ i, HasSum (fun a => inner ℝ (PsiVec e ψ a) (R (e i)) ^ 2) (‖R (e i)‖ ^ 2) :=
    fun i => psiVec_frame ho _
  have hsum : Summable (fun p : ιe × (κ ⊕ ιe) => inner ℝ (PsiVec e ψ p.2) (R (e p.1)) ^ 2) := by
    rw [summable_prod_of_nonneg (fun p => sq_nonneg _)]
    exact ⟨fun i => (hrow i).summable, by simpa [(hrow _).tsum_eq] using hHS⟩
  have hcol : ∀ a, HasSum (fun i => inner ℝ (PsiVec e ψ a) (R (e i)) ^ 2)
      (‖R (PsiVec e ψ a)‖ ^ 2) := fun a => by
    have := RelCov.hasSum_sq_inner e (R (PsiVec e ψ a))
    convert this using 2 with i
    rw [← hR, real_inner_comm]
  have hsw : Summable (fun p : (κ ⊕ ιe) × ιe => inner ℝ (PsiVec e ψ p.1) (R (e p.2)) ^ 2) :=
    hsum.prod_symm
  have h1 := hsw.hasSum.prod_fiberwise (fun a => (hsw.prod_factor a).hasSum)
  have h2 : ∑' p : (κ ⊕ ιe) × ιe, inner ℝ (PsiVec e ψ p.1) (R (e p.2)) ^ 2 =
      ∑' i, ‖R (e i)‖ ^ 2 := by
    have h3 := (Equiv.prodComm (κ ⊕ ιe) ιe).tsum_eq
      (fun p : ιe × (κ ⊕ ιe) => inner ℝ (PsiVec e ψ p.2) (R (e p.1)) ^ 2)
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap] at h3
    rw [h3, hsum.tsum_prod' (fun i => (hrow i).summable)]
    exact tsum_congr fun i => (hrow i).tsum_eq
  rw [h2] at h1
  convert h1 using 1
  funext a
  exact ((hcol a).tsum_eq).symm


variable {Sb T : H →L[ℝ] H} {Φ : κ → H}

lemma psiVec_T (hT : IsPSDOp T)
    (hx : ∀ x a, HasSum (fun j => inner ℝ (T (e j)) x * ψ j a)
      (Sum.elim (fun k => inner ℝ (Sb (Φ k)) x) (fun _ => (0 : ℝ)) a)) (a : κ ⊕ ιe) :
    T (PsiVec e ψ a) = Sb (Sum.elim Φ (fun _ => 0) a) := by
  refine ext_inner_right ℝ fun x => ?_
  have h1 : HasSum (fun i => ψ i a * inner ℝ (e i) (T x)) (inner ℝ (PsiVec e ψ a) (T x)) :=
    pcVec_hasSum_inner e (rowsum_le_one ψ ho a) (T x)
  have h2 : HasSum (fun j => inner ℝ (T (e j)) x * ψ j a) (inner ℝ (PsiVec e ψ a) (T x)) := by
    convert h1 using 2 with j
    rw [hT.symm, mul_comm]
  rw [hT.symm, h2.unique (hx x a)]
  rcases a with k | l <;> simp

/-- The difference integrand `Z_a = Φ̂_a - Sb Ψ̃_a`. -/
def ZVec (Sb : H →L[ℝ] H) (Φ : κ → H) (ψ : ιe → κ ⊕ ιe → ℝ) (a : κ ⊕ ιe) : H :=
  Sum.elim Φ (fun _ => (0 : H)) a - Sb (PsiVec e ψ a)

omit ho in
lemma tsum_diag_eq_traceNormForm {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) :
    ∑' i, C (e i) (e i) = traceNormForm C :=
  le_antisymm (hC.tsum_basis_le e) ((traceNormForm_le_basis_trace hC e).trans (le_of_eq rfl))

theorem cross_trace (hT : IsPSDOp T) (hSb : IsPSDOp Sb)
    (hx : ∀ x a, HasSum (fun j => inner ℝ (T (e j)) x * ψ j a)
      (Sum.elim (fun k => inner ℝ (Sb (Φ k)) x) (fun _ => (0 : ℝ)) a))
    (hΦ : Summable fun k => ‖Φ k‖ ^ 2) (hHS : Summable fun i => ‖Sb (e i)‖ ^ 2)
    (htc : IsTraceClassCov ((innerSL ℝ).comp T)) :
    HasSum (fun a => ‖ZVec (e := e) Sb Φ ψ a‖ ^ 2)
      (∑' k, ‖Φ k‖ ^ 2 + ∑' i, ‖Sb (e i)‖ ^ 2 - 2 * traceNormForm ((innerSL ℝ).comp T)) := by
  have H1 : HasSum (fun a : κ ⊕ ιe => ‖Sum.elim Φ (fun _ => (0 : H)) a‖ ^ 2) (∑' k, ‖Φ k‖ ^ 2) := by
    have := HasSum.sum (f := fun a : κ ⊕ ιe => ‖Sum.elim Φ (fun _ => (0 : H)) a‖ ^ 2)
      (a := ∑' k, ‖Φ k‖ ^ 2) (b := 0) (by exact hΦ.hasSum)
      (by convert (hasSum_zero : HasSum (fun _ : ιe => (0 : ℝ)) 0) using 1; funext l; simp)
    simpa using this
  have H2 := psiVec_frame_hs ho hSb.symm hHS
  obtain ⟨R0, hR0⟩ := RelCov.exists_isSqrtOfForm htc
  have hHS0 : Summable fun i => ‖R0 (e i)‖ ^ 2 := RelCov.summable_sqrt_diag e hR0 htc
  have H3 := psiVec_frame_hs ho hR0.symm hHS0
  have e3 : ∀ a, ‖R0 (PsiVec e ψ a)‖ ^ 2 = inner ℝ (T (PsiVec e ψ a)) (PsiVec e ψ a) := fun a => by
    rw [← real_inner_self_eq_norm_sq, hR0.sq]; try simp
  have e4 : ∑' i, ‖R0 (e i)‖ ^ 2 = traceNormForm ((innerSL ℝ).comp T) := by
    rw [← tsum_diag_eq_traceNormForm (e := e) htc]
    refine tsum_congr fun i => ?_
    rw [← real_inner_self_eq_norm_sq, hR0.sq]; try simp
  simp only [e3, e4] at H3
  have H4 := (H1.add H2).sub (H3.mul_left 2)
  convert H4 using 1
  funext a
  have h5 : inner ℝ (Sum.elim Φ (fun _ => (0 : H)) a) (Sb (PsiVec e ψ a)) =
      inner ℝ (T (PsiVec e ψ a)) (PsiVec e ψ a) := by
    rw [← hSb.symm, ← psiVec_T ho hT hx a]
  unfold ZVec
  rw [norm_sub_sq_real, h5]
  ring


omit ho in
lemma summable_norm_sq_comp (hΦ : Summable fun k => ‖Φ k‖ ^ 2) :
    Summable fun k => ‖Sb (Φ k)‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) (hΦ.mul_left (‖Sb‖ ^ 2))
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (Sb.le_opNorm _) 2

omit ho in
/-- Along the polar family, `∑_a ‖Z_a‖² = 𝔟(C, D)²` when `C = ΦΦ*` and `Sb = D^{1/2}`. -/
theorem sum_norm_ZVec_eq_bures2 {D : H →L[ℝ] H →L[ℝ] ℝ} (hD : IsTraceClassCov D)
    (hSbD : IsSqrtOfForm Sb D) (hΦ : Summable fun k => ‖Φ k‖ ^ 2)
    (hT : IsSqrtOfForm T (hsCovForm fun k => Sb (Φ k)))
    (ho : ∀ i j, HasSum (fun a => ψ i a * ψ j a) (if i = j then (1 : ℝ) else 0))
    (hx : ∀ x a, HasSum (fun j => inner ℝ (T (e j)) x * ψ j a)
      (Sum.elim (fun k => inner ℝ (Sb (Φ k)) x) (fun _ => (0 : ℝ)) a)) :
    HasSum (fun a => ‖ZVec (e := e) Sb Φ ψ a‖ ^ 2) (Uniform.bures2 (hsCovForm Φ) D) := by
  have hCtc : IsTraceClassCov (hsCovForm Φ) := isTraceClassCov_hsCovForm hΦ
  have hSbpsd : IsPSDOp Sb := ⟨hSbD.symm, hSbD.nonneg⟩
  have hTpsd : IsPSDOp T := ⟨hT.symm, hT.nonneg⟩
  have hS1 := Uniform.RelCov.formSqrt_spec hCtc
  have hS2 : Uniform.formSqrt D = Sb := sqrt_unique (Uniform.RelCov.formSqrt_spec hD) hSbD
  set S₁ := Uniform.formSqrt (hsCovForm Φ) with hS₁
  have hS1psd : IsPSDOp S₁ := ⟨hS1.symm, hS1.nonneg⟩
  have hA : Summable fun j => ‖S₁ (e j)‖ ^ 2 := Uniform.RelCov.summable_sqrt_diag e hS1 hCtc
  have hB : Summable fun j => ‖Sb (e j)‖ ^ 2 := Uniform.RelCov.summable_sqrt_diag e hSbD hD
  have hsΘ := summable_norm_sq_comp (Sb := Sb) hΦ
  have hBT : ∀ x, ‖S₁ (Sb x)‖ = ‖T x‖ := by
    intro x
    have h1 : ‖T x‖ ^ 2 = ∑' k, inner ℝ (Sb (Φ k)) x * inner ℝ (Sb (Φ k)) x := by
      rw [← real_inner_self_eq_norm_sq, hT.sq, hsCovForm_apply hsΘ]
    have h2 : ‖S₁ (Sb x)‖ ^ 2 = ∑' k, inner ℝ (Sb (Φ k)) x * inner ℝ (Sb (Φ k)) x := by
      rw [← real_inner_self_eq_norm_sq, hS1.sq, hsCovForm_apply hΦ]
      refine tsum_congr fun k => ?_
      rw [hSbD.symm (Φ k) x]
    have := h1.trans h2.symm
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this.symm
  obtain ⟨htc, hTN⟩ := trace_norm_prod hS1psd hSbpsd hTpsd hBT e hA hB
  have hcr := cross_trace ho hTpsd hSbpsd hx hΦ hB htc
  have e1 : ∑' k, ‖Φ k‖ ^ 2 = traceNormForm (hsCovForm Φ) := by
    rw [← tsum_diag_eq_traceNormForm (e := e) hCtc, ← (hasSum_diag_decomp hΦ e).tsum_eq]
    refine tsum_congr fun i => ?_
    rw [hsCovForm_apply hΦ]
    exact tsum_congr fun k => sq _
  have e2 : ∑' i, ‖Sb (e i)‖ ^ 2 = traceNormForm D := by
    rw [← tsum_diag_eq_traceNormForm (e := e) hD]
    refine tsum_congr fun i => ?_
    rw [← real_inner_self_eq_norm_sq, hSbD.sq]
  unfold Uniform.bures2
  rw [hS2]
  rw [e1, e2, ← hTN] at hcr
  exact hcr

end Polar

end HRS.Uniform.Q07c
