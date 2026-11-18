import HRS.Uniform.Q07cAux2

/-!
# Q14, part 1: Hilbert-Schmidt toolkit (adjoint invariance, cyclicity of the trace)
-/

noncomputable section

open HRS
open MeasureTheory Filter Topology HRS.HilbertCLTAux
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q14

section HS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {ι : Type*} (e : HilbertBasis ι ℝ H)

omit [CompleteSpace H] in
lemma q14_hasSum_sq (x : H) : HasSum (fun j => inner ℝ x (e j) ^ 2) (‖x‖ ^ 2) := by
  have h := e.hasSum_inner_mul_inner x x
  rw [real_inner_self_eq_norm_sq] at h
  convert h using 2 with j
  rw [real_inner_comm (e j) x]; ring

lemma q14_hs_adjoint {P : H →L[ℝ] H} (hP : Summable fun i => ‖P (e i)‖ ^ 2) :
    Summable (fun i => ‖(ContinuousLinearMap.adjoint P) (e i)‖ ^ 2) ∧
      ∑' i, ‖(ContinuousLinearMap.adjoint P) (e i)‖ ^ 2 = ∑' i, ‖P (e i)‖ ^ 2 := by
  set a : ι → ι → ℝ := fun i j => inner ℝ (P (e i)) (e j) ^ 2 with ha
  have h1 : ∀ i, HasSum (fun j => a i j) (‖P (e i)‖ ^ 2) := fun i => q14_hasSum_sq e (P (e i))
  have h2 : ∀ j, HasSum (fun i => a i j) (‖(ContinuousLinearMap.adjoint P) (e j)‖ ^ 2) := fun j => by
    have := q14_hasSum_sq e ((ContinuousLinearMap.adjoint P) (e j))
    convert this using 2 with i
    rw [ha]; simp only []
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  have hf : Summable (Function.uncurry a) := by
    refine (summable_prod_of_nonneg (fun p => sq_nonneg _)).2 ⟨fun i => (h1 i).summable, ?_⟩
    exact hP.congr fun i => ((h1 i).tsum_eq).symm
  have hs := hf.prod_symm
  have hsum2 : Summable fun j => ∑' i, a i j := by
    have := (summable_prod_of_nonneg (f := fun p : ι × ι => a p.2 p.1) (fun p => sq_nonneg _)).1 hs
    exact this.2
  refine ⟨?_, ?_⟩
  · simpa [(h2 _).tsum_eq] using hsum2
  · have e1 : ∑' i, ‖P (e i)‖ ^ 2 = ∑' i, ∑' j, a i j := tsum_congr fun i => (h1 i).tsum_eq.symm
    have e2 : ∑' j, ‖(ContinuousLinearMap.adjoint P) (e j)‖ ^ 2 = ∑' j, ∑' i, a i j :=
      tsum_congr fun j => (h2 j).tsum_eq.symm
    rw [e1, e2]
    exact hf.tsum_comm

lemma q14_summable_matrix {P : H →L[ℝ] H} (hP : Summable fun i => ‖P (e i)‖ ^ 2) :
    Summable fun p : ι × ι => inner ℝ (P (e p.1)) (e p.2) ^ 2 := by
  refine (summable_prod_of_nonneg (fun p => sq_nonneg _)).2
    ⟨fun i => (q14_hasSum_sq e (P (e i))).summable, ?_⟩
  exact hP.congr fun i => ((q14_hasSum_sq e (P (e i))).tsum_eq).symm

lemma q14_hs_comp_left {Z P : H →L[ℝ] H} (hP : Summable fun i => ‖P (e i)‖ ^ 2) (hZ : ∀ x, ‖Z x‖ ≤ ‖x‖) :
    Summable (fun i => ‖Z (P (e i))‖ ^ 2) ∧
      ∑' i, ‖Z (P (e i))‖ ^ 2 ≤ ∑' i, ‖P (e i)‖ ^ 2 := by
  have hle : ∀ i, ‖Z (P (e i))‖ ^ 2 ≤ ‖P (e i)‖ ^ 2 := fun i =>
    pow_le_pow_left₀ (norm_nonneg _) (hZ _) 2
  have hs := Summable.of_nonneg_of_le (fun i => sq_nonneg _) hle hP
  exact ⟨hs, hs.tsum_le_tsum hle hP⟩

lemma q14_adj_contr {M : H →L[ℝ] H} (hM : ∀ x, ‖M x‖ ≤ ‖x‖) :
    ∀ x, ‖(ContinuousLinearMap.adjoint M) x‖ ≤ ‖x‖ := by
  intro x
  have h1 : ‖ContinuousLinearMap.adjoint M‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by rw [one_mul]; exact hM y
  simpa using (ContinuousLinearMap.le_opNorm _ x).trans (mul_le_of_le_one_left (norm_nonneg _) h1)

lemma q14_hs_comp_right {Y M : H →L[ℝ] H} (hY : Summable fun i => ‖Y (e i)‖ ^ 2)
    (hM : ∀ x, ‖M x‖ ≤ ‖x‖) :
    Summable (fun i => ‖Y (M (e i))‖ ^ 2) ∧
      ∑' i, ‖Y (M (e i))‖ ^ 2 ≤ ∑' i, ‖Y (e i)‖ ^ 2 := by
  obtain ⟨hYa, hYe⟩ := q14_hs_adjoint e hY
  have hMa := q14_adj_contr hM
  obtain ⟨h1, h2⟩ := q14_hs_comp_left e hYa hMa
  have hcomp : (ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint M ∘L
      ContinuousLinearMap.adjoint Y)) = Y ∘L M := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
      ContinuousLinearMap.adjoint_adjoint]
  have h3 := q14_hs_adjoint e (P := ContinuousLinearMap.adjoint M ∘L ContinuousLinearMap.adjoint Y)
    (by simpa using h1)
  rw [hcomp] at h3
  refine ⟨by simpa using h3.1, ?_⟩
  have h4 : ∑' i, ‖Y (M (e i))‖ ^ 2 =
      ∑' i, ‖(ContinuousLinearMap.adjoint M) ((ContinuousLinearMap.adjoint Y) (e i))‖ ^ 2 := by
    simpa using h3.2
  rw [h4, ← hYe]
  exact h2

lemma q14_trace_cyc {P Q : H →L[ℝ] H} (hP : Summable fun i => ‖P (e i)‖ ^ 2)
    (hQ : Summable fun i => ‖Q (e i)‖ ^ 2) :
    Summable (fun j => inner ℝ (P (Q (e j))) (e j)) ∧
      Summable (fun i => inner ℝ (Q (P (e i))) (e i)) ∧
      ∑' j, inner ℝ (P (Q (e j))) (e j) = ∑' i, inner ℝ (Q (P (e i))) (e i) := by
  set f : ι × ι → ℝ := fun p => inner ℝ (Q (e p.1)) (e p.2) * inner ℝ (P (e p.2)) (e p.1) with hf
  have hrow : ∀ j, HasSum (fun i => f (j, i)) (inner ℝ (P (Q (e j))) (e j)) := by
    intro j
    have := e.hasSum_inner_mul_inner (Q (e j)) ((ContinuousLinearMap.adjoint P) (e j))
    rw [ContinuousLinearMap.adjoint_inner_right] at this
    convert this using 2 with i
    rw [hf]; simp only []
    rw [ContinuousLinearMap.adjoint_inner_right]
  have hcol : ∀ i, HasSum (fun j => f (j, i)) (inner ℝ (Q (P (e i))) (e i)) := by
    intro i
    have := e.hasSum_inner_mul_inner (P (e i)) ((ContinuousLinearMap.adjoint Q) (e i))
    rw [ContinuousLinearMap.adjoint_inner_right] at this
    convert this using 2 with j
    rw [hf]; simp only []
    rw [ContinuousLinearMap.adjoint_inner_right, mul_comm]
  have hsQ := q14_summable_matrix e hQ
  have hsP := q14_summable_matrix e hP
  have hsP' : Summable fun p : ι × ι => inner ℝ (P (e p.2)) (e p.1) ^ 2 :=
    (Equiv.prodComm ι ι).summable_iff.2 hsP
  have hfs : Summable f := by
    refine Summable.of_norm_bounded ((hsQ.add hsP').mul_left (1 / 2)) fun p => ?_
    rw [hf]; simp only [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|inner ℝ (Q (e p.1)) (e p.2)| - |inner ℝ (P (e p.2)) (e p.1)|),
      sq_abs (inner ℝ (Q (e p.1)) (e p.2)), sq_abs (inner ℝ (P (e p.2)) (e p.1))]
  have h1 : Summable fun j => ∑' i, f (j, i) := hfs.prod
  have h2 : Summable fun i => ∑' j, f (j, i) := hfs.prod_symm.prod
  refine ⟨h1.congr fun j => (hrow j).tsum_eq, h2.congr fun i => (hcol i).tsum_eq, ?_⟩
  have e1 : ∑' j, inner ℝ (P (Q (e j))) (e j) = ∑' j, ∑' i, f (j, i) :=
    tsum_congr fun j => (hrow j).tsum_eq.symm
  have e2 : ∑' i, inner ℝ (Q (P (e i))) (e i) = ∑' i, ∑' j, f (j, i) :=
    tsum_congr fun i => (hcol i).tsum_eq.symm
  rw [e1, e2]
  exact (Summable.tsum_comm' (f := fun j i => f (j, i)) hfs (fun j => (hrow j).summable)
    (fun i => (hcol i).summable)).symm

end HS

end HRS.Uniform.Q14
