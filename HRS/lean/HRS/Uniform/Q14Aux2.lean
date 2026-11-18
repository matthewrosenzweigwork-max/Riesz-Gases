import HRS.Uniform.Q14Aux1
import HRS.Uniform.Q07cAux7

/-!
# Q14, part 2: the cross term of a coupling is dominated by `‖D^{1/2} C^{1/2}‖₁`
-/

noncomputable section

open HRS
open MeasureTheory Filter Topology HRS.HilbertCLTAux
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q14

section Cross

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem q14_cross_le {ι : Type} (e : HilbertBasis ι ℝ H) {R S W : H →L[ℝ] H} (hR : IsPSDOp R)
    (hS : IsPSDOp S) (hRs : Summable fun i => ‖R (e i)‖ ^ 2) (hSs : Summable fun i => ‖S (e i)‖ ^ 2)
    (hW : ∀ x, ‖W x‖ ≤ ‖x‖) :
    Summable (fun j => inner ℝ (W (R (e j))) (S (e j))) ∧
      ∑' j, inner ℝ (W (R (e j))) (S (e j)) ≤
        traceNormForm ((innerSL ℝ).comp (S.comp R)) := by
  classical
  -- the form `⟨R S x, R S y⟩`
  set F₀ : H →L[ℝ] H →L[ℝ] ℝ :=
    (innerSL ℝ).comp ((ContinuousLinearMap.adjoint (R.comp S)).comp (R.comp S)) with hF₀
  have hF₀a : ∀ x y, F₀ x y = inner ℝ (R (S x)) (R (S y)) := fun x y => by
    simp only [hF₀, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    rw [ContinuousLinearMap.adjoint_inner_left]; rfl
  have hF₀tc : IsTraceClassCov F₀ := by
    refine ⟨fun x y => ?_, fun x => ?_, ⟨ι, e, ?_⟩⟩
    · rw [hF₀a, hF₀a, real_inner_comm]
    · rw [hF₀a]; exact real_inner_self_nonneg
    · refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
        (hSs.mul_left (‖R‖ ^ 2))
      · rw [hF₀a]; exact real_inner_self_nonneg
      · rw [hF₀a, real_inner_self_eq_norm_sq, ← mul_pow]
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        exact R.le_opNorm _
  have hTs := Uniform.RelCov.formSqrt_spec hF₀tc
  set T := Uniform.formSqrt F₀ with hT
  have hTpsd : IsPSDOp T := ⟨hTs.symm, hTs.nonneg⟩
  have hBT : ∀ x, ‖R (S x)‖ = ‖T x‖ := by
    intro x
    have h1 : ‖T x‖ ^ 2 = ‖R (S x)‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hTs.sq, hF₀a, real_inner_self_eq_norm_sq]
    exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1).symm
  obtain ⟨htc, hN⟩ := Q07c.trace_norm_prod hR hS hTpsd hBT e hRs hSs
  rw [hN]
  -- the square root `Y` of `T`
  have hYs := Uniform.RelCov.formSqrt_spec htc
  set Y := Uniform.formSqrt ((innerSL ℝ).comp T) with hY
  have hYsum : Summable fun i => ‖Y (e i)‖ ^ 2 := Uniform.RelCov.summable_sqrt_diag e hYs htc
  have hYtr : ∑' i, ‖Y (e i)‖ ^ 2 ≤ traceNormForm ((innerSL ℝ).comp T) := by
    refine le_trans (le_of_eq ?_) (htc.tsum_basis_le e)
    exact tsum_congr fun i => Uniform.RelCov.sq_norm_eq_diag hYs _
  -- polar decomposition of `R S = U T`
  obtain ⟨U, hUT, hUn⟩ := Q07c.polar_contraction hTpsd (R.comp S) (fun x => hBT x)
  -- cyclicity
  have hWR : Summable fun i => ‖(W.comp R) (e i)‖ ^ 2 := (q14_hs_comp_left e hRs hW).1
  obtain ⟨c1, c2, c3⟩ := q14_trace_cyc e hSs hWR
  -- rewrite the left side
  have hL : ∀ j, inner ℝ (S ((W.comp R) (e j))) (e j) = inner ℝ (W (R (e j))) (S (e j)) := fun j => by
    rw [hS.symm]; rfl
  simp only [hL] at c1 c3
  refine ⟨c1, ?_⟩
  rw [c3]
  -- bound each term on the right
  set M : H →L[ℝ] H := ContinuousLinearMap.adjoint (W.comp U) with hM
  have hMc : ∀ x, ‖M x‖ ≤ ‖x‖ :=
    q14_adj_contr (fun x => by
      simp only [ContinuousLinearMap.comp_apply]
      exact (hW _).trans (hUn x))
  have hterm : ∀ i, inner ℝ ((W.comp R) (S (e i))) (e i) = inner ℝ (Y (e i)) (Y (M (e i))) := by
    intro i
    have h1 : (W.comp R) (S (e i)) = (W.comp U) (T (e i)) := by
      simp only [ContinuousLinearMap.comp_apply]; rw [hUT]; rfl
    rw [h1, ← ContinuousLinearMap.adjoint_inner_right, hYs.sq]
    rfl
  obtain ⟨h4, h5⟩ := q14_hs_comp_right e hYsum hMc
  have hbd : ∀ i, inner ℝ (Y (e i)) (Y (M (e i))) ≤
      (1 / 2) * (‖Y (e i)‖ ^ 2 + ‖Y (M (e i))‖ ^ 2) := fun i => by
    have := real_inner_le_norm (Y (e i)) (Y (M (e i)))
    nlinarith [sq_nonneg (‖Y (e i)‖ - ‖Y (M (e i))‖)]
  have hsb : Summable fun i => (1 / 2) * (‖Y (e i)‖ ^ 2 + ‖Y (M (e i))‖ ^ 2) :=
    (hYsum.add h4).mul_left _
  calc ∑' i, inner ℝ ((W.comp R) (S (e i))) (e i)
      = ∑' i, inner ℝ (Y (e i)) (Y (M (e i))) := tsum_congr hterm
    _ ≤ ∑' i, (1 / 2) * (‖Y (e i)‖ ^ 2 + ‖Y (M (e i))‖ ^ 2) := by
        refine Summable.tsum_le_tsum hbd ?_ hsb
        exact c2.congr hterm
    _ = (1 / 2) * (∑' i, ‖Y (e i)‖ ^ 2 + ∑' i, ‖Y (M (e i))‖ ^ 2) := by
        rw [tsum_mul_left, hYsum.tsum_add h4]
    _ ≤ (1 / 2) * (∑' i, ‖Y (e i)‖ ^ 2 + ∑' i, ‖Y (e i)‖ ^ 2) := by gcongr
    _ = ∑' i, ‖Y (e i)‖ ^ 2 := by ring
    _ ≤ _ := hYtr

end Cross

section Factor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

lemma q14_polar_contr {S : H →L[ℝ] H} (hS : IsPSDOp S) (T : H →L[ℝ] K) (hT : ∀ x, ‖T x‖ = ‖S x‖) :
    ∃ U : H →L[ℝ] K, (∀ x, U (S x) = T x) ∧ ∀ x, ‖U x‖ ≤ ‖x‖ := by
  obtain ⟨U, Q, -, -, hsym, hid, -, hUS, hUQ⟩ := exists_polar hS T hT
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

/-- `𝔟(C,D)² ≤ Tr C + Tr D - 2 ∑_j ⟨A e_j, B e_j⟩` for every pair of factorisations `C = A*A`, `D = B*B`
through a common Hilbert space. -/
theorem q14_bures2_le {ι : Type} (e : HilbertBasis ι ℝ H) {C D : H →L[ℝ] H →L[ℝ] ℝ}
    (hC : IsTraceClassCov C) (hD : IsTraceClassCov D) (A B : H →L[ℝ] K)
    (hA : ∀ x y, inner ℝ (A x) (A y) = C x y) (hB : ∀ x y, inner ℝ (B x) (B y) = D x y) :
    Uniform.bures2 C D ≤ traceNormForm C + traceNormForm D -
      2 * ∑' j, inner ℝ (A (e j)) (B (e j)) := by
  classical
  have hRs := Uniform.RelCov.formSqrt_spec hC
  have hSs := Uniform.RelCov.formSqrt_spec hD
  set R := Uniform.formSqrt C with hR
  set S := Uniform.formSqrt D with hS
  have hRp : IsPSDOp R := ⟨hRs.symm, hRs.nonneg⟩
  have hSp : IsPSDOp S := ⟨hSs.symm, hSs.nonneg⟩
  have hRsum := Uniform.RelCov.summable_sqrt_diag e hRs hC
  have hSsum := Uniform.RelCov.summable_sqrt_diag e hSs hD
  have hnA : ∀ x, ‖A x‖ = ‖R x‖ := fun x => by
    have : ‖A x‖ ^ 2 = ‖R x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hA, ← real_inner_self_eq_norm_sq, hRs.sq]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  have hnB : ∀ x, ‖B x‖ = ‖S x‖ := fun x => by
    have : ‖B x‖ ^ 2 = ‖S x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hB, ← real_inner_self_eq_norm_sq, hSs.sq]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  obtain ⟨U₁, hU₁, hU₁n⟩ := q14_polar_contr hRp A hnA
  obtain ⟨U₂, hU₂, hU₂n⟩ := q14_polar_contr hSp B hnB
  set W : H →L[ℝ] H := (ContinuousLinearMap.adjoint U₂).comp U₁ with hW
  have hWn : ∀ x, ‖W x‖ ≤ ‖x‖ := by
    intro x
    simp only [hW, ContinuousLinearMap.comp_apply]
    have h1 : ‖ContinuousLinearMap.adjoint U₂‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]
      exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
        rw [one_mul]; exact hU₂n y
    calc ‖(ContinuousLinearMap.adjoint U₂) (U₁ x)‖
        ≤ ‖ContinuousLinearMap.adjoint U₂‖ * ‖U₁ x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖x‖ := mul_le_mul h1 (hU₁n x) (norm_nonneg _) zero_le_one
      _ = ‖x‖ := one_mul _
  have hterm : ∀ j, inner ℝ (A (e j)) (B (e j)) = inner ℝ (W (R (e j))) (S (e j)) := by
    intro j
    rw [← hU₁, ← hU₂, hW]
    simp only [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.adjoint_inner_left]
  obtain ⟨-, hle⟩ := q14_cross_le e hRp hSp hRsum hSsum hWn
  have hsum : ∑' j, inner ℝ (A (e j)) (B (e j)) ≤ traceNormForm ((innerSL ℝ).comp (S.comp R)) := by
    rw [tsum_congr hterm]; exact hle
  unfold Uniform.bures2
  linarith

end Factor

end HRS.Uniform.Q14
