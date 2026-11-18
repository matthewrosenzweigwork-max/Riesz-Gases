import HRS.MS.Fp81S21WickG12

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

private theorem fp81s21_wickG_kernel_rearrange
    {d m q : ℕ} (c : Fin m → Fin m → ℝ)
    (M : Fin m → Fin q → ℝ) (e : Fin q → Euc d → ℝ)
    (x y : Euc d) :
    ∑ i, ∑ j, c i j *
        ((∑ a, M i a * e a x) * (∑ b, M j b * e b y)) =
      ∑ a, ∑ b, (∑ i, ∑ j, c i j * M i a * M j b) * e a x * e b y := by
  classical
  calc
    ∑ i, ∑ j, c i j *
        ((∑ a, M i a * e a x) * (∑ b, M j b * e b y)) =
      ∑ i, ∑ j, ∑ a, ∑ b,
        c i j * M i a * M j b * e a x * e b y := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_mul_sum]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          ring
    _ = ∑ a, ∑ b, ∑ i, ∑ j,
        c i j * M i a * M j b * e a x * e b y := by
          calc
            ∑ i, ∑ j, ∑ a, ∑ b,
                c i j * M i a * M j b * e a x * e b y =
              ∑ i, ∑ a, ∑ j, ∑ b,
                c i j * M i a * M j b * e a x * e b y := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [Finset.sum_comm]
            _ = ∑ a, ∑ i, ∑ j, ∑ b,
                c i j * M i a * M j b * e a x * e b y := by
                  rw [Finset.sum_comm]
            _ = ∑ a, ∑ i, ∑ b, ∑ j,
                c i j * M i a * M j b * e a x * e b y := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [Finset.sum_comm]
            _ = ∑ a, ∑ b, ∑ i, ∑ j,
                c i j * M i a * M j b * e a x * e b y := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, (∑ i, ∑ j, c i j * M i a * M j b) * e a x * e b y := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          simp only [Finset.sum_mul]

/-- The finite-rank kernel is an orthonormal tensor expansion in the span of
its inputs.  This gives its exact product-space `L²` norm. -/
theorem fp81s21_wickG_kernel_orthonormal_coordinates
    {d m : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c : Fin m → Fin m → ℝ) :
    ∃ q : ℕ, ∃ e : Fin q → Lp ℝ 2 μ, ∃ M : Fin m → Fin q → ℝ,
      Orthonormal ℝ e ∧
      (∀ i, (hu i).toLp (u i) = ∑ a, M i a • e a) ∧
      MemLp (fun z : Euc d × Euc d => r2FiniteRankKernel c u z.1 z.2)
        2 (μ.prod μ) ∧
      (let d' : Fin q → Fin q → ℝ := fun a b =>
        ∑ i, ∑ j, c i j * M i a * M j b
       (fun z : Euc d × Euc d => r2FiniteRankKernel c u z.1 z.2) =ᵐ[μ.prod μ]
          fun z => ∑ a, ∑ b, d' a b * (e a) z.1 * (e b) z.2) ∧
      ∫ z : Euc d × Euc d, (r2FiniteRankKernel c u z.1 z.2) ^ 2 ∂(μ.prod μ) =
        ∑ a, ∑ b,
          (∑ i, ∑ j, c i j * M i a * M j b) ^ 2 := by
  classical
  let f : Fin m → Lp ℝ 2 μ := fun i => (hu i).toLp (u i)
  obtain ⟨q, e, M, he, hdecomp⟩ :=
    fp81s21_wickG_span_orthonormal_decomposition f
  let d' : Fin q → Fin q → ℝ := fun a b =>
    ∑ i, ∑ j, c i j * M i a * M j b
  have hdecompAE : ∀ i, u i =ᵐ[μ] fun x => ∑ a, M i a * (e a) x := by
    intro i
    have hclass : f i =ᵐ[μ] (∑ a, M i a • e a : Lp ℝ 2 μ) := by
      filter_upwards [ae_of_all μ fun x =>
        congrFun (congrArg (fun z : Lp ℝ 2 μ => (z : Euc d → ℝ)) (hdecomp i)) x]
        with x hx
      exact hx
    have hsum : (∑ a : Fin q, M i a • e a : Lp ℝ 2 μ) =ᵐ[μ]
        fun x => ∑ a, M i a * (e a) x := by
      have h1 : (∑ a : Fin q, M i a • e a : Lp ℝ 2 μ) =ᵐ[μ]
          fun x => ∑ a, (M i a • e a : Lp ℝ 2 μ) x := by
        simpa using HRS.A33.a33_coeFn_sum (P := μ) Finset.univ
          (fun a => M i a • e a)
      have h2 : ∀ᵐ x ∂μ, ∀ a : Fin q,
          (M i a • e a : Lp ℝ 2 μ) x = M i a * (e a) x := by
        rw [ae_all_iff]
        intro a
        filter_upwards [Lp.coeFn_smul (M i a) (e a)] with x hx
        simpa [smul_eq_mul] using hx
      filter_upwards [h1, h2] with x hx hxA
      rw [hx]
      exact Finset.sum_congr rfl fun a _ => hxA a
    have huLp : f i =ᵐ[μ] u i := (hu i).coeFn_toLp
    filter_upwards [huLp.symm, hclass, hsum] with x hx hx' hx''
    exact hx.trans (hx'.trans hx'')
  have hfst : ∀ i, (fun z : Euc d × Euc d => u i z.1) =ᵐ[μ.prod μ]
      fun z => ∑ a, M i a * (e a) z.1 := by
    intro i
    exact (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq_comp
      (hdecompAE i)
  have hsnd : ∀ i, (fun z : Euc d × Euc d => u i z.2) =ᵐ[μ.prod μ]
      fun z => ∑ a, M i a * (e a) z.2 := by
    intro i
    exact (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq_comp
      (hdecompAE i)
  have hkernel : (fun z : Euc d × Euc d => r2FiniteRankKernel c u z.1 z.2) =ᵐ[μ.prod μ]
      fun z => ∑ a, ∑ b, d' a b * (e a) z.1 * (e b) z.2 := by
    filter_upwards [ae_all_iff.mpr fun i => hfst i,
      ae_all_iff.mpr fun j => hsnd j] with z hxi hxj
    unfold r2FiniteRankKernel
    calc
      ∑ i, ∑ j, c i j * u i z.1 * u j z.2 =
        ∑ i, ∑ j, c i j *
          ((∑ a, M i a * (e a) z.1) * (∑ b, M j b * (e b) z.2)) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [hxi i, hxj j]
            ring
      _ = ∑ a, ∑ b, d' a b * (e a) z.1 * (e b) z.2 := by
            simpa [d'] using fp81s21_wickG_kernel_rearrange c M
              (fun a x => (e a) x) z.1 z.2
  obtain ⟨hKmem, hKint⟩ := fp81s21_wickG_orthonormal_tensor_norm e he d'
  have hmem : MemLp (fun z : Euc d × Euc d => r2FiniteRankKernel c u z.1 z.2)
      2 (μ.prod μ) := (memLp_congr_ae hkernel).2 hKmem
  have hint : ∫ z : Euc d × Euc d, (r2FiniteRankKernel c u z.1 z.2) ^ 2 ∂(μ.prod μ) =
      ∑ a, ∑ b, d' a b ^ 2 := by
    calc
      ∫ z : Euc d × Euc d, (r2FiniteRankKernel c u z.1 z.2) ^ 2 ∂(μ.prod μ) =
          ∫ z : Euc d × Euc d, (∑ a, ∑ b, d' a b * (e a) z.1 * (e b) z.2) ^ 2 ∂(μ.prod μ) := by
            apply integral_congr_ae
            exact hkernel.mono fun z hz => congrArg (fun r : ℝ => r ^ 2) hz
      _ = ∑ a, ∑ b, d' a b ^ 2 := hKint
  refine ⟨q, e, M, he, hdecomp, hmem, ?_, ?_⟩
  · simpa [d'] using hkernel
  · simpa [d'] using hint

#print axioms fp81s21_wickG_kernel_orthonormal_coordinates

end HRS.Fp81.S21

end
