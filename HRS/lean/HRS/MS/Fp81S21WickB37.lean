import HRS.MS.Fp81S21WickB36

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

/-- Classes admitting a single finite-rank representation. -/
def fp81s21_wickB37_representable {d : ℕ} (μ : Measure (Euc d))
    (k : Lp ℝ 2 (μ.prod μ)) : Prop :=
  ∃ (m : ℕ) (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c : Fin m → Fin m → ℝ)
    (hk : MemLp (fp81s21_wickG_finite_rank_kernel u c) 2 (μ.prod μ)),
    k = hk.toLp (fp81s21_wickG_finite_rank_kernel u c)

/-- The difference of represented classes has a single block representation. -/
theorem fp81s21_wickB37_representable_sub {d : ℕ} {μ : Measure (Euc d)}
    {k₁ k₂ : Lp ℝ 2 (μ.prod μ)}
    (h₁ : fp81s21_wickB37_representable μ k₁)
    (h₂ : fp81s21_wickB37_representable μ k₂) :
    fp81s21_wickB37_representable μ (k₁ - k₂) := by
  obtain ⟨m, u, hu, c, hk, rfl⟩ := h₁
  obtain ⟨n, v, hv, c', hk', rfl⟩ := h₂
  let w := fp81s21_wickB22_concatFunction u v
  let a := fp81s21_wickB22_concatCoeff c c'
  have hw := fp81s21_wickB36_concat_memLp u hu v hv
  have hkernel : fp81s21_wickG_finite_rank_kernel w a =
      fp81s21_wickG_finite_rank_kernel u c - fp81s21_wickG_finite_rank_kernel v c' :=
    fp81s21_wickB35_kernel_concat u v c c'
  have hka : MemLp (fp81s21_wickG_finite_rank_kernel w a) 2 (μ.prod μ) := by
    rw [hkernel]
    exact hk.sub hk'
  refine ⟨m+n, w, hw, a, hka, ?_⟩
  calc
    _ = (hk.sub hk').toLp _ := (MemLp.toLp_sub hk hk').symm
    _ = hka.toLp _ := MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun z => (congrFun hkernel z).symm)

/-- The scalar multiple of a represented class has a single representation. -/
theorem fp81s21_wickB37_representable_smul {d : ℕ} {μ : Measure (Euc d)}
    {k : Lp ℝ 2 (μ.prod μ)} (h : fp81s21_wickB37_representable μ k) (a : ℝ) :
    fp81s21_wickB37_representable μ (a • k) := by
  obtain ⟨m, u, hu, c, hk, rfl⟩ := h
  have hkernel : fp81s21_wickG_finite_rank_kernel u (fun i j => a * c i j) =
      a • fp81s21_wickG_finite_rank_kernel u c := fp81s21_wickB35_kernel_smul u c a
  have hka : MemLp (fp81s21_wickG_finite_rank_kernel u (fun i j => a * c i j))
      2 (μ.prod μ) := by rw [hkernel]; exact hk.const_smul a
  refine ⟨m, u, hu, fun i j => a * c i j, hka, ?_⟩
  calc
    _ = (hk.const_smul a).toLp _ := (MemLp.toLp_const_smul a hk).symm
    _ = hka.toLp _ := MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun z => (congrFun hkernel z).symm)

/-- Every element of the finite-rank span has a single representation. -/
theorem fp81s21_wickB37_span_representable {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (k : fp81s21_wickB32_finiteRankSubmodule μ) :
    fp81s21_wickB37_representable μ k := by
  have hzero : fp81s21_wickB37_representable μ 0 := by
    let u : Fin 0 → Euc d → ℝ := fun i => Fin.elim0 i
    let c : Fin 0 → Fin 0 → ℝ := fun i => Fin.elim0 i
    have hu : ∀ i, MemLp (u i) 2 μ := fun i => Fin.elim0 i
    have hf : fp81s21_wickG_finite_rank_kernel u c = 0 := by
      funext z
      simp [fp81s21_wickG_finite_rank_kernel, r2FiniteRankKernel]
    have hk : MemLp (fp81s21_wickG_finite_rank_kernel u c) 2 (μ.prod μ) := by
      rw [hf]; exact MemLp.zero
    refine ⟨0, u, hu, c, hk, ?_⟩
    calc
      0 = (MemLp.zero : MemLp (0 : Euc d × Euc d → ℝ) 2 (μ.prod μ)).toLp 0 := (MemLp.toLp_zero _).symm
      _ = hk.toLp _ := MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun z => (congrFun hf z).symm)
  have hall : ∀ x : Lp ℝ 2 (μ.prod μ), x ∈ Submodule.span ℝ (fp81s21_wickB32_generators μ) → fp81s21_wickB37_representable μ x := by
   intro x hx
   induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨m, c, u, hdata, hk, rfl⟩ := hx
        exact ⟨m, u, fun i => (hdata.smooth i).continuous.memLp_of_hasCompactSupport
          (hdata.compactSupport i), c, hk, rfl⟩
    | zero => exact hzero
    | add x y hx hy ihx ihy =>
        have hneg := fp81s21_wickB37_representable_smul ihy (-1)
        simpa using fp81s21_wickB37_representable_sub ihx hneg
    | smul a x hx ih => exact fp81s21_wickB37_representable_smul ih a
  
  exact hall k k.property

#print axioms fp81s21_wickB37_representable_sub
#print axioms fp81s21_wickB37_representable_smul
#print axioms fp81s21_wickB37_span_representable

end HRS.Fp81.S21
end
