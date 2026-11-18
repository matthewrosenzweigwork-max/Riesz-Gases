import HRS.Main.A8PAux49

/-!
# Packet A8P, part 50: the pair process `Y^i - Y^j - k` of a contact strong solution (`d = 1`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

/-- The functional `v ↦ v_i - v_j` (coordinate `0`). -/
def a8pL (N : ℕ) (i j : Fin N) : (Fin N → Euc 1) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (0 : Fin 1)).comp (ContinuousLinearMap.proj i) -
    (EuclideanSpace.proj (0 : Fin 1)).comp (ContinuousLinearMap.proj j)

theorem a8pL_apply {N : ℕ} (i j : Fin N) (v : Fin N → Euc 1) : a8pL N i j v = v i 0 - v j 0 := by
  simp [a8pL]

section Pair

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {N : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
  {D : DynData 1} {T : ℝ} {X₀ : Ω → Config 1 N} {W : ℝ≥0 → Ω → (Fin N → Euc 1)}
  {X : ℝ≥0 → Ω → Config 1 N} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}

/-- The pair process. -/
def a8pZp (D : DynData 1) (W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ) (X : ℝ≥0 → Ω → Config 1 N)
    (i j : Fin N) (k : ℤ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => a8pL N i j (liftProcM D W' X t ω) - k

/-- Its drift. -/
def a8pBp (D : DynData 1) (X : ℝ≥0 → Ω → Config 1 N) (i j : Fin N) : ℝ≥0 → Ω → ℝ :=
  fun t ω => a8pL N i j (driftProc D X t ω)

/-- Its noise coefficients. -/
def a8pSg1 (D : DynData 1) (i j : Fin N) : Fin N × Fin 1 → ℝ :=
  fun kk => a8pL N i j (liftedNoise D kk)

theorem a8p_pair_eq (hX : IsContactStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (hT0 : 0 ≤ T) (i j : Fin N) (k : ℤ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      a8pZp D W' X i j k t ω = a8pZp D W' X i j k 0 ω +
        (∫ s in Set.Icc (0 : ℝ) t, a8pBp D X i j (Real.toNNReal s) ω) +
        ∑ kk, (W' t ω kk - W' 0 ω kk) • a8pSg1 D i j kk := by
  have hI := hX.ae_integrableOn_drift hT0 le_rfl
  filter_upwards [hI] with ω hω t ht
  have hIt : IntegrableOn (fun s : ℝ => driftProc D X (Real.toNNReal s) ω) (Set.Icc 0 (t : ℝ)) :=
    hω.mono_set (Set.Icc_subset_Icc le_rfl ht)
  have hint := intPart_eq_integral ω (t : ℝ) hIt
  have h1 : liftProcM D W' X t ω = liftProcM D W' X 0 ω +
      (∫ s in Set.Icc (0 : ℝ) t, driftProc D X (Real.toNNReal s) ω) +
      ∑ kk, (W' t ω kk - W' 0 ω kk) • liftedNoise D kk := by
    rw [liftProcM_zero ω]
    simp only [liftProcM]
    rw [hint]
  unfold a8pZp a8pBp a8pSg1
  rw [h1]
  have h2 : a8pL N i j (∫ s in Set.Icc (0 : ℝ) t, driftProc D X (Real.toNNReal s) ω) =
      ∫ s in Set.Icc (0 : ℝ) t, a8pL N i j (driftProc D X (Real.toNNReal s) ω) :=
    (ContinuousLinearMap.integral_comp_comm (a8pL N i j) hIt).symm
  rw [map_add, map_add, h2, map_sum]
  simp only [map_smul]
  ring

end Pair

end HRS.Main.A8P
