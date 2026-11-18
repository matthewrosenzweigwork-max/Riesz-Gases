import HRS.Main.A8PAux53

/-!
# Packet A8P, part 42: null contact occupation of a contact strong solution in `d = 1`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_nullContact_d1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {N : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {D : DynData d} {T : ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hd : d = 1) (hT0 : 0 ≤ T)
    (hX : IsContactStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (hV : Torus.IsCk 2 D.V) (hβ : 0 < D.invβ) : NullContactOccupation P T X := by
  subst hd
  have hI := hX.ae_integrableOn_drift hT0 le_rfl
  -- the pairwise zero sets
  have hzero : ∀ (i j : Fin N) (k : ℤ), i ≠ j → ∀ᵐ ω ∂P,
      volume {s : ℝ | s ∈ Set.Icc 0 T ∧ a8pZp D W' X i j k (Real.toNNReal s) ω = 0} = 0 := by
    intro i j k hij
    refine a8p_zero_null hF.brownian hT0 (a8pSg1 D i j) ?_ (a8pZp D W' X i j k)
      ?_ (a8pBp D X i j) ?_ ?_ (a8p_pair_eq hX hF hT0 i j k)
    · have h1 : a8pSg1 D i j (i, 0) = Real.sqrt (2 * D.invβ) := by
        unfold a8pSg1
        rw [a8pL_apply, liftedNoise_apply, liftedNoise_apply]
        simp [hij.symm]
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun kk => a8pSg1 D i j kk ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ (i, (0 : Fin 1))))
      rw [h1]
      have : 0 < Real.sqrt (2 * D.invβ) := Real.sqrt_pos.2 (by linarith)
      positivity
    · intro t
      have e : a8pZp D W' X i j k 0 = fun ω => a8pL N i j (fun m => Torus.rep (X 0 ω m)) - k := by
        funext ω
        simp only [a8pZp, liftProcM_zero]
      rw [e]
      have hg : Measurable (fun x : Config 1 N => a8pL N i j (fun m => Torus.rep (x m)) - k) := by
        refine ((a8pL N i j).continuous.measurable.comp ?_).sub measurable_const
        exact measurable_pi_iff.2 fun m => (measurable_torusRep 1).comp (measurable_pi_apply m)
      exact hg.comp (hF.measurable_init t)
    · exact fun m => (a8pL N i j).continuous.measurable.comp (isProgressive_driftProc hV hF m)
    · filter_upwards [hI] with ω hω
      exact (a8pL N i j).integrable_comp hω
  -- the lift
  have hlift := hX.ae_lift_eq hF
  have hint : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ T →
      intPart D X τ ω = ∫ s in Set.Icc 0 (τ : ℝ), driftProc D X (Real.toNNReal s) ω := by
    filter_upwards [hI] with ω hω τ hτ
    exact intPart_eq_integral ω τ (hω.mono_set (Set.Icc_subset_Icc le_rfl hτ))
  have hlift' : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ T →
      X τ ω = fun i => Torus.mk (liftProcM D W' X τ ω i) := by
    filter_upwards [hlift, hint] with ω h1 h2 τ hτ
    rw [h1 τ hτ]
    funext i
    simp only [liftProcM, liftProc, h2 τ hτ]
  have hall : ∀ᵐ ω ∂P, ∀ (i j : Fin N) (k : ℤ), i ≠ j →
      volume {s : ℝ | s ∈ Set.Icc 0 T ∧ a8pZp D W' X i j k (Real.toNNReal s) ω = 0} = 0 := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    rw [ae_all_iff]; intro k
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun ω h => absurd hij h
    · filter_upwards [hzero i j k hij] with ω h _ using h
  filter_upwards [hall, hlift'] with ω h1 h2
  have hsub : {s : ℝ | s ∈ Set.Icc 0 T ∧ X (Real.toNNReal s) ω ∈ collisionSet 1 N} ⊆
      ⋃ p : Fin N × Fin N × ℤ, {s : ℝ | s ∈ Set.Icc 0 T ∧ p.1 ≠ p.2.1 ∧
        a8pZp D W' X p.1 p.2.1 p.2.2 (Real.toNNReal s) ω = 0} := by
    rintro s ⟨hs, i, j, hij, hc⟩
    have hle : ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ T := by
      rw [Real.coe_toNNReal _ hs.1]; exact hs.2
    have hm := h2 (Real.toNNReal s) hle
    have hmk : Torus.mk (liftProcM D W' X (Real.toNNReal s) ω i) =
        Torus.mk (liftProcM D W' X (Real.toNNReal s) ω j) := by
      have := congrFun hm i
      have h' := congrFun hm j
      rw [← this, ← h']; exact hc
    obtain ⟨n, hn⟩ := exists_lattice_of_mk_eq hmk
    refine Set.mem_iUnion.2 ⟨(i, j, n 0), hs, hij, ?_⟩
    have h0 := congrArg (fun v : Euc 1 => v 0) hn
    simp only [PiLp.add_apply, Lattice.toEuc] at h0
    unfold a8pZp
    rw [a8pL_apply, h0]
    simp
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null fun p => ?_
  by_cases hp : p.1 = p.2.1
  · have : {s : ℝ | s ∈ Set.Icc 0 T ∧ p.1 ≠ p.2.1 ∧
        a8pZp D W' X p.1 p.2.1 p.2.2 (Real.toNNReal s) ω = 0} = ∅ := by
      ext s; simp [hp]
    rw [this]; exact measure_empty
  · refine measure_mono_null ?_ (h1 p.1 p.2.1 p.2.2 hp)
    intro s hs
    exact ⟨hs.1, hs.2.2⟩

section Null

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ}

theorem a8p_nullContact (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) : NullContactOccupation (R N).P S.T (R N).X := by
  have h := hS.flow N hN
  rcases h.flow with ⟨h1, -⟩ | ⟨-, -, -, -, h2⟩ | ⟨hd1, -, hβ, -, h4⟩
  · exact nullContactOccupation_of_strong h1
  · exact h2.occupation
  · obtain ⟨ℱ, W', hF⟩ := hS.filtered N hN
    have hV : Torus.IsCk 2 (S.dyn N).V := by
      have := hS.potential.1
      exact this.of_le (by exact_mod_cast (by omega : 2 ≤ PDE.mStar d + 3))
    exact a8p_nullContact_d1 hd1 S.hT.le h4 hF hV hβ

end Null

end HRS.Main.A8P
