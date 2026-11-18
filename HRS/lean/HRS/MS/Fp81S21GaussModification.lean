import HRS.MS.S21F_D01

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

namespace HRS.Fp81.S21

open HRS.Whole
open HRS.MS.R26T3

/-- Deterministic step: continuity of `f` on every `[0,n]`, `n : ℕ`, gives continuity on `[0,∞)`. -/
theorem fp81s21_contOn_Ici_of_nat {β : Type*} [TopologicalSpace β] (f : ℝ → β)
    (h : ∀ n : ℕ, ContinuousOn f (Set.Icc 0 (n : ℝ))) :
    ContinuousOn f (Set.Ici 0) := by
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_gt t
  have hI : Set.Ici (0 : ℝ) ∩ Set.Iio (n : ℝ) ∈ 𝓝[Set.Ici 0] t :=
    inter_mem_nhdsWithin _ (Iio_mem_nhds hn)
  have hsub : Set.Ici (0 : ℝ) ∩ Set.Iio (n : ℝ) ⊆ Set.Icc 0 (n : ℝ) :=
    fun x hx => Set.mem_Icc.mpr ⟨Set.mem_Ici.mp hx.1, le_of_lt (Set.mem_Iio.mp hx.2)⟩
  have hcw : ContinuousWithinAt f (Set.Icc 0 (n : ℝ)) t :=
    h n t (Set.mem_Icc.mpr ⟨Set.mem_Ici.mp ht, hn.le⟩)
  exact hcw.mono_of_mem_nhdsWithin (Filter.mem_of_superset hI hsub)

/-- A joint continuous modification of an arbitrary supplied Gaussian realization `G`: there is a
jointly measurable `Zbar` whose paths are continuous on all of `ℝ`, and which agrees with `G.Z`
at every `u ≥ 0`, almost surely. -/
theorem fp81s21_gauss_modification (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (G : GaussianRealization R) :
    ∃ Zbar : ℝ → G.Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ),
      Measurable (Function.uncurry Zbar) ∧
      (∀ ζ, Continuous (fun t => Zbar t ζ)) ∧
      (∀ᵐ ζ ∂G.P, ∀ u : ℝ, 0 ≤ u → Zbar u ζ = G.Z u ζ) := by
  classical
  -- (1) continuity on every integer horizon, almost surely and simultaneously for all `n`
  have hnat : ∀ᵐ ζ ∂G.P, ∀ n : ℕ, ContinuousOn (fun s => G.Z s ζ) (Set.Icc 0 (n : ℝ)) :=
    ae_all_iff.mpr fun n => (G.evolution (n : ℝ)).cont
  have hcont : ∀ᵐ ζ ∂G.P, ContinuousOn (fun s => G.Z s ζ) (Set.Ici 0) :=
    hnat.mono fun ζ hζ => fp81s21_contOn_Ici_of_nat _ hζ
  -- (2) a measurable null superset of the bad event
  obtain ⟨Bad, hsub, hBadm, hBad0⟩ := exists_measurable_superset_of_null (ae_iff.mp hcont)
  have hgood : ∀ ζ, ζ ∉ Bad → ContinuousOn (fun s => G.Z s ζ) (Set.Ici 0) := by
    intro ζ hζ
    by_contra h
    have hmem : ζ ∈ {a : G.Ω | ¬ ContinuousOn (fun s => G.Z s a) (Set.Ici 0)} := h
    exact hζ (hsub hmem)
  have hnBad : ∀ᵐ ζ ∂G.P, ζ ∉ Bad := by
    rw [ae_iff]
    simpa using hBad0
  -- (3) the modification: zero on the null set `Bad`, the path `G.Z (max t 0)` elsewhere
  have hcontZ : ∀ ζ, Continuous (fun s => if ζ ∈ Bad then
      (0 : OscDual p.d (wholeSpaceIndex p.d : ℝ)) else G.Z (max s 0) ζ) := by
    intro ζ
    by_cases hζ : ζ ∈ Bad
    · simp only [if_pos hζ]
      exact continuous_const
    · simp only [if_neg hζ]
      exact (hgood ζ hζ).comp_continuous (continuous_id.max continuous_const :
          Continuous fun s : ℝ => max s (0 : ℝ))
        (fun s => Set.mem_Ici.mpr (le_max_right s 0))
  have hmeasZ : ∀ s : ℝ, Measurable (fun ζ => if ζ ∈ Bad then
      (0 : OscDual p.d (wholeSpaceIndex p.d : ℝ)) else G.Z (max s 0) ζ) := by
    intro s
    exact Measurable.ite hBadm measurable_const ((G.evolution 0).meas (max s 0))
  refine ⟨fun s ζ => if ζ ∈ Bad then (0 : OscDual p.d (wholeSpaceIndex p.d : ℝ))
    else G.Z (max s 0) ζ, ?_, ?_, ?_⟩
  · exact measurable_uncurry_of_continuous_of_measurable hcontZ hmeasZ
  · exact hcontZ
  · filter_upwards [hnBad] with ζ hζ u hu
    simp only [if_neg hζ]
    rw [max_eq_left hu]

#print axioms fp81s21_contOn_Ici_of_nat
#print axioms fp81s21_gauss_modification

end HRS.Fp81.S21

end
