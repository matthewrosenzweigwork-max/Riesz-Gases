import HRS.MS.GenPathAux6

/-!
# S5.6 packet P9a, part 2: the identity evolution on a Hilbert space and its stochastic convolution

`s56_idEvol K : EvolData K K` (identity evolution, `j = id`, `A = 0`) satisfies `MaxHyp T 1` (`s56_idEvol_maxHyp`), and the
stochastic convolution `∫_0^t V dM` of a process `M` against it is `M_t - M_0` (`s56_isStochConv_id`): the Riemann sums
telescope.  This is how the maximal/comparison machinery of Section 3 (stated for evolutions `V(t,r)`) is applied to the
`𝒦`-valued martingale of S5.2 ("identity evolution, followed by the bounded reconstruction map", S L3416-3418).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.Uniform

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The identity evolution. -/
def s56_idEvol (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℝ K] : EvolData K K where
  j := ContinuousLinearMap.id ℝ K
  VH := fun _ _ => ContinuousLinearMap.id ℝ K
  VE := fun _ _ => ContinuousLinearMap.id ℝ K
  D := ⊤
  A := fun _ => 0

lemma s56_idEvol_A (r : ℝ) (x : ↥(s56_idEvol K).D) : (s56_idEvol K).A r x = 0 := rfl

theorem s56_idEvol_isEvolution (T : ℝ) : (s56_idEvol K).IsEvolution T where
  inj := fun x y h => h
  dense := by
    show Dense (((⊤ : Submodule ℝ K) : Submodule ℝ K) : Set K)
    rw [Submodule.top_coe]; exact dense_univ
  self_H := fun t _ => rfl
  self_E := fun t _ => rfl
  comp_H := fun s r t _ _ _ _ => rfl
  comp_E := fun s r t _ _ _ _ => rfl
  intertwine := fun r t _ _ _ => rfl
  cont_E := fun y => continuousOn_const
  deriv := fun t _ x r _ => by
    have h0 : -((s56_idEvol K).VE t r ((s56_idEvol K).A r x)) = 0 := by
      rw [s56_idEvol_A]; simp [s56_idEvol]
    rw [h0]
    exact hasDerivWithinAt_const _ _ _

theorem s56_idEvol_twoLevel (T : ℝ) : (s56_idEvol K).TwoLevel T 1 := by
  refine ⟨rfl, ContinuousLinearMap.norm_id_le, fun r t _ _ _ => ⟨ContinuousLinearMap.norm_id_le,
    ContinuousLinearMap.norm_id_le⟩, fun r _ x => ?_⟩
  rw [s56_idEvol_A]; simp

theorem s56_idEvol_maxHyp (T : ℝ) : (s56_idEvol K).MaxHyp T 1 :=
  ⟨s56_idEvol_isEvolution T, Or.inl (s56_idEvol_twoLevel T)⟩

lemma s56_fin_telescope {G : Type*} [AddCommGroup G] (n : ℕ) (g : Fin (n + 1) → G) :
    ∑ i : Fin n, (g i.succ - g i.castSucc) = g (Fin.last n) - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have := ih (fun i => g i.castSucc)
    simp only [Fin.succ_castSucc] at *
    rw [this]
    simp [Fin.succ_last]

/-- The stochastic convolution against the identity evolution is the increment: `∫_a^t dM = M_t - M_a`. -/
theorem s56_isStochConv_id {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : ℝ → Ω → K) (a t : ℝ) :
    IsStochConv P (s56_idEvol K).VE (s56_idEvol K).j M a t (fun ζ => M t ζ - M a ζ) := by
  intro ε hε
  refine ⟨1, one_pos, fun n r h0 hn hmono hmesh => ?_⟩
  have hsum : ∀ ζ, riemannSum (s56_idEvol K).VE (s56_idEvol K).j M t r ζ = M t ζ - M a ζ := by
    intro ζ
    unfold riemannSum
    have h := s56_fin_telescope n (fun i : Fin (n + 1) => M (r i) ζ)
    rw [hn, h0] at h
    simpa [s56_idEvol] using h
  have hz : ∀ ζ, M t ζ - M a ζ - riemannSum (s56_idEvol K).VE (s56_idEvol K).j M t r ζ = 0 := fun ζ => by
    rw [hsum ζ, sub_self]
  simp only [hz, enorm_zero]
  simpa using ENNReal.ofReal_pos.2 hε

end HRS.MS.GenPath
