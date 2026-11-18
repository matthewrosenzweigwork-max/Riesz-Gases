import HRS.Sections.QuenchAux19

/-!
# Packet QUENCH (Q27), part 20: difference of two window expectations

For two window processes whose coordinate covariances differ by `κ_j f_j(t)f_j(r)`:
`E₁ M(W₁,W₁) - E₂ M(W₂,W₂) = ∑_j κ_j M(p_j,p_j)` with `p_j(t) = f_j(t) e_j`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

variable {d : ℕ} {m T : ℝ}

/-- The elementary path `t ↦ f(t) e_j`. -/
def pathOf (f : C(Set.Icc (0 : ℝ) T, ℝ)) (j : NonzeroLattice d) : PathSpace d m T :=
  (⟨fun t => f t • esingle m j, f.continuous.smul continuous_const⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m))

lemma pathOf_at (f : C(Set.Icc (0 : ℝ) T, ℝ)) (j : NonzeroLattice d) (t : Set.Icc (0 : ℝ) T) :
    (pathOf f j : PathSpace d m T).at' t = f t • esingle m j := rfl

lemma norm_pathOf_le (f : C(Set.Icc (0 : ℝ) T, ℝ)) (j : NonzeroLattice d) :
    ‖(pathOf f j : PathSpace d m T)‖ ≤ ‖f‖ := by
  refine (ContinuousMap.norm_le (pathOf f j : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) (norm_nonneg _)).2
    fun t => ?_
  show ‖f t • esingle m j‖ ≤ _
  rw [norm_smul, norm_esingle, mul_one]
  exact ContinuousMap.norm_coe_le_norm f t

section Diff

variable {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
  [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
  {W₁ : ℝ → Ω₁ → NegSobolev d m} {W₂ : ℝ → Ω₂ → NegSobolev d m}
  {c₁ c₂ : NonzeroLattice d → ℝ → ℝ → ℝ}

theorem win_diff (hT : 0 < T) (h₁ : WinData P₁ m T W₁ c₁) (h₂ : WinData P₂ m T W₂ c₂)
    (M : PathSpace d m T [×2]→L[ℝ] ℝ) (κ : NonzeroLattice d → ℝ) (f : NonzeroLattice d → C(Set.Icc (0 : ℝ) T, ℝ))
    (hc : ∀ (j : NonzeroLattice d) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) T),
      c₁ j t r - c₂ j t r = κ j * f j ⟨t, ht⟩ * f j ⟨r, hr⟩)
    (hsum : Summable fun j => |κ j| * ‖f j‖ ^ 2) :
    (∫ ω, M ![toPath m T W₁ ω, toPath m T W₁ ω] ∂P₁) - (∫ ω, M ![toPath m T W₂ ω, toPath m T W₂ ω] ∂P₂) =
      ∑' j, κ j * M ![(pathOf (f j) j : PathSpace d m T), (pathOf (f j) j : PathSpace d m T)] := by
  classical
  -- the finite-`n` identity
  have hn : ∀ n : ℕ, HasSum (fun j => κ j * M ![bInterp hT n ((pathOf (f j) j : PathSpace d m T)), bInterp hT n ((pathOf (f j) j : PathSpace d m T))])
      ((∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
        ∫ ω, bk hT M n k l (W₁ (bnode hT n k) ω) (W₁ (bnode hT n l) ω) ∂P₁) -
       (∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
        ∫ ω, bk hT M n k l (W₂ (bnode hT n k) ω) (W₂ (bnode hT n l) ω) ∂P₂)) := by
    intro n
    have hkl : ∀ k l : Fin (n + 1), HasSum
        (fun j => κ j * (f j (bnode hT n k) * f j (bnode hT n l) *
          bk hT M n k l (esingle m j) (esingle m j)))
        ((∫ ω, bk hT M n k l (W₁ (bnode hT n k) ω) (W₁ (bnode hT n l) ω) ∂P₁) -
         (∫ ω, bk hT M n k l (W₂ (bnode hT n k) ω) (W₂ (bnode hT n l) ω) ∂P₂)) := by
      intro k l
      have := (win_hasSum hT h₁ M n k l).sub (win_hasSum hT h₂ M n k l)
      have e : (fun j => κ j * (f j (bnode hT n k) * f j (bnode hT n l) *
          bk hT M n k l (esingle m j) (esingle m j))) = fun j =>
          bk hT M n k l (esingle m j) (esingle m j) * c₁ j (bnode hT n k) (bnode hT n l) -
          bk hT M n k l (esingle m j) (esingle m j) * c₂ j (bnode hT n k) (bnode hT n l) := by
        funext j
        have h := hc j (bnode hT n k).1 (bnode hT n k).2 (bnode hT n l).1 (bnode hT n l).2
        have h' : c₁ j (bnode hT n k) (bnode hT n l) = c₂ j (bnode hT n k) (bnode hT n l) +
            κ j * f j (bnode hT n k) * f j (bnode hT n l) := by linarith
        rw [h']
        ring
      rw [e]
      exact this
    have hsumkl := hasSum_sum (s := (Finset.univ : Finset (Fin (n + 1)))) fun k _ =>
      hasSum_sum (s := (Finset.univ : Finset (Fin (n + 1)))) fun l _ => hkl k l
    have e2 : (fun j => ∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
        κ j * (f j (bnode hT n k) * f j (bnode hT n l) * bk hT M n k l (esingle m j) (esingle m j))) =
        fun j => κ j * M ![bInterp hT n ((pathOf (f j) j : PathSpace d m T)), bInterp hT n ((pathOf (f j) j : PathSpace d m T))] := by
      funext j
      rw [bInterp_bilin, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [pathOf_at, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [e2] at hsumkl
    have e3 : (∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
        ((∫ ω, bk hT M n k l (W₁ (bnode hT n k) ω) (W₁ (bnode hT n l) ω) ∂P₁) -
         (∫ ω, bk hT M n k l (W₂ (bnode hT n k) ω) (W₂ (bnode hT n l) ω) ∂P₂))) =
        (∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
          ∫ ω, bk hT M n k l (W₁ (bnode hT n k) ω) (W₁ (bnode hT n l) ω) ∂P₁) -
        (∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
          ∫ ω, bk hT M n k l (W₂ (bnode hT n k) ω) (W₂ (bnode hT n l) ω) ∂P₂) := by
      simp_rw [Finset.sum_sub_distrib]
    rw [e3] at hsumkl
    exact hsumkl
  -- the limit
  have hlimL := (win_limit hT h₁ M).sub (win_limit hT h₂ M)
  have hlimR : Tendsto (fun n : ℕ => ∑' j, κ j * M ![bInterp hT n ((pathOf (f j) j : PathSpace d m T)), bInterp hT n ((pathOf (f j) j : PathSpace d m T))])
      atTop (𝓝 (∑' j, κ j * M ![(pathOf (f j) j : PathSpace d m T), (pathOf (f j) j : PathSpace d m T)])) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun j => |κ j| * (‖M‖ * ‖f j‖ ^ 2)) ?_ ?_ ?_
    · have := hsum.mul_left ‖M‖
      refine (this.congr fun j => ?_)
      ring
    · intro j
      have h1 : Tendsto (fun n => ![bInterp hT n ((pathOf (f j) j : PathSpace d m T)), bInterp hT n ((pathOf (f j) j : PathSpace d m T))]) atTop
          (𝓝 ![(pathOf (f j) j : PathSpace d m T), (pathOf (f j) j : PathSpace d m T)]) := by
        refine tendsto_pi_nhds.2 fun i => ?_
        fin_cases i <;> simpa using bInterp_tendsto hT ((pathOf (f j) j : PathSpace d m T))
      exact ((M.cont.tendsto _).comp h1).const_mul (κ j)
    · refine Eventually.of_forall fun n j => ?_
      have h1 := abs_multi_le M (bInterp hT n ((pathOf (f j) j : PathSpace d m T))) (bInterp hT n ((pathOf (f j) j : PathSpace d m T)))
      have h2 := norm_bInterp_le hT n ((pathOf (f j) j : PathSpace d m T))
      have h3 := norm_pathOf_le (m := m) (f j) j
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |M ![bInterp hT n ((pathOf (f j) j : PathSpace d m T)), bInterp hT n ((pathOf (f j) j : PathSpace d m T))]|
          ≤ ‖M‖ * ‖bInterp hT n ((pathOf (f j) j : PathSpace d m T))‖ * ‖bInterp hT n ((pathOf (f j) j : PathSpace d m T))‖ := h1
        _ ≤ ‖M‖ * ‖f j‖ * ‖f j‖ := by
            gcongr
            · exact h2.trans h3
            · exact h2.trans h3
        _ = ‖M‖ * ‖f j‖ ^ 2 := by ring
  have hlimR' : Tendsto (fun n : ℕ => ∑' j, κ j * M ![bInterp hT n ((pathOf (f j) j : PathSpace d m T)), bInterp hT n ((pathOf (f j) j : PathSpace d m T))])
      atTop (𝓝 ((∫ ω, M ![toPath m T W₁ ω, toPath m T W₁ ω] ∂P₁) -
        (∫ ω, M ![toPath m T W₂ ω, toPath m T W₂ ω] ∂P₂))) := by
    refine hlimL.congr fun n => ?_
    exact ((hn n).tsum_eq).symm
  exact tendsto_nhds_unique hlimR' hlimR

end Diff

end Qch

end HRS
