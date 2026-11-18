import HRS.MS.R2GenInitAux19

/-!
# S10.5 window comparison, packet B6: `r ↦ ⟨e, Γ_{b,r,a}(x)⟩` is measurable (piecewise continuous with a jump at `r = b`)

`s105_win_A0_cont`: the first slot is continuous in `r` on `[0,τ₀]` (`∂_aU(r,b)φ_α` for `r ≤ b`, `∂_aφ_α` after).
`s105_win_mid_cont`: the pairing of the middle slot is continuous in `r` (dominated convergence in `u`; the integrand jumps only at `u = r - b`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.MP.RdRem HRS.MS.Go HRS.MS.R2WinErr HRS.MS.GenPath

variable {d : ℕ}

theorem s105_b_sq_summable (hbS : Summable (s104_b d)) : Summable fun α : MultiIndex d => (s104_b d α) ^ 2 := by
  refine hbS.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => ?_)
  have h0 := s104_b_nonneg (d := d) α
  have h1 := s105_b_le_one (d := d) α
  nlinarith

/-- Pointwise bound of the coordinates of an orbit term from `R2OrbitGrad`. -/
theorem s105_coord_le (C : WholeCoeff d) {k : ℕ} {t : ℝ} {ψ : Euc d → ℝ} {A cdec : ℝ} (hA : 0 ≤ A) (hcd : 0 ≤ cdec)
    (h : R2OrbitGrad C k t ψ A cdec) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) (a : Fin d) (x : Euc d) :
    |gradComp a (propagatorW C r t ψ) x| ≤ A := by
  obtain ⟨-, h2⟩ := s104_gradComp_bound C hA h hr a
  have := h2 0 (Nat.zero_le _) x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  refine this.trans (mul_le_of_le_one_right hA ?_)
  rw [Real.exp_le_one_iff]
  nlinarith [hr.2]

/-- Continuity in `r` of the first slot of the window feature. -/
theorem s105_win_A0_cont (C : WholeCoeff d) (m : ℝ) {b τ₀ : ℝ} (hb : 0 ≤ b) (Cs : ℝ) (a : Fin d)
    (x : Euc d) (hbS : Summable (s104_b d))
    (hex0 : ∀ α, ∀ t : ℝ, 0 ≤ t → ∃ f, IsClassicalAdjointW C t (oscTestFun m α) f)
    (hbd : ∀ α, ∀ r ∈ Set.Icc (0 : ℝ) τ₀, |gradComp a (propagatorW C r (max b r) (oscTestFun m α)) x| ≤
      Cs * s104_b d α) (v : OscDual d m) :
    ContinuousOn (fun r => inner ℝ v (ellVec (d := d) m
      (fun α => gradComp a (propagatorW C r (max b r) (oscTestFun m α)) x))) (Set.Icc (0 : ℝ) τ₀) := by
  have hcα : ∀ α, ContinuousOn (fun r => gradComp a (propagatorW C r (max b r) (oscTestFun m α)) x)
      (Set.Icc (0 : ℝ) τ₀) := by
    intro α
    have hclb := HRS.MS.Fcau.propagatorW_isClassical (hex0 α b hb)
    have hF : ContinuousOn (fun r' => gradComp a (propagatorW C r' b (oscTestFun m α)) x) (Set.Icc 0 b) :=
      s56_gradComp_cont_r hclb a x
    have hcomp : ContinuousOn (fun r => gradComp a (propagatorW C (min r b) b (oscTestFun m α)) x)
        (Set.Icc (0 : ℝ) τ₀) :=
      hF.comp (continuous_id.min continuous_const).continuousOn (fun r hr => ⟨le_min hr.1 hb, min_le_right _ _⟩)
    refine hcomp.congr fun r hr => ?_
    beta_reduce
    by_cases hrb : r ≤ b
    · rw [max_eq_left hrb, min_eq_left hrb]
    · have hbr : b < r := not_le.1 hrb
      rw [max_eq_right hbr.le, min_eq_right hbr.le]
      have h1 := (HRS.MS.Fcau.propagatorW_isClassical (hex0 α r hr.1)).terminal
      have h2 := hclb.terminal
      rw [h1]; simp only [h2]
  have hpair := s56_cont_pairing (bb := s104_b d) (s105_b_sq_summable hbS) (fun α => s104_b_nonneg α) Cs
    (s := Set.Icc (0 : ℝ) τ₀)
    (c := fun α r => gradComp a (propagatorW C r (max b r) (oscTestFun m α)) x) hcα hbd
    (γ := fun α => OscDual.coord v α) (s56_sq_summable_of_memℓp (lp.memℓp v))
  refine hpair.congr fun r hr => ?_
  rw [real_inner_comm, s56_inner_ellVec m (s105_memℓp_of_bound (K := Cs) (fun α => hbd α r hr) hbS) v]

end HRS.MS.R2GenInit
