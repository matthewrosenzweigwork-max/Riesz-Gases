import HRS.MS.R2InterpAux27

/-!
# S10.2 (worker S102), part 28 (packet B1): the gradient feature of the grid has norm `≤ C ⟨x⟩^P`

For `u ∈ [0,T]`, a point `x` and a direction `a`, the coefficient vector `cc(i,α) = 1[u ≤ t_i] ∂_aU^{u,t_i}φ_α(x)` on the index set of `P_L`
has synthesis `‖∑ cc(p) b_p‖_𝒳 ≤ C_emb ⟨x⟩^P K_V`, uniformly in `L`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.FixEq

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

/-- The coefficient vector of the gradient feature. -/
def s102_cc (C : WholeCoeff d) (m : ℝ) (hT : 0 < T) (L : ℕ) (u : ℝ) (x : Euc d) (a : Fin d)
    (p : ℕ × MultiIndex d) : ℝ :=
  if u ≤ ((s102_node hT L p.1 : Set.Icc (0 : ℝ) T) : ℝ) then
    gradient (propagatorW C u ((s102_node hT L p.1 : Set.Icc (0 : ℝ) T) : ℝ) (oscTestFun m p.2)) x a
  else 0

theorem s102_feature_norm (hd : 1 ≤ d) (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 + 1 < r) (hP : (d : ℝ) < 2 * Pw)
    (hD : S101Data C m T r c) (hlin : S102Lin C m T) (hT : 0 < T) :
    ∃ Ce : ℝ, 0 < Ce ∧ ∀ (L : ℕ) {u : ℝ}, u ∈ Icc (0 : ℝ) T → ∀ (x : Euc d) (a : Fin d),
      ‖∑ p ∈ s102_idx d L, s102_cc C m hT L u x a p • s102_bpath (m := m) T L p‖ ≤
        Ce * jbracket x ^ Pw * s102_KV d r Pw c := by
  obtain ⟨Ce, hCe, hb⟩ := s102_eval_bound1 hd hP0 r hr
  refine ⟨Ce, hCe, fun L u hu x a => ?_⟩
  set M : ℝ := Ce * jbracket x ^ Pw with hMdef
  have hM0 : 0 ≤ M := mul_nonneg hCe.le (Real.rpow_nonneg (HRS.MS.Who.who_jb_pos x).le Pw)
  have hKV0 := s102_KV_nonneg d r Pw c
  have hz := s102_Z_gradient hd hP0 r hr x a
  have hbound : ∀ f, IsR2WeightedTest r Pw f → |gradient f x a| ≤ M * (weightedSobolevE r Pw f).toReal :=
    fun f hf => hb x a f hf.1 hf.2
  refine s102_Lam'_norm_le hT L _ (mul_nonneg hM0 hKV0) (fun i hi => ?_)
  by_cases hiu : u ≤ ((s102_node hT L i : Set.Icc (0 : ℝ) T) : ℝ)
  · have hti : ((s102_node hT L i : Set.Icc (0 : ℝ) T) : ℝ) ∈ Icc u T := ⟨hiu, (s102_node hT L i).2.2⟩
    have hV := s102_Vprop_norm_M hP hD (z := fun f => gradient f x a) hz hlin hbound hu hti
    rw [abs_of_nonneg hM0] at hV
    have hcoord : ∀ α, s102_cc C m hT L u x a (i, α) =
        OscDual.coord (r2Vprop C m ((s102_node hT L i : Set.Icc (0 : ℝ) T) : ℝ) u (fun f => gradient f x a)) α := by
      intro α
      rw [s102_Vprop_coord hP hD hz hlin hu hti α]
      simp [s102_cc, hiu]
    simp_rw [hcoord]
    set v := r2Vprop C m ((s102_node hT L i : Set.Icc (0 : ℝ) T) : ℝ) u (fun f => gradient f x a) with hv
    have h1 : ∑ α ∈ s102_SL d L, OscDual.coord v α ^ 2 ≤ ∑' α, OscDual.coord v α ^ 2 :=
      (OscDual.coord_sq_summable' v).sum_le_tsum _ (fun α _ => sq_nonneg _)
    have h2 : ∑' α, OscDual.coord v α ^ 2 = ‖v‖ ^ 2 := by
      rw [OscDual.norm_eq_coord, Real.sq_sqrt (tsum_nonneg fun α => sq_nonneg _)]
    calc _ ≤ ‖v‖ ^ 2 := h2 ▸ h1
      _ ≤ (M * s102_KV d r Pw c) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hV 2
  · have : ∀ α, s102_cc C m hT L u x a (i, α) = 0 := fun α => by simp [s102_cc, hiu]
    simp_rw [this]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity

end HRS.MS.R2Interp

end
