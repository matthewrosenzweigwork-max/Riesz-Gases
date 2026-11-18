import HRS.MS.MovAdjAux11

/-!
# S6.7 (packet P3, part 1): the ladder operators `x_j`, `∂_j` on `Σ^m` for non-Schwartz functions

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

For `ψ ∈ Σ^{r+1}` that is `C¹` with `ψ, x_jψ, ∂_jψ ∈ L²` (qualitative decay, true for `ψ = √ρ (f - c)`, `f ∈ C_b²`):
* `s67_coeff_xmul_gen`, `s67_coeff_partial_gen`: the Hermite coefficient formulas of `x_jψ` and `∂_jψ`;
* `s67_xmul_osc`, `s67_partial_osc`: `‖x_jψ‖_{Σ^r}, ‖∂_jψ‖_{Σ^r} ≤ 2^{|r+1|/2} ‖ψ‖_{Σ^{r+1}}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MS.MovOsc

variable {d : ℕ}

theorem s67_ladder_general (j : Fin d) (r : ℝ) {ψ g : Euc d → ℝ} (hψ : MemOsc (r + 1) ψ)
    (hg : MemLp g 2 (volume : Measure (Euc d))) (σ : ℝ) (hσ : σ ^ 2 = 1)
    (hc : ∀ α, hermiteCoeff g α =
      Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteCoeff ψ (mova1_up j α) +
        σ * Real.sqrt ((α j : ℝ) / 2) * hermiteCoeff ψ (mova1_dn j α)) :
    MemOsc r g ∧ oscNorm r g ≤ Real.sqrt (2 ^ |r + 1|) * oscNorm (r + 1) ψ := by
  have hA : ∀ α : MultiIndex d, Real.sqrt (((α j : ℝ) + 1) / 2) ^ 2 ≤ oscEigenvalue d α / 4 := by
    intro α
    rw [Real.sq_sqrt (by positivity)]
    have := mova1_eigen_ge j α
    linarith
  have hB : ∀ α : MultiIndex d, (σ * Real.sqrt ((α j : ℝ) / 2)) ^ 2 ≤ oscEigenvalue d α / 4 := by
    intro α
    rw [mul_pow, hσ, one_mul, Real.sq_sqrt (by positivity)]
    have := mova1_eigen_ge j α
    have : (0 : ℝ) ≤ α j := Nat.cast_nonneg _
    linarith
  have hB0 : ∀ α : MultiIndex d, α j = 0 → σ * Real.sqrt ((α j : ℝ) / 2) = 0 := by
    intro α h; simp [h]
  obtain ⟨hsum, hle⟩ := mova1_ladder_bound j r (hermiteCoeff ψ) (hermiteCoeff g)
    (fun α => Real.sqrt (((α j : ℝ) + 1) / 2)) (fun α => σ * Real.sqrt ((α j : ℝ) / 2)) hA hB hB0
    (fun α => hc α) hψ.2
  refine ⟨⟨hg, hsum⟩, ?_⟩
  unfold oscNorm
  rw [← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt hle

theorem s67_coeff_xmul_gen {ψ : Euc d → ℝ} (hψ : MemLp ψ 2 (volume : Measure (Euc d))) (j : Fin d)
    (α : MultiIndex d) :
    hermiteCoeff (fun x => x j * ψ x) α =
      Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteCoeff ψ (mova1_up j α) +
        Real.sqrt ((α j : ℝ) / 2) * hermiteCoeff ψ (mova1_dn j α) := by
  unfold hermiteCoeff
  have I1 : Integrable (fun x => ψ x * hermiteFunD (mova1_up j α) x) :=
    hψ.integrable_mul (memLp_hermiteFunD _)
  have I2 : Integrable (fun x => ψ x * hermiteFunD (mova1_dn j α) x) :=
    hψ.integrable_mul (memLp_hermiteFunD _)
  have e : ∀ x : Euc d, (x j * ψ x) * hermiteFunD α x =
      Real.sqrt (((α j : ℝ) + 1) / 2) * (ψ x * hermiteFunD (mova1_up j α) x) +
        Real.sqrt ((α j : ℝ) / 2) * (ψ x * hermiteFunD (mova1_dn j α) x) := by
    intro x
    have := mova1_x_hD α j x
    linear_combination ψ x * this
  simp_rw [e]
  rw [integral_add (I1.const_mul _) (I2.const_mul _), integral_const_mul, integral_const_mul]

theorem s67_coeff_partial_gen {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψL : MemLp ψ 2 (volume : Measure (Euc d)))
    (j : Fin d)
    (hdL : MemLp (fun x => fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))) 2 (volume : Measure (Euc d)))
    (α : MultiIndex d) :
    hermiteCoeff (fun x => fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))) α =
      Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteCoeff ψ (mova1_up j α) -
        Real.sqrt ((α j : ℝ) / 2) * hermiteCoeff ψ (mova1_dn j α) := by
  obtain ⟨hA, -⟩ := hermiteFunD_line_data α j
  have hhs : ContDiff ℝ 1 (hermiteFunD α : Euc d → ℝ) := (contDiff_hermiteFunD α).of_le (by simp)
  have hDh : ∀ x : Euc d, fderiv ℝ (hermiteFunD α) x (EuclideanSpace.single j (1 : ℝ)) =
      (∏ i ∈ Finset.univ.erase j, hermiteFun (α i) (x i)) * deriv (hermiteFun (α j)) (x j) := by
    intro x
    have h1 := (hA x).lineDeriv
    rw [← h1]
    exact ((hhs.differentiable one_ne_zero x).lineDeriv_eq_fderiv).symm
  have hDh' : ∀ x : Euc d, fderiv ℝ (hermiteFunD α) x (EuclideanSpace.single j (1 : ℝ)) =
      Real.sqrt ((α j : ℝ) / 2) * hermiteFunD (mova1_dn j α) x -
        Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteFunD (mova1_up j α) x := by
    intro x; rw [hDh x, mova1_dQ_hD]
  have hDL : MemLp (fun x => fderiv ℝ (hermiteFunD α) x (EuclideanSpace.single j (1 : ℝ))) 2
      (volume : Measure (Euc d)) := by
    have : (fun x => fderiv ℝ (hermiteFunD α) x (EuclideanSpace.single j (1 : ℝ))) = fun x =>
        Real.sqrt ((α j : ℝ) / 2) * hermiteFunD (mova1_dn j α) x -
          Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteFunD (mova1_up j α) x := funext hDh'
    rw [this]
    exact ((memLp_hermiteFunD _).const_mul _).sub ((memLp_hermiteFunD _).const_mul _)
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
    (f := (hermiteFunD α : Euc d → ℝ)) (g := ψ) (v := EuclideanSpace.single j (1 : ℝ))
    (hDL.integrable_mul hψL) ((memLp_hermiteFunD α).integrable_mul hdL)
    ((memLp_hermiteFunD α).integrable_mul hψL)
    (fun x _ => hhs.differentiable one_ne_zero x) (fun x _ => hψ.differentiable one_ne_zero x)
  unfold hermiteCoeff
  have I1 : Integrable (fun x => ψ x * hermiteFunD (mova1_up j α) x) :=
    hψL.integrable_mul (memLp_hermiteFunD _)
  have I2 : Integrable (fun x => ψ x * hermiteFunD (mova1_dn j α) x) :=
    hψL.integrable_mul (memLp_hermiteFunD _)
  have e1 : (fun x => fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) * hermiteFunD α x) =
      fun x => hermiteFunD α x * fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) := by
    funext x; ring
  rw [e1, key]
  simp_rw [hDh']
  have e2 : ∀ x : Euc d, -((Real.sqrt ((α j : ℝ) / 2) * hermiteFunD (mova1_dn j α) x -
      Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteFunD (mova1_up j α) x) * ψ x) =
      Real.sqrt (((α j : ℝ) + 1) / 2) * (ψ x * hermiteFunD (mova1_up j α) x) -
        Real.sqrt ((α j : ℝ) / 2) * (ψ x * hermiteFunD (mova1_dn j α) x) := by
    intro x; ring
  rw [← integral_neg]
  simp_rw [e2]
  rw [integral_sub (I1.const_mul _) (I2.const_mul _), integral_const_mul, integral_const_mul]

theorem s67_xmul_osc (j : Fin d) (r : ℝ) {ψ : Euc d → ℝ} (hψ : MemOsc (r + 1) ψ)
    (hx : MemLp (fun x => x j * ψ x) 2 (volume : Measure (Euc d))) :
    MemOsc r (fun x => x j * ψ x) ∧
      oscNorm r (fun x => x j * ψ x) ≤ Real.sqrt (2 ^ |r + 1|) * oscNorm (r + 1) ψ :=
  s67_ladder_general j r hψ hx 1 (by norm_num) (fun α => by
    rw [s67_coeff_xmul_gen hψ.1 j α]; ring)

theorem s67_partial_osc (j : Fin d) (r : ℝ) {ψ : Euc d → ℝ} (hψ : MemOsc (r + 1) ψ)
    (hψC : ContDiff ℝ 1 ψ)
    (hd : MemLp (fun x => fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))) 2 (volume : Measure (Euc d))) :
    MemOsc r (fun x => fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))) ∧
      oscNorm r (fun x => fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))) ≤
        Real.sqrt (2 ^ |r + 1|) * oscNorm (r + 1) ψ :=
  s67_ladder_general j r hψ hd (-1) (by norm_num) (fun α => by
    rw [s67_coeff_partial_gen hψC hψ.1 j hd α]; ring)

end HRS.MS.MovAdj
