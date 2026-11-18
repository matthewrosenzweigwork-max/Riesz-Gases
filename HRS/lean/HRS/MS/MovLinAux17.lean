import HRS.MS.MovLinAux16

/-!
# MOV-LIN, part 8: the `L²_0`-adjoint of `T(t)` at the level of sequences

Namespace `HRS.MS.MovLin`, helpers `movlin_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.

For `w ∈ L²_0` the sequence `Φ⁻¹ (T(t)† w)` is orthogonal to `e₁ = Φ⁻¹ √ρ` and satisfies
`⟨T(t)† w, y⟩ = ⟨w, G_0(t) y⟩` for all `y ⊥ e₁`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovLin

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

section Adj

variable {s : ℝ} {β q : ℝ} {ρ : Euc d → ℝ}

lemma movlin_pr_zero (x y : OscSpace d 0) : movlin_pr x y = inner ℝ x y := rfl

lemma movlin_orth (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    (w : MovL2Zero ρ) :
    movlin_pr (OscSpace.ofFun 0 (⇑ψ0 : Euc d → ℝ)) ((mov2d_Phi d).symm (w : Lp ℝ 2 (volume : Measure (Euc d)))) = 0 := by
  have h1 := (mov2d_mem_zero_iff (ρ := ρ)).1 w.2
  rw [mov2d_sqrtLp H ψ0 hψ0] at h1
  rw [movlin_pr_zero, ← LinearIsometryEquiv.inner_map_map (mov2d_Phi d), LinearIsometryEquiv.apply_symm_apply]
  exact h1

lemma movlin_mem_of_orth (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    (y : OscSpace d 0) (hy : movlin_pr (OscSpace.ofFun 0 (⇑ψ0 : Euc d → ℝ)) y = 0) :
    mov2d_Phi d y ∈ MovL2Zero ρ := by
  rw [mov2d_mem_zero_iff, mov2d_sqrtLp H ψ0 hψ0, LinearIsometryEquiv.inner_map_map]
  exact hy

lemma movlin_inner_symm {X E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (e : X ≃ₗᵢ[ℝ] E) (a : E) (b : X) :
    inner ℝ (e.symm a) b = inner ℝ a (e b) := by
  rw [← e.inner_map_map, e.apply_symm_apply]

lemma movlin_adj_inner (A : MovL2Zero ρ →L[ℝ] MovL2Zero ρ) (w v : MovL2Zero ρ) :
    inner ℝ ((ContinuousLinearMap.adjoint A w : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d)))
        (v : Lp ℝ 2 (volume : Measure (Euc d))) =
      inner ℝ (w : Lp ℝ 2 (volume : Measure (Euc d))) ((A v : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) := by
  have := ContinuousLinearMap.adjoint_inner_left A v w
  exact this

/-- The pairing identity of the `L²_0`-adjoint (for any `W` with the adjoint property). -/
lemma movlin_adj_pair (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {t : ℝ} (ht : 0 ≤ t) (w W : MovL2Zero ρ)
    (hW : ∀ v : MovL2Zero ρ, inner ℝ (W : Lp ℝ 2 (volume : Measure (Euc d))) (v : Lp ℝ 2 (volume : Measure (Euc d))) =
      inner ℝ (w : Lp ℝ 2 (volume : Measure (Euc d))) ((mov2d_T H ψ0 hψ0 t v : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))))
    (y : OscSpace d 0)
    (hy : inner ℝ (OscSpace.ofFun 0 (⇑ψ0 : Euc d → ℝ)) y = 0) :
    inner ℝ ((mov2d_Phi d).symm (W : Lp ℝ 2 (volume : Measure (Euc d)))) y =
      inner ℝ ((mov2d_Phi d).symm (w : Lp ℝ 2 (volume : Measure (Euc d)))) (mov2d_G H 0 t y) := by
  have hv := movlin_mem_of_orth H ψ0 hψ0 y hy
  have h1 := hW ⟨mov2d_Phi d y, hv⟩
  have h2 : ((mov2d_T H ψ0 hψ0 t ⟨mov2d_Phi d y, hv⟩ : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) =
      mov2d_Phi d (mov2d_G H 0 t y) := by
    rw [mov2d_T_coe H ψ0 hψ0 ht, mov2d_Tl_apply]
    show mov2d_Phi d (mov2d_G H 0 t ((mov2d_Phi d).symm (mov2d_Phi d y))) = _
    rw [LinearIsometryEquiv.symm_apply_apply]
  rw [h2] at h1
  rw [Submodule.coe_mk] at h1
  have e1 := movlin_inner_symm (mov2d_Phi d) (W : Lp ℝ 2 (volume : Measure (Euc d))) y
  have e2 := movlin_inner_symm (mov2d_Phi d) (w : Lp ℝ 2 (volume : Measure (Euc d))) (mov2d_G H 0 t y)
  exact e1.trans (h1.trans e2.symm)

end Adj

end HRS.MS.MovLin
