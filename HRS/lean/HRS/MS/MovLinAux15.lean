import HRS.MS.MovLinAux14

/-!
# MOV-LIN, part 6: the bridge between levels of the scale and functions; smoothing for `T` on `L²_0`

Namespace `HRS.MS.MovLin`, helpers `movlin_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.

* `movlin_memOsc_of_lev`: if `j z = ofFun 0 f` with `z ∈ Σ^σ`, `σ ≥ 0`, `f ∈ L²`, then `f ∈ Σ^σ` and `ofFun σ f = z`.
* `movlin_Hs_T`: the short-time smoothing hypothesis `HsOK` for the constructed semigroup `T`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovLin

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

section Bridge

lemma movlin_memOsc_of_lev {σ : ℝ} (hσ : 0 ≤ σ) {f : Euc d → ℝ}
    (hf : MemLp f 2 (volume : Measure (Euc d))) {z : OscSpace d σ}
    (hz : mov2d_j hσ z = OscSpace.ofFun 0 f) : MemOsc σ f ∧ OscSpace.ofFun σ f = z := by
  have hfo : MemOsc 0 f := ⟨hf, by simpa using mov2b_coeff_sq_summable hf⟩
  have hc : ∀ α : MultiIndex d, hermiteCoeff f α =
      oscEigenvalue d α ^ (-(σ / 2)) * OscSpace.coord z α := by
    intro α
    have h1 := congrArg (fun y => OscSpace.coord y α) hz
    simp only [mov2d_j_coord hσ, OscSpace.coord_ofFun_eq hfo] at h1
    have e0 : oscEigenvalue d α ^ ((0 : ℝ) / 2) = 1 := by simp
    rw [e0, one_mul] at h1
    rw [← h1]
    congr 2
    ring
  have hmem : MemOsc σ f := by
    refine ⟨hf, ?_⟩
    have hs := lp_two_summable (show lp (fun _ : MultiIndex d => ℝ) 2 from z)
    refine hs.congr fun α => ?_
    show OscSpace.coord z α ^ 2 = _
    have hL := oscEv_pos (d := d) α
    have hsq : (oscEigenvalue d α ^ (-(σ / 2))) ^ 2 = oscEigenvalue d α ^ (-σ) := by
      rw [show -(σ / 2) = (-σ) / 2 by ring]; exact rpow_half_sq _ _ hL
    rw [hc α, mul_pow, hsq]
    have : oscEigenvalue d α ^ σ * (oscEigenvalue d α ^ (-σ) * OscSpace.coord z α ^ 2) =
        OscSpace.coord z α ^ 2 := by
      rw [← mul_assoc, ← Real.rpow_add hL]; simp
    rw [this]
  refine ⟨hmem, ?_⟩
  apply lp.ext
  funext α
  change OscSpace.coord (OscSpace.ofFun σ f) α = OscSpace.coord z α
  rw [OscSpace.coord_ofFun_eq hmem, hc α, ← mul_assoc, ← Real.rpow_add (oscEv_pos α)]
  have : σ / 2 + -(σ / 2) = 0 := by ring
  rw [this, Real.rpow_zero, one_mul]

variable {s : ℝ} {β q : ℝ} {ρ : Euc d → ℝ}

lemma movlin_T_seq (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R) (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    {t : ℝ} (ht : 0 ≤ t) (v : MovL2Zero ρ) :
    OscSpace.ofFun 0 (movFun (mov2d_T H ψ0 hψ0 t v)) =
      mov2d_G H 0 t (OscSpace.ofFun 0 (movFun v)) := by
  rw [(movlin_L2_osc ((mov2d_T H ψ0 hψ0 t v : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d)))).2.2,
    (movlin_L2_osc (v : Lp ℝ 2 (volume : Measure (Euc d)))).2.2, mov2d_T_coe H ψ0 hψ0 ht, mov2d_Tl_apply]
  exact LinearIsometryEquiv.symm_apply_apply _ _

/-- Short-time smoothing for the constructed semigroup `T`. -/
theorem movlin_Hs_T (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) : HsOK (mov2d_T H ψ0 hψ0) := by
  intro ρ' σ hρ' hρσ
  obtain ⟨C, hC0, hC⟩ := movlin_smooth H hρσ
  refine ⟨C, hC0, fun t ht v hv => ?_⟩
  have hσ : 0 ≤ σ := hρ'.trans hρσ
  obtain ⟨z', hz1, hz2⟩ := hC t ht (OscSpace.ofFun ρ' (movFun v))
  have hseq := movlin_T_seq H ψ0 hψ0 ht.1.le v
  have hj : mov2d_j hρ' (OscSpace.ofFun ρ' (movFun v)) = OscSpace.ofFun 0 (movFun v) :=
    mov2d_j_ofFun hρ' hv
  have hlev : mov2d_j hσ z' = OscSpace.ofFun 0 (movFun (mov2d_T H ψ0 hψ0 t v)) := by
    rw [hseq, ← hj, ← mov2d_G_compat H hρ' ht.1.le, ← hz1, movlin_j_comp hρσ hρ']
  obtain ⟨hm, hzeq⟩ := movlin_memOsc_of_lev hσ
    (Lp.memLp ((mov2d_T H ψ0 hψ0 t v : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d)))) hlev
  refine ⟨hm, ?_⟩
  have e1 : oscNorm σ (movFun (mov2d_T H ψ0 hψ0 t v)) = ‖z'‖ := by
    rw [← OscSpace.norm_ofFun _ hm, hzeq]
  rw [e1]
  have e2 : ‖OscSpace.ofFun ρ' (movFun v)‖ = oscNorm ρ' (movFun v) := OscSpace.norm_ofFun _ hv
  rw [e2] at hz2
  exact hz2

end Bridge

end HRS.MS.MovLin
