import HRS.MS.MovLinAux10
import HRS.MS.MovDecAux3

/-!
# MOV-LIN, part 2: `L²` exponential decay of the constructed semigroup on `L²_0`

Namespace `HRS.MS.MovLin`, helpers `movlin_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.

* `movlin_core_flow`: for a Schwartz core datum `φ` the orbit `T(t) φ` is a family of Schwartz functions satisfying the
  hypotheses of `mov2e_decay` (zero `ψ`-mean, `L²`-continuity, `L²` right derivative `-S u(t)`).
* `movlin_L2_decay`: `‖T(t) v‖ ≤ C e^{-λt} ‖v‖` for all `v ∈ L²_0`, `t ≥ 0` (extension by density of the core).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovLin

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

section Decay

variable {s : ℝ} {β q : ℝ} {ρ : Euc d → ℝ}

/-- Shifting the right derivative at `0` of `τ ↦ T τ (T t v)` to the right derivative at `t` of `τ ↦ T τ v`. -/
lemma movlin_shift_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ → E →L[ℝ] E) (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → T (a + b) = T a * T b) (h0 : T 0 = 1)
    (v w : E) {t : ℝ} (ht : 0 ≤ t)
    (hd : HasDerivWithinAt (fun τ => T τ (T t v)) (-(T 0 w)) (Set.Ici 0) 0) :
    HasDerivWithinAt (fun τ => T τ v) (-w) (Set.Ici t) t := by
  have hs := mov2d_slope_of_hasDerivWithinAt_Ici hd
  rw [h0] at hs
  simp only [ContinuousLinearMap.one_apply] at hs
  apply mov2d_hasDerivWithinAt_Ici
  refine hs.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : (0 : ℝ) ≤ h := le_of_lt hh
  have : T h (T t v) = T (t + h) v := by
    rw [add_comm, hadd h t hh' ht, ContinuousLinearMap.mul_apply]
  simp only [this, zero_add, h0, ContinuousLinearMap.one_apply]


/-- The orbit of a core datum is a classical Schwartz solution. -/
lemma movlin_core_flow (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x))
    (φ : 𝓢R) (v : MovL2Zero ρ) (hv : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v x = φ x) :
    ∃ u : ℝ → 𝓢R, (∀ t : ℝ, 0 ≤ t →
        ((mov2d_T H ψ0 hψ0 t v : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) = (u t).toLp 2 volume) ∧
      (∀ t, 0 ≤ t → ∫ x, Real.sqrt (ρ x) * u t x = 0) ∧
      ContinuousOn (fun τ => (u τ).toLp 2 volume) (Set.Ici 0) ∧
      (∀ t, 0 ≤ t → ∃ w : Lp ℝ 2 (volume : Measure (Euc d)),
        (∀ᵐ x ∂(volume : Measure (Euc d)), w x = movS d s β ρ (u t) x) ∧
          HasDerivWithinAt (fun τ => (u τ).toLp 2 volume) (-w) (Set.Ici t) t) := by
  have hφL : MemLp (fun z => φ z) 2 (volume : Measure (Euc d)) := φ.memLp 2
  have hv' : (⇑(v : Lp ℝ 2 (volume : Measure (Euc d))) : Euc d → ℝ) =ᵐ[volume] fun z => φ z := hv
  have hvφ : (v : Lp ℝ 2 (volume : Measure (Euc d))) = hφL.toLp _ := Lp.ext (hv'.trans hφL.coeFn_toLp.symm)
  have hy : (mov2d_Phi d).symm (v : Lp ℝ 2 (volume : Measure (Euc d))) = OscSpace.ofFun 0 (⇑φ : Euc d → ℝ) := by
    rw [LinearIsometryEquiv.symm_apply_eq, mov2d_Phi_ofFun hφL, hvφ]
  have hex : ∀ τ : ℝ, ∃ ψ : 𝓢R, 0 ≤ τ →
      mov2d_G H 0 τ (OscSpace.ofFun 0 (⇑φ : Euc d → ℝ)) = OscSpace.ofFun 0 (⇑ψ : Euc d → ℝ) := by
    intro τ
    by_cases h : 0 ≤ τ
    · obtain ⟨ψ, hψ⟩ := mov2d_core_inv H φ h
      exact ⟨ψ, fun _ => hψ⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose u hu using hex
  have hTu : ∀ t : ℝ, 0 ≤ t →
      ((mov2d_T H ψ0 hψ0 t v : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) = (u t).toLp 2 volume := by
    intro t ht
    rw [mov2d_T_coe H ψ0 hψ0 ht, mov2d_Tl_apply, hy, hu t ht, mov2d_Phi_ofFun ((u t).memLp 2)]
    rfl
  refine ⟨u, hTu, ?_, ?_, ?_⟩
  · intro t ht
    have h1 : ((mov2d_T H ψ0 hψ0 t v : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) ∈ MovL2Zero ρ :=
      (mov2d_T H ψ0 hψ0 t v).2
    have hψ' : (u t).toLp 2 volume = mov2d_Phi d (OscSpace.ofFun 0 (⇑(u t) : Euc d → ℝ)) :=
      (mov2d_Phi_ofFun ((u t).memLp 2)).symm
    rw [mov2d_mem_zero_iff, hTu t ht, mov2d_sqrtLp H ψ0 hψ0, hψ'] at h1
    rw [LinearIsometryEquiv.inner_map_map,
      mov2d_inner_ofFun (ψ0.memLp 2) ((u t).memLp 2)] at h1
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hψ0]
  · have hc := (continuous_subtype_val.comp_continuousOn (mov2d_T_cont H ψ0 hψ0 v))
    refine hc.congr fun τ hτ => ?_
    exact (hTu τ hτ).symm
  · intro t ht
    obtain ⟨w, hw, hwd⟩ := mov2d_T_gen H ψ0 hψ0 (u t) (mov2d_T H ψ0 hψ0 t v)
      (by
        have h1 := hTu t ht
        have h2 : (⇑((mov2d_T H ψ0 hψ0 t v : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))) : Euc d → ℝ) =ᵐ[volume]
            fun x => u t x := by
          rw [h1]; exact SchwartzMap.coeFn_toLp (u t) 2 volume
        exact h2)
    refine ⟨(w : Lp ℝ 2 (volume : Measure (Euc d))), hw, ?_⟩
    have hTs : MovIsSemigroup d s β ρ (mov2d_T H ψ0 hψ0) := mov2d_isSemigroup H ψ0 hψ0
    have hd1 : HasDerivWithinAt (fun τ => mov2d_T H ψ0 hψ0 τ v) (-w) (Set.Ici t) t :=
      movlin_shift_deriv (mov2d_T H ψ0 hψ0) (fun a b ha hb => hTs.add a b ha hb) (mov2d_T_zero H ψ0 hψ0) v w ht
        (hwd 0 le_rfl)
    have hd2 := (Submodule.subtypeL (MovL2Zero ρ)).hasFDerivAt.comp_hasDerivWithinAt t hd1
    refine (hd2.congr (fun τ hτ => ?_) ?_)
    · exact (hTu τ (le_trans ht hτ)).symm
    · exact (hTu t ht).symm

/-- **`L²` exponential decay on `L²_0`**: `‖T(t) v‖ ≤ C e^{-λ t} ‖v‖`. -/
theorem movlin_L2_decay (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ v : MovL2Zero ρ,
      ‖mov2d_T H ψ0 hψ0 t v‖ ≤ C * Real.exp (-lam * t) * ‖v‖ := by
  obtain ⟨lam, hlam, C, hC, hdec⟩ := HRS.MS.MovDec.mov2e_decay H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ
  refine ⟨lam, hlam, C, hC, fun t ht v => ?_⟩
  have hclosed : IsClosed {v : MovL2Zero ρ | ‖mov2d_T H ψ0 hψ0 t v‖ ≤ C * Real.exp (-lam * t) * ‖v‖} :=
    isClosed_le ((mov2d_T H ψ0 hψ0 t).continuous.norm) (continuous_const.mul continuous_norm)
  have hsub : {v : MovL2Zero ρ | ∃ φ : 𝓢R, ∀ᵐ x ∂(volume : Measure (Euc d)), movFun v x = φ x} ⊆
      {v : MovL2Zero ρ | ‖mov2d_T H ψ0 hψ0 t v‖ ≤ C * Real.exp (-lam * t) * ‖v‖} := by
    rintro v ⟨φ, hφ⟩
    obtain ⟨u, hTu, hmean, hcont, hder⟩ := movlin_core_flow H ψ0 hψ0 φ v hφ
    have h1 := hdec u hmean hcont hder t ht
    have e1 : ‖mov2d_T H ψ0 hψ0 t v‖ = ‖(u t).toLp 2 volume‖ := by
      rw [← hTu t ht]; rfl
    have e0 : ‖v‖ = ‖(u 0).toLp 2 volume‖ := by
      rw [← hTu 0 le_rfl, mov2d_T_zero H ψ0 hψ0]; rfl
    show ‖mov2d_T H ψ0 hψ0 t v‖ ≤ C * Real.exp (-lam * t) * ‖v‖
    rw [e1, e0]
    exact h1
  have := closure_minimal hsub hclosed
  rw [(mov2d_dense_core H ψ0 hψ0).closure_eq] at this
  exact this (Set.mem_univ v)

end Decay

end HRS.MS.MovLin
