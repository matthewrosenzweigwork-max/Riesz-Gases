import HRS.MS.Mov63BAux4

/-!
# S6.3 packet N2a (5): `⟨B_ext(v,w), √ρ_*⟩ = 0`

Namespace `HRS.MS.Mov63`, helper prefix `mnb_`.  Infrastructure for S6.3 (`W:thm:r2mov-nonlinear`); not a manuscript row.

* `mnb_sub_a_nonneg`: `0 ≤ m - movA d s` for `m > d/2 + 3`.
* `mov_B_ext_mass`: for all `v, w ∈ Σ^m`, the `L²` element `Φ(j(B_ext(v,w)))` (`j : Σ^{m-a} → Σ^0`, `Φ : Σ^0 ≃ L²`)
  is orthogonal to `movSqrtLp ρ`, i.e. `B_ext(v,w) ∈ L²_0` (`MovL2Zero ρ`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovForce HRS.MS.MovOsc HRS.MS.MovLin HRS.MS.MovC1

variable {d : ℕ}

section Pair

variable {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

lemma mnb_sub_a_nonneg (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) : 0 ≤ m - movA d s := by
  have h2 := (mov2d_a_bounds d H.hd H.hsd).2
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

lemma mnb_inner_sqrt (H : Mov2dTh d s β q ρ) {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) :
    inner ℝ (movSqrtLp ρ) (hf.toLp f) = ∫ x, Real.sqrt (ρ x) * f x := by
  obtain ⟨ψ0, hψ0⟩ := mov2d_sqrt_schwartz H
  have hm : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by
    rw [← hψ0]; exact ψ0.memLp 2
  unfold movSqrtLp
  rw [dif_pos hm, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hm.coeFn_toLp, hf.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

/-- The pairing functional with `√ρ_*` on `Σ^{m-a}`. -/
def mnb_L (H : Mov2dTh d s β q ρ) {m : ℝ} (h0 : 0 ≤ m - movA d s) : OscSpace d (m - movA d s) →L[ℝ] ℝ :=
  (innerSL ℝ (movSqrtLp ρ)).comp (((mov2d_Phi d).toContinuousLinearEquiv : OscSpace d 0 →L[ℝ]
    Lp ℝ 2 (volume : Measure (Euc d))).comp (mov2d_j h0))

lemma mnb_L_apply (H : Mov2dTh d s β q ρ) {m : ℝ} (h0 : 0 ≤ m - movA d s) (x : OscSpace d (m - movA d s)) :
    mnb_L H h0 x = inner ℝ (movSqrtLp ρ) (mov2d_Phi d (mov2d_j h0 x)) := rfl

lemma mnb_L_hs (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) (h0 : 0 ≤ m - movA d s)
    (c c' : MultiIndex d →₀ ℝ) :
    mnb_L H h0 (OscSpace.ofFun (m - movA d s) (movB d s ρ (mov2d_hs d c) (mov2d_hs d c'))) = 0 := by
  obtain ⟨φ, h1⟩ := mnb_hs_sch (d := d) c
  obtain ⟨ψ, h2⟩ := mnb_hs_sch (d := d) c'
  rw [← h1, ← h2]
  have hmem := (mnb_Kdata H hm).choose_spec.2 φ ψ
  have hmem0 : MemOsc 0 (movB d s ρ (⇑φ) (⇑ψ)) := (mo_mono h0 hmem.1).1
  rw [mnb_L_apply, mov2d_j_ofFun h0 hmem.1, mov2d_Phi_ofFun hmem0.1, mnb_inner_sqrt H hmem0.1]
  exact mnb_mass H φ ψ

/-- **Mass conservation for the extended bilinear term**: `B_ext(v,w) ⟂ √ρ_*` in `L²`
(`⟨B(v,w), √ρ_*⟩ = 0`, i.e. `B_ext(v,w) ∈ L²_0`). -/
theorem mov_B_ext_mass (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) (h0 : 0 ≤ m - movA d s)
    (v w : OscSpace d m) :
    inner ℝ (movSqrtLp ρ) (mov2d_Phi d (mov2d_j h0 (mov_B_ext H hm v w))) = 0 := by
  set L := mnb_L H h0 with hL
  have step2 : ∀ c : MultiIndex d →₀ ℝ, L.comp (mov_B_ext H hm (mov2d_e d m c)) = 0 := fun c =>
    mnb_clm_ext (e := mov2d_e d m) (mov2d_e_dense m) fun c' => by
      rw [ContinuousLinearMap.comp_apply, mov2d_e_apply, mov2d_e_apply, mov_B_ext_hs, hL, mnb_L_hs H hm h0]
      rfl
  have step3 : (ContinuousLinearMap.compL ℝ (OscSpace d m) (OscSpace d (m - movA d s)) ℝ L).comp
      (mov_B_ext H hm) = 0 :=
    mnb_clm_ext (e := mov2d_e d m) (mov2d_e_dense m) fun c => by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply, step2]
      rfl
  have := congrArg (fun Λ => Λ v w) step3
  simpa [hL, mnb_L_apply] using this

/-- `B_ext(v,w)` lies in `L²_0` (`MovL2Zero ρ`). -/
theorem mov_B_ext_mem_L2Zero (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m)
    (h0 : 0 ≤ m - movA d s) (v w : OscSpace d m) :
    mov2d_Phi d (mov2d_j h0 (mov_B_ext H hm v w)) ∈ MovL2Zero ρ :=
  mov2d_mem_zero_iff.2 (mov_B_ext_mass H hm h0 v w)

/-- `B` is linear in the first argument on Schwartz functions (as `mov2d_P_lin` for `P`). -/
theorem mov_B_lin_left (H : Mov2dTh d s β q ρ) (a b : ℝ) (v1 v2 w : 𝓢R) :
    movB d s ρ (fun z => a * v1 z + b * v2 z) (⇑w) =
      fun z => a * movB d s ρ (⇑v1) (⇑w) z + b * movB d s ρ (⇑v2) (⇑w) z :=
  funext fun x => mnb_B_lin_left (by have := H.hd; omega) H.hs0 H.hsd (mnb_rhoData H) v1 v2 w a b x

/-- `B` is linear in the second argument on Schwartz functions. -/
theorem mov_B_lin_right (H : Mov2dTh d s β q ρ) (a b : ℝ) (v w1 w2 : 𝓢R) :
    movB d s ρ (⇑v) (fun z => a * w1 z + b * w2 z) =
      fun z => a * movB d s ρ (⇑v) (⇑w1) z + b * movB d s ρ (⇑v) (⇑w2) z :=
  funext fun x => mnb_B_lin_right (by have := H.hd; omega) H.hs0 H.hsd (mnb_rhoData H) v w1 w2 a b x

/-- `√ρ_*` is a genuine (non-junk, nonzero) element of `L²`. -/
theorem mov_sqrtLp_ne_zero (H : Mov2dTh d s β q ρ) : movSqrtLp ρ ≠ 0 := by
  obtain ⟨ψ0, hψ0⟩ := mov2d_sqrt_schwartz H
  have hm : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by
    rw [← hψ0]; exact ψ0.memLp 2
  have hpos := (mnb_rhoData H).pos
  intro h0
  unfold movSqrtLp at h0
  rw [dif_pos hm] at h0
  have h1 := hm.coeFn_toLp
  rw [h0] at h1
  have h2 : ∀ᵐ x ∂(volume : Measure (Euc d)), Real.sqrt (ρ x) = 0 := by
    filter_upwards [h1, Lp.coeFn_zero ℝ 2 (volume : Measure (Euc d))] with x hx hz
    rw [← hx]; simpa using hz
  have hne : (volume : Measure (Euc d)) ≠ 0 := by
    have : Nonempty (Euc d) := ⟨0⟩
    exact (NeZero.ne _)
  haveI : (ae (volume : Measure (Euc d))).NeBot := ae_neBot.2 hne
  obtain ⟨x, hx⟩ := h2.exists
  have := Real.sqrt_pos.2 (hpos x)
  linarith

end Pair

end HRS.MS.Mov63

end
